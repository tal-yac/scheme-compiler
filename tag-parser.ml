#use "reader.ml";;

exception X_syntax of string;;

type var = 
  | Var of string;;

type lambda_kind =
  | Simple
  | Opt of string;;

type expr =
  | ScmConst of sexpr
  | ScmVarGet of var
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmOr of expr list
  | ScmVarSet of var * expr
  | ScmVarDef of var * expr
  | ScmLambda of string list * lambda_kind * expr
  | ScmApplic of expr * expr list;;

module type TAG_PARSER = sig
  val tag_parse : sexpr -> expr
end;;

module Tag_Parser : TAG_PARSER = struct
  open Reader;;
  
  let reserved_word_list =
    ["and"; "begin"; "cond"; "do"; "else"; "if"; "lambda";
     "let"; "let*"; "letrec"; "or"; "quasiquote"; "quote";
     "unquote"; "unquote-splicing"];;

  let rec scheme_list_to_ocaml = function
    | ScmNil -> ([], ScmNil)
    | ScmPair(car, cdr) ->
       ((fun (rdc, last) -> (car :: rdc, last))
          (scheme_list_to_ocaml cdr))
    | rac -> ([], rac);;

  let is_reserved_word name = is_member name reserved_word_list;;

  let unsymbolify_var = function
    | ScmSymbol var -> var
    | _ -> raise (X_syntax "not a symbol");;

  let unsymbolify_vars = List.map unsymbolify_var;;

  let list_contains_unquote_splicing =
    ormap (function
        | ScmPair (ScmSymbol "unquote-splicing",
                   ScmPair (_, ScmNil)) -> true
        | _ -> false);;

  let rec macro_expand_qq = function
    | ScmNil -> ScmPair (ScmSymbol "quote", ScmPair (ScmNil, ScmNil))
    | (ScmSymbol _) as sexpr ->
       ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
    | ScmPair (ScmSymbol "unquote", ScmPair (sexpr, ScmNil)) -> sexpr
    | ScmPair (ScmPair (ScmSymbol "unquote",
                        ScmPair (car, ScmNil)),
               cdr) ->
       let cdr = macro_expand_qq cdr in
       ScmPair (ScmSymbol "cons", ScmPair (car, ScmPair (cdr, ScmNil)))
    | ScmPair (ScmPair (ScmSymbol "unquote-splicing",
                        ScmPair (sexpr, ScmNil)),
               ScmNil) ->
       sexpr
    | ScmPair (ScmPair (ScmSymbol "unquote-splicing",
                        ScmPair (car, ScmNil)), cdr) ->
       let cdr = macro_expand_qq cdr in
       ScmPair (ScmSymbol "append",
                ScmPair (car, ScmPair (cdr, ScmNil)))
    | ScmPair (car, cdr) ->
       let car = macro_expand_qq car in
       let cdr = macro_expand_qq cdr in
       ScmPair
         (ScmSymbol "cons",
          ScmPair (car, ScmPair (cdr, ScmNil)))
    | ScmVector sexprs ->
       if (list_contains_unquote_splicing sexprs)
       then let sexpr = macro_expand_qq
                          (scheme_sexpr_list_of_sexpr_list sexprs) in
            ScmPair (ScmSymbol "list->vector",
                     ScmPair (sexpr, ScmNil))
       else let sexprs = 
              (scheme_sexpr_list_of_sexpr_list
                 (List.map macro_expand_qq sexprs)) in
            ScmPair (ScmSymbol "vector", sexprs)
    | sexpr -> sexpr;;

  let rec macro_expand_and_clauses expr = function
    | [] -> expr
    | expr' :: exprs ->
      let remaining = macro_expand_and_clauses expr' exprs in
      ScmPair(ScmSymbol("if") ,ScmPair(expr, ScmPair(
                                                    ScmPair(
                                                      ScmSymbol("and"),
                                                      ScmPair (remaining, ScmNil)                                  ),
                                                    ScmPair(
                                                      ScmBoolean false,
                                                      ScmNil))))

  let rec macro_expand_cond_ribs = function
    | ScmNil -> ScmVoid
    | ScmPair (ScmPair (ScmSymbol "else", exprs), ribs) -> ScmPair(
                                                            ScmSymbol "begin",
                                                              exprs)
    | ScmPair (ScmPair (expr,
                        ScmPair (ScmSymbol "=>",
                                 ScmPair (func, ScmNil))),
               ribs) ->
       let remaining = macro_expand_cond_ribs ribs in
       ScmPair
         (ScmSymbol "let",
          ScmPair
            (ScmPair
               (ScmPair (ScmSymbol "value", ScmPair (expr, ScmNil)),
                ScmPair
                  (ScmPair
                     (ScmSymbol "f",
                      ScmPair
                        (ScmPair
                           (ScmSymbol "lambda",
                            ScmPair (ScmNil, ScmPair (func, ScmNil))),
                         ScmNil)),
                   ScmPair
                     (ScmPair
                        (ScmSymbol "rest",
                         ScmPair
                           (ScmPair
                              (ScmSymbol "lambda",
                               ScmPair (ScmNil, ScmPair (remaining, ScmNil))),
                            ScmNil)),
                      ScmNil))),
             ScmPair
               (ScmPair
                  (ScmSymbol "if",
                   ScmPair
                     (ScmSymbol "value",
                      ScmPair
                        (ScmPair
                           (ScmPair (ScmSymbol "f", ScmNil),
                            ScmPair (ScmSymbol "value", ScmNil)),
                         ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))),
                ScmNil)))
    | ScmPair (ScmPair (pred, exprs), ribs) ->
       let remaining = macro_expand_cond_ribs ribs in
       ScmPair (ScmSymbol "if",
                ScmPair (pred,
                         ScmPair
                           (ScmPair (ScmSymbol "begin", exprs),
                            ScmPair (remaining, ScmNil))))
    | _ -> raise (X_syntax "malformed cond-rib");;

    let rec make_proper_list = function
    | [] -> ScmNil
    | car :: [] -> ScmPair(car, ScmNil)
    | car :: cdr -> ScmPair(car, make_proper_list cdr);;

    let rec macro_expand_let body = function
      | ScmNil -> ScmPair(
                    ScmPair(
                      ScmSymbol("lambda"),
                      ScmPair(ScmNil, body)),
                    ScmNil)
      | ribs -> let params = (match (scheme_list_to_ocaml ribs) with
                                | (params, ScmNil) -> params
                                | _ -> raise (X_syntax "malformed let: params")) in
                let params_names = List.map
                                    (function
                                      | ScmPair(ScmSymbol(var_name), _) -> ScmSymbol var_name
                                      | _ -> raise (X_syntax "malformed let: params names"))
                                    params in
                let params_values = List.map
                                      (function
                                        | ScmPair(_, ScmPair(value, _)) -> value
                                        | _ -> raise (X_syntax "malformed let: params values"))
                                      params in
                ScmPair(
                  ScmPair(
                    ScmSymbol("lambda"),
                    ScmPair(make_proper_list params_names, body)),
                  make_proper_list params_values);;

    let rec macro_expand_letrec body = function
      | ScmNil -> ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, body)), ScmNil)
      | ribs -> let params = (match (scheme_list_to_ocaml ribs) with
                              | (params, ScmNil) -> params
                              | _ -> raise (X_syntax "malformed letrec: params")) in
                let params_names = (List.map (function
                    | ScmPair(ScmSymbol(param_name), _) -> ScmSymbol param_name
                    | _-> raise (X_syntax "malformed letrec: params names"))
                    params) in
                let params_set = (List.map (function
                    | (ScmPair(x, ScmPair(y, ScmNil))) -> (ScmPair(ScmSymbol "set!", ScmPair(x, ScmPair(y, ScmNil)))) 
                    | _ -> raise (X_syntax "malformed letrec: params values"))
                    params) in
                let whatever = List.map (fun x ->
                    ScmPair(x,
                      ScmPair(
                        ScmPair(
                          ScmSymbol "quote",
                          ScmPair(
                            ScmSymbol("whatever"),
                            ScmNil)),
                      ScmNil)))
                    params_names in
                let body = (match body with
                  | ScmPair(expr, ScmNil) -> expr
                  | _ -> body)
                in
                macro_expand_let (make_proper_list (params_set@[body])) (make_proper_list whatever)

  let rec tag_parse sexpr =
    match sexpr with
    | ScmVoid | ScmBoolean _ | ScmChar _ | ScmString _ | ScmNumber _ ->
       ScmConst sexpr
    | ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil)) -> ScmConst sexpr    
| ScmPair (ScmSymbol "quasiquote", ScmPair (sexpr, ScmNil)) ->
       tag_parse (macro_expand_qq sexpr)
    | ScmSymbol var ->
       if (is_reserved_word var)
       then raise (X_syntax "Variable cannot be a reserved word")
       else ScmVarGet(Var var)
    | ScmPair (ScmSymbol "if",
               ScmPair (test, ScmPair (dit, ScmNil))) ->
       ScmIf(tag_parse test,
             tag_parse dit,
             tag_parse ScmVoid)
    | ScmPair (ScmSymbol "if",
               ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil)))) ->
       ScmIf(tag_parse test,
             tag_parse dit,
             tag_parse dif)
    | ScmPair (ScmSymbol "begin", ScmNil) -> ScmConst(ScmVoid)
    | ScmPair (ScmSymbol "begin", ScmPair (sexpr, ScmNil)) ->
       tag_parse sexpr
    | ScmPair (ScmSymbol "begin", sexprs) ->
       (match (scheme_list_to_ocaml sexprs) with
        | (sexprs', ScmNil) -> ScmSeq(List.map tag_parse sexprs')
        | _ -> raise (X_syntax "Improper sequence"))
    | ScmPair (ScmSymbol "set!",
               ScmPair (ScmSymbol var,
                        ScmPair (expr, ScmNil))) ->
       if (is_reserved_word var)
       then raise (X_syntax "cannot assign a reserved word")
       else ScmVarSet(Var var, tag_parse expr)
    | ScmPair (ScmSymbol "define", ScmPair (ScmPair (var, params), exprs)) ->
       tag_parse
         (ScmPair (ScmSymbol "define",
                   ScmPair (var,
                            ScmPair (ScmPair (ScmSymbol "lambda",
                                              ScmPair (params, exprs)),
                                     ScmNil))))
    | ScmPair (ScmSymbol "define",
               ScmPair (ScmSymbol var,
                        ScmPair (expr, ScmNil))) ->
       if (is_reserved_word var)
       then raise (X_syntax "cannot define a reserved word")
       else ScmVarDef(Var var, tag_parse expr)
    | ScmPair (ScmSymbol "lambda", ScmPair (params, exprs)) ->
       let expr = tag_parse (ScmPair(ScmSymbol "begin", exprs)) in
       (match (scheme_list_to_ocaml params) with
        | params, ScmNil -> ScmLambda(unsymbolify_vars params, Simple, expr)
        | params, ScmSymbol opt ->
           ScmLambda(unsymbolify_vars params, Opt opt, expr)
        | _ -> raise (X_syntax "invalid parameter list"))
    | ScmPair (ScmSymbol "let", ScmPair (ribs, exprs)) -> tag_parse(macro_expand_let exprs ribs)
    | ScmPair (ScmSymbol "let*", ScmPair (ScmNil, exprs)) -> tag_parse(macro_expand_let exprs ScmNil)
    | ScmPair (ScmSymbol "let*",
               ScmPair
                 (ScmPair
                    (ScmPair (var, ScmPair (value, ScmNil)), ScmNil),
                  exprs)) -> tag_parse(macro_expand_let 
                                        exprs
                                        (ScmPair(
                                          ScmPair(
                                            var,
                                            ScmPair(value,
                                                    ScmNil)),
                                          ScmNil)))
    | ScmPair (ScmSymbol "let*",
               ScmPair (ScmPair (ScmPair (var,
                                          ScmPair (arg, ScmNil)),
                                 ribs),
                        exprs)) ->
                          let remaining = ScmPair
                                            (ScmPair(
                                              ScmSymbol "let*",
                                              ScmPair(ribs, exprs)),
                                            ScmNil) in
                          tag_parse(macro_expand_let
                                      remaining
                                      (ScmPair(
                                        ScmPair(
                                          var,
                                          ScmPair(arg,
                                                  ScmNil)),
                                        ScmNil)))
    | ScmPair (ScmSymbol "letrec", ScmPair (ribs, exprs)) -> tag_parse(macro_expand_letrec exprs ribs)
    | ScmPair (ScmSymbol "and", ScmNil) -> ScmConst(ScmBoolean true)
    | ScmPair (ScmSymbol "and", exprs) ->
       (match (scheme_list_to_ocaml exprs) with
        | expr :: exprs, ScmNil ->
           tag_parse (macro_expand_and_clauses expr exprs)
        | _ -> raise (X_syntax "malformed and-expression"))
    | ScmPair (ScmSymbol "or", ScmNil) -> ScmConst(ScmBoolean false)
    | ScmPair (ScmSymbol "or", ScmPair (sexpr, ScmNil)) -> tag_parse sexpr
    | ScmPair (ScmSymbol "or", exprs) ->
      (match (scheme_list_to_ocaml exprs) with
       | (exprs', ScmNil) -> ScmOr(List.map tag_parse exprs')
       | _ -> raise (X_syntax "malformed or"))
    | ScmPair (ScmSymbol "cond", ribs) ->
       tag_parse (macro_expand_cond_ribs ribs)
    | ScmPair (proc, args) ->
       let proc =
         (match proc with
          | ScmSymbol var ->
             if (is_reserved_word var)
             then raise (X_syntax "reserved word in proc position")
             else proc
          | proc -> proc) in
       (match (scheme_list_to_ocaml args) with
        | args, ScmNil ->
           ScmApplic (tag_parse proc, List.map tag_parse args)
        | _ -> raise (X_syntax "malformed application"))
    | _ -> let _ = Printf.printf "%s" (Printf.sprintf
    "Unknown form: %a\n"
    sprint_sexpr sexpr) in
      raise (X_syntax "x");;

  end;; (* end of struct Tag_Parser *)

  let rec sexpr_of_expr = function
                                                | ScmConst(ScmVoid) -> ScmVoid
                                                | ScmConst((ScmBoolean _) as sexpr) -> sexpr
                                                | ScmConst((ScmChar _) as sexpr) -> sexpr
                                                | ScmConst((ScmString _) as sexpr) -> sexpr
                                                | ScmConst((ScmNumber _) as sexpr) -> sexpr
                                                | ScmConst((ScmSymbol _) as sexpr)
                                                  | ScmConst(ScmNil as sexpr)
                                                  | ScmConst(ScmPair _ as sexpr)
                                                  | ScmConst((ScmVector _) as sexpr) ->
                                                   ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
                                                | ScmVarGet(Var var) -> ScmSymbol var
                                                | ScmIf(test, dit, ScmConst ScmVoid) ->
                                                   let test = sexpr_of_expr test in
                                                   let dit = sexpr_of_expr dit in
                                                   ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmNil)))
                                                | ScmIf(e1, e2, ScmConst (ScmBoolean false)) ->
                                                   let e1 = sexpr_of_expr e1 in
                                                   (match (sexpr_of_expr e2) with
                                                    | ScmPair (ScmSymbol "and", exprs) ->
                                                       ScmPair (ScmSymbol "and", ScmPair(e1, exprs))
                                                    | e2 -> ScmPair (ScmSymbol "and", ScmPair (e1, ScmPair (e2, ScmNil))))
                                                | ScmIf(test, dit, dif) ->
                                                   let test = sexpr_of_expr test in
                                                   let dit = sexpr_of_expr dit in
                                                   let dif = sexpr_of_expr dif in
                                                   ScmPair
                                                     (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil))))
                                                | ScmSeq([]) -> ScmVoid
                                                | ScmSeq([expr]) -> sexpr_of_expr expr
                                                | ScmSeq(exprs) ->
                                                   ScmPair(ScmSymbol "begin", 
                                                           scheme_sexpr_list_of_sexpr_list
                                                             (List.map sexpr_of_expr exprs))
                                                | ScmOr([]) -> ScmBoolean false
                                                | ScmOr([expr]) -> sexpr_of_expr expr
                                                | ScmOr(exprs) -> ScmPair(ScmSymbol "or", 
                                                                        scheme_sexpr_list_of_sexpr_list
                                                                          (List.map sexpr_of_expr exprs))
                                                | ScmVarSet(Var var, expr) ->
                                                   let var = ScmSymbol var in
                                                   let expr = sexpr_of_expr expr in
                                                   ScmPair (ScmSymbol "set!", ScmPair (var, ScmPair (expr, ScmNil)))
                                                | ScmVarDef(Var var, expr) ->
                                                   let var = ScmSymbol var in
                                                   let expr = sexpr_of_expr expr in
                                                   ScmPair (ScmSymbol "define", ScmPair (var, ScmPair (expr, ScmNil)))
                                                | ScmLambda(params, Simple, expr) ->
                                                   let params = scheme_sexpr_list_of_sexpr_list
                                                                  (List.map (fun str -> ScmSymbol str) params) in
                                                   let expr = sexpr_of_expr expr in
                                                   ScmPair (ScmSymbol "lambda",
                                                            ScmPair (params,
                                                                     ScmPair (expr, ScmNil)))
                                                | ScmLambda([], Opt opt, expr) ->
                                                   let expr = sexpr_of_expr expr in
                                                   let opt = ScmSymbol opt in
                                                   ScmPair
                                                     (ScmSymbol "lambda",
                                                      ScmPair (opt, ScmPair (expr, ScmNil)))
                                                | ScmLambda(params, Opt opt, expr) ->
                                                   let expr = sexpr_of_expr expr in
                                                   let opt = ScmSymbol opt in
                                                   let params = List.fold_right
                                                                  (fun param sexpr -> ScmPair(ScmSymbol param, sexpr))
                                                                  params
                                                                  opt in
                                                   ScmPair
                                                     (ScmSymbol "lambda", ScmPair (params, ScmPair (expr, ScmNil)))
                                                | ScmApplic (ScmLambda (params, Simple, expr), args) ->
                                                   let ribs =
                                                     scheme_sexpr_list_of_sexpr_list
                                                       (List.map2
                                                          (fun param arg -> ScmPair (ScmSymbol param, ScmPair (arg, ScmNil)))
                                                          params
                                                          (List.map sexpr_of_expr args)) in
                                                   let expr = sexpr_of_expr expr in
                                                   ScmPair
                                                     (ScmSymbol "let",
                                                      ScmPair (ribs,
                                                               ScmPair (expr, ScmNil)))
                                                | ScmApplic (proc, args) ->
                                                   let proc = sexpr_of_expr proc in
                                                   let args =
                                                     scheme_sexpr_list_of_sexpr_list
                                                       (List.map sexpr_of_expr args) in
                                                   ScmPair (proc, args)

let string_of_expr expr =
  Printf.sprintf "%a" sprint_sexpr (sexpr_of_expr expr);;

let print_expr chan expr =
  output_string chan
    (string_of_expr expr);;

let print_exprs chan exprs =
  output_string chan
    (Printf.sprintf "[%s]"
       (String.concat "; "
          (List.map string_of_expr exprs)));;

let sprint_expr _ expr = string_of_expr expr;;

let sprint_exprs chan exprs =
  Printf.sprintf "[%s]"
    (String.concat "; "
       (List.map string_of_expr exprs));;