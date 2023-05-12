#use "tag-parser.ml";;

type app_kind = Tail_Call | Non_Tail_Call;;

type lexical_address =
  | Free
  | Param of int
  | Bound of int * int;;

type var' = Var' of string * lexical_address;;

type expr' =
  | ScmConst' of sexpr
  | ScmVarGet' of var'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmOr' of expr' list
  | ScmVarSet' of var' * expr'
  | ScmVarDef' of var' * expr'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmLambda' of string list * lambda_kind * expr'
  | ScmApplic' of expr' * expr' list * app_kind;;

module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_address : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val auto_box : expr' -> expr'
  val semantics : expr -> expr'  
end;; (* end of signature SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> Var' (name, Free)
        | Some(major, minor) -> Var' (name, Bound (major, minor)))
    | Some minor -> Var' (name, Param minor);;

  (* run this first *)
  let annotate_lexical_address =
    let rec run expr params env =
      match expr with
      | ScmConst sexpr -> ScmConst' sexpr
      | ScmVarGet (Var str) -> ScmVarGet'(tag_lexical_address_for_var str params env)
      | ScmIf (test, dit, dif) -> ScmIf'((run test params env), (run dit params env), (run dif params env))
      | ScmSeq exprs -> ScmSeq'((List.map (fun expr -> run expr params env) exprs))
      | ScmOr exprs -> ScmOr'(List.map (fun expr -> run expr params env) exprs)
      | ScmVarSet(Var v, expr) -> ScmVarSet'(tag_lexical_address_for_var v params env, run expr params env)
      (* this code does not [yet?] support nested define-expressions *)
      | ScmVarDef(Var v, expr) -> ScmVarDef'(tag_lexical_address_for_var v params env, run expr params env)
      | ScmLambda (params', Simple, expr) -> ScmLambda'(params', Simple, (run expr params' (params::env)))
      | ScmLambda (params', Opt opt, expr) -> ScmLambda'(params', Opt opt, (run expr (params'@[opt]) (params::env)))
      | ScmApplic (proc, args) ->
         ScmApplic' (run proc params env,
                     List.map (fun arg -> run arg params env) args,
                     Non_Tail_Call)
    in
    fun expr ->
    run expr [] [];;

  (* run this second *)
  let annotate_tail_calls = 
    let rec run in_tail = function
      | (ScmConst' _) as orig -> orig
      | (ScmVarGet' _) as orig -> orig
      | ScmIf' (test, dit, dif) ->  ScmIf'(run false test, run in_tail dit, run in_tail dif)
      | ScmSeq' [] -> ScmConst' (ScmVoid)
      | ScmSeq' (expr :: exprs) -> ScmSeq'(runl in_tail expr exprs)
      | ScmOr' [] -> ScmConst'(ScmBoolean(false))
      | ScmOr' (expr :: exprs) -> ScmOr'(runl in_tail expr exprs)
      | ScmVarSet' (var', expr') -> ScmVarSet'(var', run false expr')
      | ScmVarDef' (var', expr') -> ScmVarDef'(var', run false expr')
      | (ScmBox' _) as expr' -> expr'
      | (ScmBoxGet' _) as expr' -> expr'
      | ScmBoxSet' (var', expr') -> ScmBoxSet'(var', run false expr')
      | ScmLambda' (params, Simple, expr) -> ScmLambda'(params, Simple, run true expr)
      | ScmLambda' (params, Opt opt, expr) -> ScmLambda'(params, Opt opt, run true expr)
      | ScmApplic' (proc, args, app_kind) ->
         if in_tail
         then ScmApplic' (run false proc,
                          List.map (fun arg -> run false arg) args,
                          Tail_Call)
         else ScmApplic' (run false proc,
                          List.map (fun arg -> run false arg) args,
                          Non_Tail_Call)
    and runl in_tail expr = function
      | [] -> [run in_tail expr]
      | expr' :: exprs -> (run false expr) :: (runl in_tail expr' exprs)
    in
    fun expr' -> run false expr';;
  (* auto_box *)

  let copy_list = List.map (fun si -> si);;

  let combine_pairs =
    List.fold_left
      (fun (rs1, ws1) (rs2, ws2) -> (rs1 @ rs2, ws1 @ ws2))
      ([], []);;

  let find_reads_and_writes =
    let rec run name expr params env =
      match expr with
      | ScmConst' _ -> ([], [])
      | ScmVarGet' (Var' (_, Free)) -> ([], [])
      | ScmVarGet' (Var' (name', _) as v) ->
         if name = name'
         then ([(v, env)], [])
         else ([], [])
      | ScmBox' _ -> ([], [])
      | ScmBoxGet' _ -> ([], [])
      | ScmBoxSet' (_, expr) -> run name expr params env
      | ScmIf' (test, dit, dif) ->
         let (rs1, ws1) = (run name test params env) in
         let (rs2, ws2) = (run name dit params env) in
         let (rs3, ws3) = (run name dif params env) in
         (rs1 @ rs2 @ rs3, ws1 @ ws2 @ ws3)
      | ScmSeq' exprs ->
         combine_pairs
           (List.map
              (fun expr -> run name expr params env)
              exprs)
      | ScmVarSet' (Var' (_, Free), expr) -> run name expr params env
      | ScmVarSet' ((Var' (name', _) as v), expr) ->
         let (rs1, ws1) =
           if name = name'
           then ([], [(v, env)])
           else ([], []) in
         let (rs2, ws2) = run name expr params env in
         (rs1 @ rs2, ws1 @ ws2)
      | ScmVarDef' (_, expr) -> run name expr params env
      | ScmOr' exprs ->
         combine_pairs
           (List.map
              (fun expr -> run name expr params env)
              exprs)
      | ScmLambda' (params', Simple, expr) ->
         if (List.mem name params')
         then ([], [])
         else run name expr params' ((copy_list params) :: env)
      | ScmLambda' (params', Opt opt, expr) ->
         let params' = params' @ [opt] in
         if (List.mem name params')
         then ([], [])
         else run name expr params' ((copy_list params) :: env)
      | ScmApplic' (proc, args, app_kind) ->
         let (rs1, ws1) = run name proc params env in
         let (rs2, ws2) = 
           combine_pairs
             (List.map
                (fun arg -> run name arg params env)
                args) in
         (rs1 @ rs2, ws1 @ ws2)
    in
    fun name expr params ->
    run name expr params [];;

  let cross_product as' bs' =
    List.concat (List.map (fun ai ->
                     List.map (fun bj -> (ai, bj)) bs')
                   as');;

  let should_box_var name expr params =
    let vars = find_reads_and_writes name expr params in
    let pred = fun (write_list, read_list) ->
                          List.for_all
                            (fun read ->
                              List.for_all
                                (fun (write) -> write == read)
                                write_list)
                              read_list in
    (not (pred vars));;

  let box_sets_and_gets name body =
    let rec run expr =
      match expr with
      | ScmConst' _ -> expr
      | ScmVarGet' (Var' (_, Free)) -> expr
      | ScmVarGet' (Var' (name', _) as v) ->
         if name = name'
         then ScmBoxGet' v
         else expr
      | ScmBox' _ -> expr
      | ScmBoxGet' _ -> expr
      | ScmBoxSet' (v, expr) -> ScmBoxSet' (v, run expr)
      | ScmIf' (test, dit, dif) ->
         ScmIf' (run test, run dit, run dif)
      | ScmSeq' exprs -> ScmSeq' (List.map run exprs)
      | ScmVarSet' (Var' (_, Free) as v, expr') ->
         ScmVarSet'(v, run expr')
      | ScmVarSet' (Var' (name', _) as v, expr') ->
         if name = name'
         then ScmBoxSet' (v, run expr')
         else ScmVarSet' (v, run expr')
      | ScmVarDef' (v, expr) -> ScmVarDef' (v, run expr)
      | ScmOr' exprs -> ScmOr' (List.map run exprs)
      | (ScmLambda' (params, Simple, expr)) as expr' ->
         if List.mem name params
         then expr'
         else ScmLambda' (params, Simple, run expr)
      | (ScmLambda' (params, Opt opt, expr)) as expr' ->
         if List.mem name (params @ [opt])
         then expr'
         else ScmLambda' (params, Opt opt, run expr)
      | ScmApplic' (proc, args, app_kind) ->
         ScmApplic' (run proc, List.map run args, app_kind)
    in
    run body;;

  let make_sets =
    let rec run minor names params =
      match names, params with
      | [], _ -> []
      | name :: names', param :: params' ->
         if name = param
         then let v = Var' (name, Param minor) in
              (ScmVarSet' (v, ScmBox' v)) :: (run (minor + 1) names' params')
         else run (minor + 1) names params'
      | _, _ -> raise (X_this_should_not_happen
                        "no free vars should be found here")
    in
    fun box_these params -> run 0 box_these params;;

  let rec auto_box expr =
    match expr with
    | ScmConst' _ | ScmVarGet' _ | ScmBox' _ | ScmBoxGet' _ -> expr
    | ScmBoxSet' (v, expr) -> ScmBoxSet' (v, auto_box expr)
    | ScmIf' (test, dit, dif) ->
       ScmIf' (auto_box test, auto_box dit, auto_box dif)
    | ScmSeq' exprs -> ScmSeq' (List.map auto_box exprs)
    | ScmVarSet' (v, expr) -> ScmVarSet'(v, auto_box expr)
    | ScmVarDef' (v, expr) -> ScmVarDef'(v, auto_box expr)
    | ScmOr' exprs -> ScmOr'(List.map auto_box exprs)
    | ScmLambda' (params, Simple, expr') ->
       let box_these =
         List.filter
           (fun param -> should_box_var param expr' params)
           params in
       let new_body = 
         List.fold_left
           (fun body name -> box_sets_and_gets name body)
           (auto_box expr')
           box_these in
       let new_sets = make_sets box_these params in
       let new_body = 
         match box_these, new_body with
         | [], _ -> new_body
         | _, ScmSeq' exprs -> ScmSeq' (new_sets @ exprs)
         | _, _ -> ScmSeq'(new_sets @ [new_body]) in
       ScmLambda' (params, Simple, new_body)
    | ScmLambda' (params, Opt opt, expr') ->
      let box_these =
        List.filter
          (fun param -> should_box_var param expr' (params@[opt]))
          params in
      let new_body = 
        List.fold_left
          (fun body name -> box_sets_and_gets name body)
          (auto_box expr')
          box_these in
      let new_sets = make_sets box_these params in
      let new_body = 
        match box_these, new_body with
        | [], _ -> new_body
        | _, ScmSeq' exprs -> ScmSeq' (new_sets @ exprs)
        | _, _ -> ScmSeq'(new_sets @ [new_body]) in
        ScmLambda' (params, Opt opt, new_body)
    | ScmApplic' (proc, args, app_kind) ->
       ScmApplic' (auto_box proc, List.map auto_box args, app_kind);;

  let semantics expr =
    auto_box
      (annotate_tail_calls
         (annotate_lexical_address expr));;

end;; (* end of module Semantic_Analysis *)

let sexpr_of_var' (Var' (name, _)) = ScmSymbol name;;

let rec sexpr_of_expr' = function
  | ScmConst' (ScmVoid) -> ScmVoid
  | ScmConst' ((ScmBoolean _) as sexpr) -> sexpr
  | ScmConst' ((ScmChar _) as sexpr) -> sexpr
  | ScmConst' ((ScmString _) as sexpr) -> sexpr
  | ScmConst' ((ScmNumber _) as sexpr) -> sexpr
  | ScmConst' ((ScmSymbol _) as sexpr) ->
     ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
  | ScmConst'(ScmNil as sexpr) ->
     ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
  | ScmConst' ((ScmVector _) as sexpr) ->
     ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))      
  | ScmVarGet' var -> sexpr_of_var' var
  | ScmIf' (test, dit, ScmConst' ScmVoid) ->
     let test = sexpr_of_expr' test in
     let dit = sexpr_of_expr' dit in
     ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmNil)))
  | ScmIf' (e1, e2, ScmConst' (ScmBoolean false)) ->
     let e1 = sexpr_of_expr' e1 in
     (match (sexpr_of_expr' e2) with
      | ScmPair (ScmSymbol "and", exprs) ->
         ScmPair (ScmSymbol "and", ScmPair(e1, exprs))
      | e2 -> ScmPair (ScmSymbol "and", ScmPair (e1, ScmPair (e2, ScmNil))))
  | ScmIf' (test, dit, dif) ->
     let test = sexpr_of_expr' test in
     let dit = sexpr_of_expr' dit in
     let dif = sexpr_of_expr' dif in
     ScmPair
       (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil))))
  | ScmSeq' ([]) -> ScmVoid
  | ScmSeq' ([expr]) -> sexpr_of_expr' expr
  | ScmSeq' (exprs) ->
     ScmPair (ScmSymbol "begin", 
              scheme_sexpr_list_of_sexpr_list
                (List.map sexpr_of_expr' exprs))
  | ScmOr'([]) -> ScmBoolean false
  | ScmOr'([expr']) -> sexpr_of_expr' expr'
  | ScmOr'(exprs) ->
                   ScmPair (ScmSymbol "or",
                            scheme_sexpr_list_of_sexpr_list
                              (List.map sexpr_of_expr' exprs))
  | ScmVarSet' (var, expr) ->
     let var = sexpr_of_var' var in
     let expr = sexpr_of_expr' expr in
     ScmPair (ScmSymbol "set!", ScmPair (var, ScmPair (expr, ScmNil)))
  | ScmVarDef' (var, expr) ->
     let var = sexpr_of_var' var in
     let expr = sexpr_of_expr' expr in
     ScmPair (ScmSymbol "define", ScmPair (var, ScmPair (expr, ScmNil)))
  | ScmLambda' (params, Simple, expr) ->
     let expr = sexpr_of_expr' expr in
     let params = scheme_sexpr_list_of_sexpr_list
                    (List.map (fun str -> ScmSymbol str) params) in
     ScmPair (ScmSymbol "lambda",
              ScmPair (params,
                       ScmPair (expr, ScmNil)))
  | ScmLambda' ([], Opt opt, expr) ->
     let expr = sexpr_of_expr' expr in
     let opt = ScmSymbol opt in
     ScmPair
       (ScmSymbol "lambda",
        ScmPair (opt, ScmPair (expr, ScmNil)))
  | ScmLambda' (params, Opt opt, expr) ->
     let expr = sexpr_of_expr' expr in
     let opt = ScmSymbol opt in
     let params = List.fold_right
                    (fun param sexpr -> ScmPair(ScmSymbol param, sexpr))
                    params
                    opt in
     ScmPair
       (ScmSymbol "lambda", ScmPair (params, ScmPair (expr, ScmNil)))
  | ScmApplic' (ScmLambda' (params, Simple, expr), args, app_kind) ->
     let ribs =
       scheme_sexpr_list_of_sexpr_list
         (List.map2
            (fun param arg -> ScmPair (ScmSymbol param, ScmPair (arg, ScmNil)))
            params
            (List.map sexpr_of_expr' args)) in
     let expr = sexpr_of_expr' expr in
     ScmPair
       (ScmSymbol "let",
        ScmPair (ribs,
                 ScmPair (expr, ScmNil)))
  | ScmApplic' (proc, args, app_kind) ->
     let proc = sexpr_of_expr' proc in
     let args =
       scheme_sexpr_list_of_sexpr_list
         (List.map sexpr_of_expr' args) in
     ScmPair (proc, args)
  | _ -> raise (X_syntax "Unknown form");;

let string_of_expr' expr =
  Printf.sprintf "%a" sprint_sexpr (sexpr_of_expr' expr);;

let print_expr' chan expr =
  output_string chan
    (string_of_expr' expr);;

let print_exprs' chan exprs =
  output_string chan
    (Printf.sprintf "[%s]"
       (String.concat "; "
          (List.map string_of_expr' exprs)));;

let sprint_expr' _ expr = string_of_expr' expr;;

let sprint_exprs' chan exprs =
  Printf.sprintf "[%s]"
    (String.concat "; "
       (List.map string_of_expr' exprs));;