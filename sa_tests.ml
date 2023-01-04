#use "compiler.ml";;
(* expects semantics to complete successfully
 * 'test' - original s-expression
 * 'expected_result' - output of (Semantic_Analysis.semantics (Tag_Parser.tag_parse (Reader.nt_sexpr str 0).found))
 * *)
 type sa_success_test = {test: string; expected_result: expr'};;

 (* expects semantics to raise exception during semantic analysis
  * 'test' - original s-expression
  * *)
 type sa_failure_test = {test: string};;
 

 let sa_success_tests = [
  {test = "x"; expected_result = ScmVarGet' (Var' ("x", Free))};
  {test = "(lambda (x y) (+ x y))"; expected_result = ScmLambda' (["x"; "y"], Simple, ScmApplic' (ScmVarGet' (Var' ("+", Free)), [ScmVarGet' (Var' ("x", Param 0)); ScmVarGet' (Var' ("y", Param 1))], Tail_Call))};
  {test = "(set! x 34)"; expected_result = ScmVarSet' (Var' ("x", Free), ScmConst' (ScmNumber (ScmRational (34, 1))))};
  {test = "(let ((x 45)) (set! x 34))"; expected_result = ScmApplic' (ScmLambda' (["x"], Simple, ScmVarSet' (Var' ("x", Param 0), ScmConst' (ScmNumber (ScmRational (34, 1))))), [ScmConst' (ScmNumber (ScmRational (45, 1)))], Non_Tail_Call)};
  {test = "(let ((x 45)) (let ((y 56)) (let ((z 78) (w 89)) (list x y z w))))"; expected_result = ScmApplic' (ScmLambda' (["x"], Simple, ScmApplic' (ScmLambda' (["y"], Simple, ScmApplic' (ScmLambda' (["z"; "w"], Simple, ScmApplic' (ScmVarGet' (Var' ("list", Free)), [ScmVarGet' (Var' ("x", Bound (1, 0))); ScmVarGet' (Var' ("y", Bound (0, 0))); ScmVarGet' (Var' ("z", Param 0)); ScmVarGet' (Var' ("w", Param 1))], Tail_Call)), [ScmConst' (ScmNumber (ScmRational (78, 1))); ScmConst' (ScmNumber (ScmRational (89, 1)))], Tail_Call)), [ScmConst' (ScmNumber (ScmRational (56, 1)))], Tail_Call)), [ScmConst' (ScmNumber (ScmRational (45, 1)))], Non_Tail_Call)};
  {test = "(if x y)"; expected_result = ScmIf' (ScmVarGet' (Var' ("x", Free)), ScmVarGet' (Var' ("y", Free)), ScmConst' ScmVoid) };
  {test = "(let* ((x #f) (y 'moshe)) (if x y))"; expected_result = ScmApplic' (ScmLambda' (["x"], Simple, ScmApplic' (ScmLambda' (["y"], Simple, ScmIf' (ScmVarGet' (Var' ("x", Bound (0, 0))), ScmVarGet' (Var' ("y", Param 0)), ScmConst' ScmVoid)), [ScmConst' (ScmSymbol "moshe")], Tail_Call)), [ScmConst' (ScmBoolean false)], Non_Tail_Call)};
  {test = "(lambda (x) (list (lambda () x) (lambda (y) (set! x y))))"; expected_result = ScmLambda' (["x"], Simple, ScmSeq' [ScmVarSet' (Var' ("x", Param 0), ScmBox' (Var' ("x", Param 0))); ScmApplic' (ScmVarGet' (Var' ("list", Free)), [ScmLambda' ([], Simple, ScmBoxGet' (Var' ("x", Bound (0, 0)))); ScmLambda' (["y"], Simple, ScmBoxSet' (Var' ("x", Bound (0, 0)), ScmVarGet' (Var' ("y", Param 0))))], Tail_Call)])};
  {test = "(lambda (x) (lambda (u) (u (lambda () x) (lambda (y) (set! x y)))))"; expected_result = ScmLambda' (["x"], Simple, ScmLambda' (["u"], Simple, ScmApplic' (ScmVarGet' (Var' ("u", Param 0)), [ScmLambda' ([], Simple, ScmVarGet' (Var' ("x", Bound (1, 0)))); ScmLambda' (["y"], Simple, ScmVarSet' (Var' ("x", Bound (1, 0)), ScmVarGet' (Var' ("y", Param 0))))], Tail_Call)))};
  {test = "\"the factorial of 5 = ~{ (fact 5) }\\n\""; expected_result = ScmApplic' (ScmVarGet' (Var' ("string-append", Free)), [ScmConst' (ScmString "the factorial of 5 = "); ScmApplic' (ScmVarGet' (Var' ("format", Free)), [ScmConst' (ScmString "~a"); ScmApplic' (ScmVarGet' (Var' ("fact", Free)), [ScmConst' (ScmNumber (ScmRational (5, 1)))], Non_Tail_Call)], Non_Tail_Call); ScmConst' (ScmString "\n")], Non_Tail_Call)};
  {test = "(lambda (a.b) (lambda (c) (a b)))"; expected_result = ScmLambda' (["a"], Opt "b", ScmLambda' (["c"], Simple, ScmApplic' (ScmVarGet' (Var' ("a", Bound (0, 0))),[ScmVarGet' (Var' ("b", Bound (0, 1)))], Tail_Call)))};
  {test = "(lambda (n) (list (lambda () (set! n (+ n 1)) n) (lambda () (set! n 0))))"; expected_result = ScmLambda' (["n"], Simple, ScmSeq' [ScmVarSet' (Var' ("n", Param 0), ScmBox' (Var' ("n", Param 0))); ScmApplic' (ScmVarGet' (Var' ("list", Free)), [ScmLambda' ([], Simple, ScmSeq' [ScmBoxSet' (Var' ("n", Bound (0, 0)), ScmApplic' (ScmVarGet' (Var' ("+", Free)), [ScmBoxGet' (Var' ("n", Bound (0, 0))); ScmConst' (ScmNumber (ScmRational (1, 1)))], Non_Tail_Call)); ScmBoxGet' (Var' ("n", Bound (0, 0)))]); ScmLambda' ([], Simple, ScmBoxSet' (Var' ("n", Bound (0, 0)), ScmConst' (ScmNumber (ScmRational (0, 1)))))], Tail_Call)])};
  {test = "(lambda (n) (lambda () (list (lambda () (set! n (+ n 1)) n) (lambda () (set! n 0)))))"; expected_result = ScmLambda' (["n"], Simple, ScmLambda' ([], Simple, ScmApplic' (ScmVarGet' (Var' ("list", Free)), [ScmLambda' ([], Simple, ScmSeq' [ScmVarSet' (Var' ("n", Bound (1, 0)), ScmApplic' (ScmVarGet' (Var' ("+", Free)), [ScmVarGet' (Var' ("n", Bound (1, 0))); ScmConst' (ScmNumber (ScmRational (1, 1)))], Non_Tail_Call)); ScmVarGet' (Var' ("n", Bound (1, 0)))]); ScmLambda' ([], Simple, ScmVarSet' (Var' ("n", Bound (1, 0)), ScmConst' (ScmNumber (ScmRational (0, 1)))))], Tail_Call)))};
  {test = "(lambda (n) (set! n (+ n 1)) n)"; expected_result = ScmLambda' (["n"], Simple, ScmSeq' [ScmVarSet' (Var' ("n", Param 0), ScmApplic' (ScmVarGet' (Var' ("+", Free)), [ScmVarGet' (Var' ("n", Param 0)); ScmConst' (ScmNumber (ScmRational (1, 1)))], Non_Tail_Call)); ScmVarGet' (Var' ("n", Param 0))])};
  {test = "(lambda (n) (lambda (u) (u (lambda () (set! n (+ n 1)) n) (lambda () (set! n 0)))))"; expected_result = ScmLambda' (["n"], Simple, ScmLambda' (["u"], Simple, ScmApplic' (ScmVarGet' (Var' ("u", Param 0)), [ScmLambda' ([], Simple, ScmSeq' [ScmVarSet' (Var' ("n", Bound (1, 0)), ScmApplic' (ScmVarGet' (Var' ("+", Free)), [ScmVarGet' (Var' ("n", Bound (1, 0))); ScmConst' (ScmNumber (ScmRational (1, 1)))], Non_Tail_Call)); ScmVarGet' (Var' ("n", Bound (1, 0)))]); ScmLambda' ([], Simple, ScmVarSet' (Var' ("n", Bound (1, 0)), ScmConst' (ScmNumber (ScmRational (0, 1)))))], Tail_Call)))};
  {test = "(lambda (n) (list (begin (set! n (* n n)) n) (lambda () n)))"; expected_result = ScmLambda' (["n"], Simple, ScmSeq' [ScmVarSet' (Var' ("n", Param 0), ScmBox' (Var' ("n", Param 0))); ScmApplic' (ScmVarGet' (Var' ("list", Free)), [ScmSeq' [ScmBoxSet' (Var' ("n", Param 0), ScmApplic' (ScmVarGet' (Var' ("*", Free)), [ScmBoxGet' (Var' ("n", Param 0)); ScmBoxGet' (Var' ("n", Param 0))], Non_Tail_Call)); ScmBoxGet' (Var' ("n", Param 0))]; ScmLambda' ([], Simple, ScmBoxGet' (Var' ("n", Bound (0, 0))))], Tail_Call)])};
  {test = "(lambda (n) (list (lambda () (set! n 0)) (lambda () (set! n 1))))"; expected_result = ScmLambda' (["n"], Simple, ScmApplic' (ScmVarGet' (Var' ("list", Free)), [ScmLambda' ([], Simple, ScmVarSet' (Var' ("n", Bound (0, 0)), ScmConst' (ScmNumber (ScmRational (0, 1))))); ScmLambda' ([], Simple, ScmVarSet' (Var' ("n", Bound (0, 0)), ScmConst' (ScmNumber (ScmRational (1, 1)))))], Tail_Call))};
];;

let sa_failure_tests = [
  {test = "(let (and 5) and)"};
  {test = "(define and 5)"}
];;

