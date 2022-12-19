(* expects tag_parser to complete successfully
 * 'test' - original s-expression
 * 'expected_result' - output of (Tag_Parser.sprint_expr () (Tag_Parser.tag_parser (Reader.nt_sexpr test 0))) if tagged successfully
 * *)
 type tp_success_test = {test: string; expected_result: string};;

 (* expects tag_parser to raise exception during parsing
  * 'test' - original s-expression
  * *)
 type tp_failure_test = {test: string};;
 
 let tp_success_tests = [
   {test = "(letrec () (+ 1 2) (- 2 1))"; expected_result = "(let () (begin (+ 1 2) (- 2 1)))"};
   {test = "(and 1)"; expected_result = "1"};
   {test = "(and)" ; expected_result = "#t"};
   {test = "(define (fact n) (if (zero? n) 1 (* n (fact (- n 1)))))"; expected_result = "(define fact (lambda (n) (if (zero? n) 1 (* n (fact (- n 1))))))"};
   {test = "(let ((a 0) (b 1) (c 2)) (list a b c))"; expected_result = "(let ((a 0) (b 1) (c 2)) (list a b c))"};
   {test = "(cond ((f? x) 'f) ((g? y) 'g) ((h? z) 'h) (else 'unknown))"; expected_result = "(if (f? x) 'f (if (g? y) 'g (if (h? z) 'h 'unknown)))"};
   {test = "(lambda (a b . c) (lambda x (lambda (z w) (list a b c x z w))))"; expected_result = "(lambda (a b . c) (lambda x (lambda (z w) (list a b c x z w))))"};
   {test = "(begin (begin (begin (display \"hello!\") (newline))))"; expected_result = "(begin (display \"hello!\") (newline))"};
   {test = "(let* ((a 1) (b 1) (a (+ a b)) (b (+ a b)) (a (+ a b)) (b (+ a b))) (list a b))"; expected_result = "(let ((a 1)) (let ((b 1)) (let ((a (+ a b))) (let ((b (+ a b))) (let ((a (+ a b))) (let ((b (+ a b))) (list a b)))))))"};
   {test = "(letrec ((fact1 (lambda (n) (if (zero? n) 1 (* n (fact2 (- n 1)))))) (fact2 (lambda (n) (if (zero? n) 1 (* n (fact3 (- n 1)))))) (fact3 (lambda (n) (if (zero? n) 1 (* n (fact1 (- n 1))))))) (fact 100))"; expected_result = "(let ((fact1 'whatever) (fact2 'whatever) (fact3 'whatever)) (begin (set! fact1 (lambda (n) (if (zero? n) 1 (* n (fact2 (- n 1)))))) (set! fact2 (lambda (n) (if (zero? n) 1 (* n (fact3 (- n 1)))))) (set! fact3 (lambda (n) (if (zero? n) 1 (* n (fact1 (- n 1)))))) (fact 100)))"};
   {test = "`(a b c)"; expected_result = "(cons 'a (cons 'b (cons 'c '())))"};
   {test = "`(,a b ,c)"; expected_result = "(cons a (cons 'b (cons c '())))"};
   {test = "`(,@a b ,@c)"; expected_result = "(append a (cons 'b c))"};
   {test = "`((a ,a) (b ,b))"; expected_result = "(cons (cons 'a (cons a '())) (cons (cons 'b (cons b '())) '()))"};
   {test = "\"the value is ~{ (foo x (+ x y)) }\\n\""; expected_result = "(string-append \"the value is \" (format \"~a\" (foo x (+ x y))) \"\\n\")"};
   {test = "((lambda () (or 1 2)))"; expected_result = "(let () (or 1 2))"}
 ];;
 
 let tp_failure_tests = [
   {test = "(let (and 5) and)"};
   {test = "(define and 5)"}
 ];;
 
 
