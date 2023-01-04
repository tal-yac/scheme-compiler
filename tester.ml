#use "compiler.ml";;
#use "tp_tests.ml";;
#use "sa_tests.ml";;
open Tag_Parser;;
open Reader;;
open Semantic_Analysis;;

exception X_test_failed of string;;

let test_tp str expected_success expected_result = 
        try let result =  sprint_expr () (tag_parse (nt_sexpr str 0).found) in
                if expected_success then
                        if result = expected_result then
                                ()
                        else
                                raise (X_test_failed (Printf.sprintf "\nString: %s\nExpected: %s\nActual: %s\n" str expected_result result))
                else
                        raise (X_test_failed (Printf.sprintf "\nString: %s\nExpected: X_syntax\nActual: %s\n" str result))
        with 
        | X_syntax(syntax_err) -> 
                if expected_success then
                        raise (X_test_failed (Printf.sprintf "\nString: %s\nExpected: %s\nResult: X_syntax(%s)\n" str expected_result syntax_err))
                else
                        ()
        | X_not_yet_implemented ->
                if expected_success then 
                        raise (X_test_failed (Printf.sprintf "\nString: %s\nExpected: %s\nResult: X_not_yet_implemented\n" str expected_result))
                else
                        raise (X_test_failed (Printf.sprintf "\nString: %s\nExpected: X_syntax\nResult: X_not_yet_implemented\n" str))
        | X_this_should_not_happen(happened) ->
                raise (X_test_failed (Printf.sprintf "\nString: %s\nResult: X_this_should_not_happen(%s)\n" str happened));;

let run_tp_tests (s_tests : tp_success_test list) (f_tests : tp_failure_test list) =
        try 
                let stub_result  = "" in
                let _ = Printf.printf "Running tests for tag parser\n" in
                let _ = List.fold_left (fun _ (s_test : tp_success_test) -> test_tp s_test.test true s_test.expected_result) () s_tests in
                let _ = List.fold_left (fun _ (f_test : tp_failure_test) -> test_tp f_test.test false stub_result) () f_tests in
                let _ = Printf.printf "Finished successfully\n" in
                ()
        with
        | X_test_failed(e) -> Printf.printf "\nError: Test Failed%s" e;;

run_tp_tests tp_success_tests tp_failure_tests

let test_sa str expected_success expected_result = 
        try let result =  semantics (tag_parse (nt_sexpr str 0).found) in
                if expected_success then
                        if result = expected_result then
                                ()
                        else
                                raise (X_test_failed (Printf.sprintf "\nString: %s\n" str))
                else
                        raise (X_test_failed (Printf.sprintf "\nString: %s\n" str))
        with 
        | X_syntax(syntax_err) -> 
                if expected_success then
                        raise (X_test_failed (Printf.sprintf "\nString: %s\nResult: X_syntax(%s)\n" str syntax_err))
                else
                        ()
        | X_not_yet_implemented ->
                raise (X_test_failed (Printf.sprintf "\nString: %s\nResult: X_not_yet_implemented\n" str))
        | X_this_should_not_happen(happened) ->
                raise (X_test_failed (Printf.sprintf "\nString: %s\nResult: X_this_should_not_happen(%s)\n" str happened));;

let run_sa_tests (s_tests : sa_success_test list) (f_tests : sa_failure_test list) =
        try 
                let stub_result  = ScmConst'(ScmVoid) in (*Can probably put something better here*)
                let _ = Printf.printf "Running tests for semantic analyzer\n" in
                let _ = List.fold_left (fun _ (s_test : sa_success_test) -> test_sa s_test.test true s_test.expected_result) () s_tests in
                let _ = List.fold_left (fun _ (f_test : sa_failure_test) -> test_sa f_test.test false stub_result) () f_tests in
                let _ = Printf.printf "Finished successfully\n" in
                ()
        with
        | X_test_failed(e) -> Printf.printf "\nError: Test Failed%s" e;;

run_sa_tests sa_success_tests sa_failure_tests
