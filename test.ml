open Compile
open Anf
open Runner
open OUnit2
open Pretty
open Exprs
open Errors
open Allocation
open Graph
open Utils

let t name program input expected allocation =
  name >:: test_run ~args:[] ~std_input:input allocation program name expected
;;


let t_notc name program input expected allocation =
  name >:: test_run ~args:[] ~std_input:input ~no_typechecking:false allocation program name expected
;;

let tgc name heap_size program input expected allocation =
  name >:: test_run ~args:[string_of_int heap_size] ~std_input:input allocation program name expected
;;

let tvg name program input expected allocation =
  name >:: test_run_valgrind ~args:[] ~std_input:input allocation program name expected
;;

let tvgc name heap_size program input expected allocation =
  name >:: test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input allocation program name expected
;;

let terr name program input expected allocation =
  name >:: test_err ~args:[] ~std_input:input allocation program name expected
;;

let tgcerr name heap_size program input expected allocation =
  name >:: test_err ~args:[string_of_int heap_size] ~std_input:input allocation program name expected
;;

let tparse name program expected _ =
  name
  >:: fun _ ->
  assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program
;;


(* let tfvs name program expected =
  name
  >:: fun _ ->
  let ast = parse_string name program in
  let anfed = anf (tag ast) in
  match anfed with
  | AProgram (body, _) ->
      let vars = free_vars body in
      let c = Stdlib.compare in
      let str_list_print strs = "[" ^ ExtString.String.join ", " strs ^ "]" in
      assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print *)
;;

(* other helper testing stuff *)

let tfvs_c name program expected =
  name
  >:: fun _ ->
  let ast = parse_string name program in
  let anfed: 'a aprogram = atag (anf (tag ast)) in
  let vprog: (tag * free_vars) aprogram = (free_vars_cache anfed) in
  let c = Stdlib.compare in 
  let str_list_print strs = "[" ^ ExtString.String.join ", " strs ^ "]" in
  match vprog with 
  | AProgram (_, body, (_, vars)) ->
    assert_equal (List.sort c (StringSet.to_list vars)) (List.sort c expected) ~printer:str_list_print
;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let tprog (filename : string) (expected : string) allocation = filename >:: test_run_input filename allocation expected

(* Runs a program similar to tprog with the provided given input *)
let tprog_input (filename : string) (input: string) (expected : string) allocation = filename >:: test_run_input filename ~std_input:input allocation expected

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let teprog (filename : string) (expected : string) allocation = filename >:: test_err_input filename allocation expected

(* Makes the test run with naive allocation *)
let make_naive tests =
  (List.map (fun test -> test Naive) tests)
;;

let make_register tests =
  (List.map (fun test -> test Register) tests)
;;

(* Pre-function language tests here *)

(* true should be true.. numbers should be numbers ect... *)
let sanity_tests = 
  [
  t "true_is_true" "true" "" "true";
  t "false_is_false" "false" "" "false";
  t "1_is_1" "1" "" "1";
  t "0_is_0" "0" "" "0";
]

(* There are Not Tests ! *)
let not_tests = [
  t "not_true" "!(true)" "" "false";
  t "not_false" "!(false)" "" "true";
  t "double_not" "!(!(true))" "" "true";
  (* t "not_prim_1" "!(isnum(false))" "" "true"; *)
  t "not_on_and_on" "!(!(!(!(!(!(true))))))" "" "true"; (* just for fun ig *)
]

let prim2_tests = [
  (* counter intuitive but we are left associative in evaluation so 
     3 + 5 * 2 = ((3 + 5) * 2) = (8 * 2) = 16 *)
  t "prim2_anf_left_assoc" "3 + 5 * 2" "" "16"; (* looking at this test makes me feel worse *)
  t "prim2_minus_simple1" "3 - 5" "" "-2"; 
  t "prim2_minus_simple2" "-3 - 5" "" "-8";
  t "prim2_minus_simple3" "-3 - -5" "" "2";
  t "prim2_minus_simple4" "3 - -5" "" "8";
  t "prim2_add_simple1" "23 + 32" "" "55";
  t "prim2_add_simple2" "-23 + 2" "" "-21";
  t "prim2_add_simple3" "2 + -23" "" "-21";
] @ [
 (* more complicated tests of prim2 with parens and nests *)
  t "prim2_parens2" "3 + (5 * 2)" "" "13"; (* looking at this test makes me feel better *) 
  t "prim2_nested3" "((3 + 5) * (4 + 7))" "" "88"; (* im ashamed to admit i did the mental math on this one wrong 4 times *)
  t "prim2_let_plus" "let x : int = 3 in 4 + x" "" "7";
  t "prim2_let_mult" "let x : int = 3, y : int = 5 in x * y" "" "15"; (* this gets tested more in let *)
]

(* im currently listening to ed sheeran imaging him as a wheel of cheese *)
(* anyways these are old tests, we're porting them over because it never 
   hurts to know what breaks as we add new stuff *)
let if_tests = [
  t "if_base" "if true: 1 else: 2" "" "1";
  t "if_base_2" "if true: true else: false" "" "true";
  t "and_eq_base_2" "true && true" "" "true";
  t "if_eq_base" "if !(true): false else: true" "" "true";
  t "if_eq_base_2" "if !(true): false else: !(!(true))" "" "true";
]

let comparison_tests = [
  t "simple_ge" "3 > 5" "" "false";
  t "simple_ge2" "5 > 3" "" "true";
  t "simple_ge3" "5 > 5" "" "false";
  t "simple_ge_eq" "3 >= 5" "" "false";
  t "simple_ge_eq2" "5 >= 3" "" "true";
  t "simple_ge_eq3" "5 >= 5" "" "true";
  t "simple_le" "-3 < 5" "" "true";
  t "simple_le2" "3 < 5" "" "true";
  t "simple_le3" "5 < 5" "" "false";
  t "simple_le4" "5 < 3" "" "false";
  t "simple_le_eq" "3 <= 5" "" "true";
  t "simple_le_eq2" "3 <= 5" "" "true";
  t "simple_eq" "3 == 5" "" "false";
  t "simple_eq2" "5 == 5" "" "true";
  t "simple_eq3" "-5 == 5" "" "false";
  t "simple_eq4" "-5 == -5" "" "true";
  t "simple_eq_total_1" "-5 == true" "" "false";
  (* fun fact: false == false should be true ! and now it is :D *)
  t "simple_eq_total_2" "(false == false)" "" "true"; 
  t "simple_eq_total_3" "(true == 1)" "" "false";
  t "simple_eq_total_4" "(true == 0)" "" "false";
  t "simple_eq_total_5" "(true == true)" "" "true";
  t "simple_eq_total_6" "(true == false)" "" "false"; 
]


(* Verify some more basic functionality of our 1 argument primatives *)
let prim1_test = [
  t "prim1_add1_basic" "add1(4)" "" "5";
  t "prim1_add1_negative" "add1(-2)" "" "-1";
  t "prim1_sub1_negative" "sub1(-2)" "" "-3";
  t "prim1_sub1_positive" "sub1(4)" "" "3";
  t "prim1_nested_prim1" "sub1(add1(3))" "" "3";
  t "prim1_nested_prim1_2" "add1(sub1(3))" "" "3";
  t "prim1_nested_prim1_zero" "sub1(add1(0))" "" "0";
  t "prim1_nested_prim1_negative" "sub1(add1(-1))" "" "-1";
  t "prim1_nested_add1" "add1(add1(3))" "" "5";
  t "prim1_nested_nested" "sub1(sub1(sub1(sub1(5))))" "" "1";
]

let ifexp_test = [
  t "if_true" "if true: 4 else: 2" "" "4";
  t "if_false" "if false: 4 else: 2" "" "2";
  t "if_false_prim1" "if !(true): 4 else: 2" "" "2";
  t "if_false_prim2" "if 4 <= 2: 4 else: 2" "" "2";
  t "if_false_prim2_assoc_left" "if 0 >= 1 && false: 4 else: 2" "" "2";
  t "if_true_let_in_pred" "if (let x : bool = true in let y : bool = x in y): 3 + 1 - 1 else: 2" "" "3";
  terr "if_branches_don't_bleed_bindings" "if false: (let x : int = 1 in 3 + x) else: x" "" "not in scope";
  terr "if_left_assoc_err" "if (3 * 2 == 2 * 3): print(true) else: print(1231231)" "" "Arithmatic expected a number, but got false";
  t "if_branches_dont_evaluate_both_1" "if true: print(true) else: print(false)" "" "true\ntrue";
  t "if_branches_dont_evaluate_both_2" "if false: print(true) else: print(false)" "" "false\nfalse";
]

(* The working basic and tricky lets *)
let let_tests = [
  t "let_base" "let x : int = 10 in x" "" "10";
  t "let_binded_to_add1" "let x : int = add1(10) in x" "" "11";
  t "let_multiple_base" "let x : int = 10, y : int = -1 in y" "" "-1";
  t "let_bind_has_bind_reference" "let x : int = 10, y : int = x in y" "" "10"; 
  t "let_bind_has_bind_reference2" "let x : int = 10, y : int = x in add1(x)" "" "11";
  t "let_scoping" "let x : int = 5 in let x : int = 6 in x" "" "6"; (* tricky one.. highlights shadowing *)
  t "let_scoping_nested" "let x : int = -1, y : int = 2 in let y : int = x, x : int = y in sub1(x)" "" "-2";
  t "let_in_add1" "add1(let aaaaaa : int = 12, b : int = 0 in add1(aaaaaa))" "" "14";
  t "let_in_sub1" "sub1(let x : int = 4 in x)" "" "3";
  t "let_nested1" "let x : int = 5 in let x : int = 6, y : int = add1(x) in y" "" "7"; 
  t "let_nested2" "let x : int = 5, y : int = 3 in let x : int = 6, y : int = add1(x) in y" "" "7";
  t "let_nested3" "let x : int = 5, y : int = 3 in let z : int = 3 in let y : int = 5 in y" "" "5";
  t "let_nested4" "let x : int = 5, y : int = 3 in let z : int = 3 in let y : int = 5 in z" "" "3";
  t "let_nested5" "let x : int = 5, y : int = 3 in let z : int = 3 in let y : int = 5 in x" "" "5";
  t "let_nested_prim2s" "let x : int = 5, y : int = 3 in let z : int = 3 in let y : int = 5 in x + y * z * (x + 23)" "" "840";
]

(* Verify some basic functionality (for sanity) *)
let basic_numbers_tests = [
  t "basic_num1" "41" "" "41";
  t "basic_num2" "0" "" "0";
  t "basic_num3" "-1" "" "-1";
  t "basic_num4" "((((-1))))" "" "-1"
]

(* Woah ^.^ 🤯 *)
let big_number = [
  t "big_add" "add1(1000)" "" "1001";
  t "big_sub" "sub1(9999999)" "" "9999998"; (* :3 *)
  t "big_prim2" "99999999 - 134095" "" "99865904";
]

let and_or_op_tests = [
  (* verify and truth table *)
  t "simple_and1" "true && true" "" "true";
  t "simple_and2" "false && true" "" "false";
  t "simple_and3" "true && false" "" "false"; 
  t "simple_and4" "false && false" "" "false";
  (* verify or truth table *)
  t "simple_or1" "true || true" "" "true";
  t "simple_or2" "true || false" "" "true";
  t "simple_or3" "false || true" "" "true";
  t "simple_or4" "false || false" "" "false"; 
  (* some edge cases *)
  t "edge_or1" "true || 123" "" "true"; (* short circuit allows for non-logic on second term *)
  terr "edge_or2" "123 || true" "" "Logic expected a bool"; (* type 123 does not resolve to bool so we cannot return true *)
  terr "edge_and" "true && 123" "" "Logic expected a bool";
  (* we can short circuit the and in this case since false && anything else is just false *)
  t "edge_and2" "false && 123" "" "false";
]


let is_type_tests = [
  (* isbool? *)
  t "true_is_bool" "isbool(true)" "" "true";
  t "false_is_bool" "isbool(false)" "" "true";
  t "num_is_not_bool" "isbool(123)" "" "false";
  (* isnum? *)
  t "true_is_not_num" "isnum(true)" "" "false";
  t "false_is_not_num" "isnum(false)" "" "false";
  t "num_is_num" "isnum(231)" "" "true";
]

let prim1_type_checking = [
  terr "add_check" "add1(true)" "" "Arithmatic expected a number, but got true";
  terr "sub_check" "sub1(false)" "" "Arithmatic expected a number, but got false";
  terr "not_check" "!(0)" "" "Logic expected a bool, but got 0";
  terr "not_check_neg_number" "!(-100)" "" "Logic expected a bool, but got -100";
]

let prim2_type_checking = [
  terr "plus_check" "false + 1" "" "Arithmatic expected a number, but got false";
  terr "plus_check2" "1 + false" "" "Arithmatic expected a number, but got false";
  terr "minus_check" "-100 - true" "" "Arithmatic expected a number, but got true";
  terr "minus_check2" "true - -100" "" "Arithmatic expected a number, but got true";
  terr "times_check" "true * false" "" "Arithmatic expected a number, but got false";
  terr "times_check2" "false * true" "" "Arithmatic expected a number, but got true";
  (* And & Or are tested below... *)
  terr "greater_check" "10 > true" "" "Comparison expected a number, but got true";
  terr "greater_check2" "true > 10" "" "Comparison expected a number, but got true";
  terr "greater_eq_check" "-13 >= true" "" "Comparison expected a number, but got true";
  terr "greater_eq_check2" "true >= -13" "" "Comparison expected a number, but got true";
  terr "less_check" "10 < true" "" "Comparison expected a number, but got true";
  terr "less_check2" "true < 10" "" "Comparison expected a number, but got true";
  terr "less_eq_check" "-13 <= true" "" "Comparison expected a number, but got true";
  terr "less_eq_check2" "true <= -13" "" "Comparison expected a number, but got true";
]

let print_tests = [
  t "simple_print" "print(5)" "" "5\n5";
  t "more_complex_print" "add1(print(5))" "" "5\n6";
  t "more_complex_print_with_bools" "!(print(false))" "" "false\ntrue";
]

let short_circuits_tests = [
  t "simple_or_short_circuit" "if true || print(false): 1 else: 0" "" "1"; 
  t "simple_and_short_circuit" "if false && print(true): 1 else: 0" "" "0"; 
]

(* Tests for 2 types of overflow. 1 -> compiler overflow (int > intmax). 2 -> runtime overflow (operation overflowed) *)
let max_sv_int: int64 = 4611686018427387903L
let min_sv_int: int64 = -4611686018427387904L

let overflow_tests = [
  terr "simle_add_overflow" (Int64.to_string(max_sv_int) ^ " + 1") "" "Arithmatic operation overflowed";
  terr "simple_mul_overflow" "99999999999999 * 999999999999999" "" "Arithmatic operation overflowed";
  terr "compiler_mul_overflow" "4611686018427387903 * 2" "" "Arithmatic operation overflowed";
  terr "compiler_add1_overflow" "add1(4611686018427387903)" "" "Arithmatic operation overflowed";
  terr "compiler_sub1_underflowflow1" "sub1(-4611686018427387904)" "" "Arithmatic operation overflowed";
  terr "compiler_sub1_underflowflow2" ("sub1(" ^ (Int64.to_string min_sv_int) ^ ")") "" "Arithmatic operation overflowed";
  terr "compiler_mul_underflow" "-4611686018427387903 * 20" "" "Arithmatic operation overflowed";
  t "big_comparison_ops1" ((Int64.to_string max_sv_int) ^ ">" ^ (Int64.to_string min_sv_int)) "" "true";
  t "big_comparison_ops2" ((Int64.to_string max_sv_int) ^ ">=" ^ (Int64.to_string min_sv_int)) "" "true";
  t "big_comparison_ops3" ((Int64.to_string min_sv_int) ^ " < " ^ (Int64.to_string max_sv_int)) "" "true";
  t "big_comparison_ops4" ((Int64.to_string min_sv_int) ^ "<=" ^ (Int64.to_string max_sv_int)) "" "true";
]

let basic_tuple_tests = [
  t "basic_tup_printing_1" "(1, 2)" "" "(1, 2)";
  t "basic_tup_printing_2" "(3,)" "" "(3,)";
  t "basic_tup_printing_3" "()" "" "()";
  t "basic_tup_printing_4" "(1, (3, 5))" "" "(1, (3, 5))";
  t "basic_tup_printing_5" "((),)" "" "((),)";
  t "basic_tup_printing_6" "(())" "" "()"; (* this is a tuple in parenthesis *)
  t "basic_tup_printing_7" "(1, true)" "" "(1, true)";
  t "basic_tup_printing_8" "((true,),)" "" "((true,),)";
  t "basic_tup_printing_9" "((1),)" "" "(1,)";
  (* A whole bunch of cases of what a tuple is and isn't *)
  (* t "tuple_is_not_1" "isbool(())" "" "false";
  t "tuple_is_not_2" "isbool((3,))" "" "false";
  t "tuple_is_not_3" "isbool((true, false))" "" "false";
  t "tuple_is_not_4" "isnum(())" "" "false";
  t "tuple_is_not_5" "isnum((false,))" "" "false";
  t "tuple_is_not_6" "isnum((false, true, 3, 100))" "" "false";
  t "tuple_is_1" "istuple(())" "" "true";
  t "tuple_is_2" "istuple((12,))" "" "true";
  t "tuple_is_3" "istuple((3, (false, (), (1,)), false))" "" "true";
  t "tuple_is_4" "istuple((1, 4, 5, 5, 5, (), ()))" "" "true";
  t "tuple_is_5" "istuple((((((((((((((()))))))))))))))" "" "true";
  t "is_not_a_tup_1" "istuple(1)" "" "false";
  t "is_not_a_tup_2" "istuple(0)" "" "false";
  t "is_not_a_tup_3" "istuple(false)" "" "false";
  t "is_not_a_tup_4" "istuple(true)" "" "false";
  t "is_not_a_tup_5" "istuple((1, 2, 3)[1])" "" "false"; *)
  (* more complicated functions and tuples *)
  (* will fail *)
  (* t "make_list"
  "def make_list(x): if x == 0: nil 
                      else: link(x, make_list(x - 1)) \n
    and def link(first, rest): (first, rest) \n
    make_list(4)"
  "" "(4, (3, (2, (1, nil))))"; *)
  t "tuple_eval_order" "(print(1), print(2))" "" "1\n2\n(1, 2)";
]

let tuple_get_tests = [
  t "basic_tuple_get_1" "(1, 2)[0]" "" "1";
  t "basic_tuple_get_2" "(1, 2)[1]" "" "2";
  t "get_with_a_let" "let a : int * int = (1, 2) in a[1]" "" "2";
  (* t "get_gets_a_tup" "let a : (int * ) * int = ((2, nil, true), 0) in a[a[1]]" "" "(2, nil, true)"; *)
  terr "too_low_tup_get" "(1, 2, 3, 4, 5)[-1]" "" "negative"; (* TODO these are bad error messages *)
  terr "too_high_tup_get" "(1, 2, 3, 4, 5)[100]" "" "out of bounds";
  t "self_ref_tuple_get" "let a : int * int = (1, 2) in a[a[0]]" "" "2";
  (* t "do_some_weird_shit" "let a = (1, 2), b = (3, 4) in a[0] := b; b[0] := a; b" ""; *) (* This just. doesn't need to work rly but also c shouldnt segfault *)
  t "tuple_checking" "(3,)[0]" "" "3";
  t "tuple_sanity" "(3, 4)[0]" "" "3";
]

let tuple_set_tests = [
  t "basic_tuple_set_1" "let a : int * int = (1, 2), _ = a[1] := 30 in a" "" "(1, 30)";
  t "basic_tuple_set_2" "let a : int * int = (1, 2) in a[0] := 12; a" "" "(12, 2)";
  (* t "single_elem_tuple_set" "let a : int = (2,) in a[0] := 3; a" "" "(3,)"; *)
  terr "too_low_tup_set" "let a : int * int * int = (1, 2, 3), _ = a[-1] := 30 in a" "" "negative";
  terr "too_high_tup_set" "let a : int * int * int = (1, 2, 3), _ = a[10] := 30 in a" "" "out of bounds";
  (* terr "empty_tuple_set" "let a = () in a[0] := 1; a" "" "out of bounds"; *)
  t "tuple_set_with_complex_idx" "let a : int * int * int = (1,2,3) in a[sub1(2 + 10 - 9)] := 4; a" "" "(1, 2, 4)";
  t "tuple_set_with_tuple_value" "let a : int * int * int = (1, 2) in a[0] := (0, 1); a" "" "((0, 1), 2)";
  t "tuple_set_with_bool_value" "let a : bool * int * int = (true, 4, 3) in a[1] := false; a" "" "(true, false, 3)";
  (* t "tuple_set_to_let_bound_value" "let a : int = add1(4), b : int * int? = (a, (4,)) in b[1] := a; b" "" "(5, 5)"; *)
  t "tuple_set_with_expr_idx" "let a : int * int * int * int = (1, 2, 3, 4) in a[add1(1)] := 9; a" "" "(1, 2, 9, 4)";
  (* t "tuple_nested_index_computation" "let a : (int * int) * (int * int) = ((1,2), (3,4)) in a[sub1(add1(1))][sub1(sub1(3))] := -2; a" "" "((1, 2), (3, -2))"; *)
  (* t "tuple_set_with_deeply_nested"
    "let a = ((1, (2, 3, 5, 7)), 4) in a[0][1][0] := 10; a"
    "" "((1, (10, 3, 5, 7)), 4)"; *)
  t "self_ref_tuple_set" "let a : int * int * int * int * int * int * int = (0, 1, 2, 3, 4, 5, 6) in a[a[3]] := 1000; a" "" "(0, 1, 2, 1000, 4, 5, 6)";
  (* t "setting_nested_twice"
    "let tup = ((1, 2, 3), 4) in \n
      tup[1] := tup[0]; \n
      tup[0] := (5, 3, 2); \n
      tup[0][1] := 0; \n
      tup"
      "" "((5, 0, 2), (1, 2, 3))"; *)
  (* because pointers we modify both a and b here*)
  (* t "indirect_tuple_set"
    "let a = (1, 2, 3), b = a in b[1] := 42; (a, b)"
    "" "((1, 42, 3), (1, 42, 3))";
    t "indirect_tuple_set_v2"
    "let a = (1, 2, 3), b = (4, 5, 6), c = (a, b) in a[1] := 42; b[2] := 23; c"
    "" "((1, 42, 3), (4, 5, 23))";
  (* assignment given tests *)
  t "assignment_given_spec"
    "let three  = (0, 0, 0) in \n
      let three1 = three[0] := 1 in \n
      let three2 = three[1] := 2 in \n
      three[2] := 3; three" "" "(1, 2, 3)";
  (* the assignment actually has an error and says tup[1][2] *)
  t "nested_operations_in_set"
    "let tup = ((1, 2, 3), 4) in \n
      tup[0][2] := 5; \n
      let x = (1, 2, 3, 4) in 
      x[0 + 1] := isbool(5);
      (x, tup)"
    "" "((1, false, 3, 4), ((1, 2, 5), 4))";
  t "destructure_example"
    "let t = (3, ((4, true), 5)) in
      let (x, (y, z)) = t in
      x + y[0] + z"
      "" "12";
  (* TODO more complex error messages cases *)
  terr "basic_non_tuple" 
      "let a = 10 in a[0] := 23132; a" 
      "" "expected a tuple, but got 10";
  terr "error_was_tuple_now_is_not"
      "let tup = ((1, 2, 3), 4) in \n
      tup[0] := 5; \n
      tup[0][1] := 3; \n
      tup"
      "" "expected a tuple, but got 5";
  (* and he shadowed away, shadow shadow, and he shadowed away, shadow shadow, 
      .. till the very next day bum bum bum bam bum bum *)
  terr "error_tuple_shadowed_away"  
      "let a = (1, 2, 3) in let a = 5 in a[0]" "" "expected a tuple, but got 5";
  terr "error_was_correct_length_now_is_not"
    "let tup = ((1, 2, 3), 4) in \n
      tup[0] := (1, 2); \n
      tup[0][2] := 3; \n
      tup"
      "" "out of bounds";
  terr "tuple_dynamic_out_of_bounds" 
      "let a = (1, 2, 3), idx = add1(2) in a[idx] := 5; a" 
      "" "out of bounds";
  (* TODO more complex cases with getting nested in things *)
  (* TODO the things in the functions *)
  (* will fail rn *)
  t "fun_set_tup"
  "def set(tup, idx, value): tup[idx] := value \n
    let a = (1, 2, 3) in set(a, 2, 5); a"
    "" "(1, 2, 5)"; (* mutation 😨😨 *)
   terr "fun_set_tup_err_too_small"
    "def set(tup, idx, value): tup[idx] := value \n
    let a = (1, 2, 3) in set(a, -2, 5); a"
    "" "negative"; (* error case too small of idx *)
    *)
] 

(* These are extra things added retroactively *)
let extra_tuple_tests = [
  terr "tuple_add" "(1, 3) + 4" "" "Arithmatic expected a number, but got (1, 3)"; (* Error *)
  terr "tuple_compare" "(1, 3) <= (2, 4)" "" "Comparison expected a number, but got (2, 4)";
  terr "tuple_function_call" "(1, 2)(1)" "" "Call wasn't closure";
  terr "tuple_prim" "sub1((2,))" "" "Arithmatic expected a number, but got (2,)";
  terr "tuple_in_get" "(1, 2)[(3,)]" "" "Tried to access out of bounds index for tuple, index too large";
  terr "tuple_in_set" "(3, 4)[(1, 2)] := 2" "" "Tuple get recieved an out of bounds index, index to high";

  (* Weird shit in gets and sets *)
  terr "int_in_set" "100[1] := 3" "" "Set expected a tuple, but got 100";
  terr "bool_in_set" "false[0] := true" "" "Set expected a tuple, but got false";
  terr "int_in_get" "1001[3]" "" "Get expected a tuple, but got 1001";
  terr "bool_in_get" "true[-2]" "" "Get expected a tuple, but got true";

  (* Tuple equality *)
  t "tuple_eq_1" "(1,) == (1,)" "" "false";
  t "tuple_eq_2" "(2, 1, 4) == (2, 1)" "" "false";
  t "tuple_eq_3" "let a : int * int * int = (1, 3, 4) in a == a" "" "true";
  (* t "tuple_eq_4" "let a = (1,) in a == (1,)" "" "false"; *)
  t "tuple_eq_5" "let a : int * int = (1, 2), b : int * int = (1, 2) in a == b" "" "false";
  t "tuple_eq_6" "let a : int * int = (1, 2), b : int * int = a in a[1] := 2;b == a" "" "true";

  (* 
  (* nil tests *)
  t "nil_get" "(1, nil, 2)[1]" "" "nil";
  t "nil_id" "nil == nil" "" "true";
  t "nil_set" "let a = (1, 2) in a[0] := nil;a" "" "(nil, 2)";
  (* t "nil_is_tup" "istuple(nil)" "" "true"; *)
  t "nil_unpack_fr" "let (a, b) = (1, nil) in b" "" "nil";

  (* Pretty nested binding *)
  t "very_nested_let_desugar" "let (a, (b, (c, (d, e)))) = (1, (2, (3, (4, (5, (6, (7, nil))))))) in d" "" "4";
  t "pretty_nested_function_arg" "def f(a, ((b, (c, d)), e)): e * b + d\nf(0, ((3, (1, 7)), 2))" "" "13";

  (* Nested _ *)
  (* me when i'm (Arms, Body, Legs, Flesh, Skin, Bone, Sinew, *Good*Luck*, _)*)
  (* Henry you are an underscores fan right? RIGHT?? *)
  t "nested_underscores" "let (x, (y, _), _) = (1, (2, 3), (4, (5, nil))) in x * y" "" "2";
  (* ok holy shit this spoiled little brat remix goes so hard *)
  (* (By complete coencidence (i cant spell) an underscores remix came on just as i was writing this) *)
  terr "what_if_the___wasnt_anything" "let (x, y, _) = (1, 2) in x + y" "" "index too large";

  vibing to internet girl rn julia
  *)

  (* Seq tests *)
  t "basic_seq" "1;2" "" "2";
  t "seq_eval_order" "print(1);print(2);print(3);4" "" "1\n2\n3\n4";
  t "seq_doesnt_bleed_binds" "let x : int = 2 in (let x : int = 3 in print(x));x" "" "3\n2";
  t "seq_with_different_types" "(1, 2);false" "" "false";
  t "nested_seq" "((let x: int = 1 in x * 4); 4 > 10) || print(false)" "" "false\nfalse"; 

]

let equals_test = [
  t "num_equal" "equal(1, 1)" "" "true";
  t "num_neq" "equal(2, 3)" "" "false";
  t "num_neq2" "equal(3, 2)" "" "false";
  t "bool_equal" "equal(true, true)" "" "true";
  t "num_bool_neq" "equal(1, true)" "" "false";
  t "bool_num_neq" "equal(true, 1)" "" "false";
  t "tuple_bool_neq" "equal((1, 2), true)" "" "false";
  t "tuple_num_neq" "equal((1, 2), 1)" "" "false";
  t "num_tuple_neq" "equal(1, (1, 2))" "" "false";
  t "tuple_tuple_eq" "equal((1, 2), (1, 2))" "" "true";
  t "tuple_tuple_eq1" "equal((1, (3, 4)), (1, (3, 4)))" "" "true";
  t "tuple_tuple_eq2" "equal(((1, 2), (3, 4)), ((1, 2), (3, 4)))" "" "true";
  t "tuple_tuple_eq3" "equal(((1, 2), (), (), (3, 4)), ((1, 2), (), (), (3, 4)))" "" "true";
  (* i consider these different, thus they are different ! *)
  t "tuple_tuple_eq4" "equal(((1, 2), (), (3, 4)), ((1, 2), (), (), (3, 4)))" "" "false";
  t "input_eq_num" "equal(input(), 2)" "2" "true";
  t "input_eq_bool" "equal(input(), true)" "true" "true";
  t "input_eq_tuple" "equal((input(), 2), (true, 2))" "true" "true";
  t "input_neq_tuple" "equal((true, (false, input())), (true, (false, false)))" "true" "false";
]

let let_egg_tests = [
  (* tuple basics *)
  t "let_tuple_err1" "let (x, y) = (3, 2) in x" "" "3";
  t "let_tuple_err2" "let (x, y) = (3, 2) in y" "" "2";
  t "let_tuple_desugared1" "let x = (3, 2)[0] in let y = (3, 2)[1] in x" "" "3";
  t "let_tuple_desugared2" "let x = (3, 2)[0] in let y = (3, 2)[1] in y" "" "2";
  t "let_tuple_desugar_nested" "let (x1, (x2, (x3, (x4, (x5, rest))))) = (1, (2, (3, (4, (5, (6, (7, (8, nil)))))))) in x2 + x3 + x4" "" "9";
  (* tuple basic errors *)
  terr "let_tuple_err_basic" "let (x, x) = (3, 3) in x" "" "The identifier x, redefined at";
  terr "let_tuple_err_nested" "let (x, (y, x)) = (3, (4, 2)) in y" "" "The identifier x, redefined at";
  terr "let_tuple_err_in_nested" "let (y, (x, x)) = (3, (4, 2)) in y" "" "The identifier x, redefined at";
  terr "let_tuple_err_in_body" "let (y, (x, z)) = (1, (true, (2, 4))) in a" "" "The identifier a, used at";
  (* some more tuple edge cases *)
  t "let_nested_tuple_z" "let x = (1, 2) in let (y, z) = x in z" "" "2";
  t "let_nested_tuple_y" "let x = (1, 2) in let (y, z) = x in y" "" "1";
  t "let_tuple_arg_nested" "let (x, (y, z)) = (1, (2, 3)) in z" "" "3";
  t "let_nested_tuple_nested" "let (x, (y, z)) = (1, (2, 3)) in let (a, (b, c)) = (x, (y, z)) in a + b" "" "3";
  (* t "let_tuple_input" "let (x, (y, z)) = (1, (2, 3)) in let (a, (b, c)) = (x, (input(), z)) in a + b" "5" "4"; *) (* TODO fix this for FDL *)
]

let decl_tuple_interactions = [
  t "basic_tuple_as_an_arg" "def f(a): a[0] := 100\nlet z = (1, 2, 3) in f(z); z" "" "(100, 2, 3)";
  t "function_return_tuple" "def f(a): let (b, c) = a in (b + 1, c + 1)\nf((1, 2))" "" "(2, 3)";
  t "tuple_as_not_the_first_arg" "def f(a, b, c): a + b[0] + c\nf(1, (1,), 1)" "" "3";
  t "fun_returns_tuple_of_args" "def f(a, b): (a, b)\nf(100, 3)" "" "(100, 3)";
  t "fun_takes_multiple_tuples" "def f(a, b): let (a1, a2) = a in let (b1, b2) = b in (a1 + b1, a2 + b2)\nf((1, 2), (10, -2))" "" "(11, 0)";
  (* Tests tuple desugaring in args *)
  t "tuple_arg_desugaring" "def f((x1, x2), y): x1 + x2 + y\nf((1, 2), 3)" "" "6";
  t "tuple_arg_desugared" "def f(x, y): let (x1, x2) = x in x1 + x2 + y\nf((1, 2), 3)" "" "6";
  (* Tests tuple errors in a function *)
  terr "tuple_func_err_not_tuple" "def f(x): x[1] := 2 \n f(0)" "" "expected a tuple";
  terr "tuple_func_err_out_of_bounds" "def f(x): x[1] := 2 \n f((1,))" "" "out of bounds";
  (* Function call as an element in a tuple *)
  t "tuple_func_call" "def f(x): 5 \n let (x1, x2) = (1, 2) in (x1, x2, f(x1), x1)" "" "(1, 2, 5, 1)";
  t "tuple_func_call_2" "def f(x): 1 + g() and \n def g(): 10 \n (g(), f(100) * 2)" "" "(10, 22)";
  t "tuple_set_recursive"
    "def update(tup, idx, val): 
        if idx == 0: 
            tup[idx] := val 
        else: 
            tup[idx] := val;
            update(tup, idx - 1, val) 
    let a = (1, 2, 3) in update(a, 1, 99); a"
    "" "(99, 99, 3)";
  t "tuple_build_recursive"
    "def build_tuple(tup, idx, len): 
     if idx == len: 
        tup 
     else: 
        tup[idx] := idx * 2; 
        build_tuple(tup, idx + 1, len) 
     let a = (0, 0, 0, 0) in build_tuple(a, 0, 4); a"
    "" "(0, 2, 4, 6)";
  t "tuple_swap"
    "def swap(tup, idx1, idx2):
      let a = tup[idx1] in
        tup[idx1] := tup[idx2];
        tup[idx2] := a;
        tup
     let b = (1, 2, 3) in
     swap(b, 0, 2)"
    "" "(3, 2, 1)";  
]

let args_are_correct_in_funcs = [
  t "print_false" "print(false)" "" "false\nfalse";
  t "basic_if_false" "def f(x): if x: 1 else: 2 \n f(false)" "" "2";
  t "basic_if_true" "def f(x): if x: 1 else: 2 \n f(true)" "" "1";
  t "identity_false" "def f(x): x \n f(false)" "" "false";
  t "identity_true" "def f(x): x \n f(true)" "" "true";
  t "identity_num" "def f(x): x \n f(1)" "" "1";
  t "identity_tuple" "def f(x): x \n f((1, true, (false,)))" "" "(1, true, (false,))"; 
]

(* Function tests *)

let function_calling_tests = [
  t "declaration" "def add_one(x) : add1(x) \n add_one(2)" "" "3";
  t "declaration_2args" "def add_one(x, y) : add1(x) \n add_one(2, 3)" "" "3";
  t "declaration_nested" "def fact(x) : if (x > 1): x * fact(x - 1) else: x \n fact(3)" "" "6";
  t "declaration_calls_into_another_fun" "def a(b) : add1(b) \n def c(d) : a(d) \n c(a(4))" "" "6";
]

let function_edge_cases = [
  terr "fun_error_redefined_add1" "def add1(x) : add1(x) \n add1(3)" "" "Parse error";
  terr "fun_error_redefined_function_same_arity" "def yay(x) : print(x) \n def yay(x) : add1(x) \n yay(4)" "" "The function name yay, redefined at";
  terr "fun_error_redefines_function_different_arity" "def omg(a, b) : print(b) + 1 \n def omg(b): b - 3 \n add1(1)" "" "The function name omg, redefined at";
  terr "fun_error_same_fun_redefined" "def a(x) : x \n def a(x) : x \n a(4)" "" "The function name a, redefined at";
  (* following function gives two errors: arity and duplicate function name error *)
  terr "fun_error_mutually_rec_same_name_wrong_arity" "def a(x) : a(x, 0) \n def a(x, y) : x + y \n a(4)" "" "The function name a, redefined at";
  terr "fun_error_bad_arg_name" "def z(1, z1) : 1 \n z(2 , 3)" "" "Parse error";
  (* add $ to function labels to avoid this explosive power *)
  terr "fun_error_call_ocsh_1" "our_code_starts_here()" "" "The identifier our_code_starts_here";
  terr "fun_error_call_ocsh_2" "our_code_starts_here()" "" "is not in scope";
  (* both x and z are out of scope in b *)
  terr "fun_error_no_bleeding_env_x" "def a(x) : x \n def b() : x + z \n let z = 3, y = a(3) in b()" "" "The identifier x, used at";
  terr "fun_error_no_bleeding_env_z" "def a(x) : x \n def b() : x + z \n let z = 3, y = a(3) in b()" "" "The identifier z, used at";
  (* id and function out of scope when flipping *)
  terr "fun_error_flipped_arg_fun_name_funcx" "def a(x) : x(a) \n a(3)" "" "Call wasn't closure";
  terr "fun_error_flipped_arg_fun_name_ida" "def a(x) : x(a) \n a(3)" "" "Call wasn't closure";
  terr "fun_error_malformed_def" "def a(x) : " "" "Parse error";

  terr "fun_error_no_program_body" "def a(x) : 3" "" "Parse error";
  terr "fun_error_redef_overflow" "def overflow(a): print(a + 100) \n overflow(a)" "" "The identifier a, used at";
  (* Calling an unreal function *)
  terr "fun_error_calling_undefined_fun" "def a(x) : let b = 0 in b + x \n let z = b(4) in a(z)" "" "The identifier b, used at";
  (* Duplicate identifier in fun args *)
  terr "fun_error_multiple_ids" "def a(x, x) : 2 * 1 \n a(1, 2)" "" "The identifier x, redefined at ";
  terr "fun_error_multiple_interspersed_ids" "def a(x, y, x) : 2 * 1 \n a(1, 2, 3)" "" "The identifier x, redefined at ";
  terr "fun_error_more_than_2_dup_ids" "def a(x, y, x, y, x) : 2 + 37 \n a(1,2,3,4,5)" "" "The identifier x, redefined at ";
  terr "fun_error_more_than_2_dup_ids_2" "def a(x, y, x, y, x) : 2 + 37 \n a(1,2,3,4,5)" "" "The identifier y, redefined at ";
  t "fun_error_arg_name_ocsh" "def a(our_code_starts_here) : our_code_starts_here \n a(4)" "" "4";
  t "fun_edge_case_printing_result" "def a() : 3 \n print(a())" "" "3\n3";
  t "fun_print_to_make_sure_not_eval_multiple_times" "def a(x) : add1(x) \n a(print(3))" "" "3\n4";
  t "fun_error_aliasing_16" "def a(a, b, c, d, e, f, g, h) : a+b+c+d+e+f+g+h \n a(1,2,3,4,5,6,7,8)" "" "36";
  t "fun_error_redef_ocsh" "def our_code_starts_here() : 1 \n 0" "" "0";
  t "fun_error_shadow_arg" "def a(x) : let x = 3 in x + 1 \n a(10)" "" "4";
  t "fun_error_redef_handle_errpr" "def handle_error() : 3 \n handle_error()" "" "3";
]

let fdl_well_scoped_tests = [
  terr "invalid_lambda_body" "let a = (lambda (x, y): x + z) in a(5, 5)" "" "The identifier z, used at";
  terr "invalid_let_body" "let a = (lambda (x, y): x + y) in b(5, 5)" "" "The identifier b, used at";
  terr "invalid_no_env_leak" "let a = (lambda (x, y): x + y) in a(x, 5)" "" "The identifier x, used at";
  terr "invalid_invalid_lambda_bind" "let a = (lambda (x, x): x + y) in a(4, 5)" "" "The identifier x, redefined at";
  terr "invalid_inner_tuple" "let a = (lambda (x, (z, b), (s, b)): x + y) in a(4, 5)" "" "The identifier b, redefined at";
  terr "invalid_inner_tuple_2" "let a = (lambda (x, (z, b), (s, x)): x + y) in a(4, 5)" "" "The identifier x, redefined at";
  terr "invalid_letrec_dup_in_lambda" "let rec add = (lambda (x, x): x + y) in add(5, 6)" "" "The identifier x, redefined at";
  terr "invalid_letrec_dup_in_names" "let rec add = (lambda (x, y): add(x + y)), add = (lambda (x, y): x + y) in 5" "" "The identifier add, redefined at";
  terr "invalid_letrec_not_func" "let rec add = 5 in 5" "" "Let-rec expected a name binding to a lambda";
  terr "invalid_letrec_not_func_recc" "let rec add = (lambda (x, y): add(x + y)), y = 5 in 5" "" "Let-rec expected a name binding to a lambda";
  terr "invalid_ordering_def_out_of_scope" "def a(): b() \n def b(): 2 \n 3" "" "The identifier b, used at"; (* opposite ordering ok dokie *)
  (* this passes well scoped but not yet compiling *)
  t "ordering_def_not_out_of_scope" "def a(): b() and def b(): 2 \n 3" "" "3";
  t "valid_ordering_and_recursive" "def b(): 2 \n def a(): b() \n 3" "" "3";
  t "valid_ordering_and_recursive2" "def b(): b() \n def a(): b() \n 3" "" "3";
  t "valid_ordering_and_recursive3" "def b(): a() and \n def a(): b() \n 3" "" "3";
  (* unit test from a bug in scoping *)
  t "defined_in_body" "let add2 = (lambda (x): x + 2) in 
                         let rec sub_1 = (lambda (x): add2(x) - 3) in 
                         sub_1(5)" "" "4";
  (* Should pass well formed since they are runtime defined *)
  t "print_wellformed_test" "print(3)" "" "3\n3";
  t "input_wellformed_test" "input()" "1" "1";
  t "equal_wellformed_test" "equal(1, 3)" "" "false";
  t "naitive_in_let" "let x = print(2) in 2" "" "2\n2";
]

(* let fdl_free_vars = [
  tfvs "simple_2_var_test" "x + y" ["x"; "y"]; 
  tfvs "simple_nested_lambda" "let f = (lambda (x): x + y) in 0" ["y"];
  tfvs "function_name_unbound" "f(x)" ["f"; "x"];
  tfvs "let_bound_var_isnt_caught" "let x = 1 in let f = (lambda (z, y): y + x + a * b(a)) in f(x)" ["a"; "b"];
  tfvs "let_bound_name_is_fine" "let x = 1 in x + y" ["y"];
  tfvs "let_ordering_matters" "let f = (lambda (z, y): y + x + a * b(a)) in let x = 1 in f(x)" ["a"; "b"; "x"];
  tfvs "let_multiple_bound" "let add = (lambda (bogus): x + y) in let sub = (lambda (bogus): y - x) in 2 + 1" ["x"; "y"];
  tfvs "let_multiple_bound_renamed" 
       "let add = (lambda (bogus): x_add + y_add) in let sub = (lambda (bogus): y_sub - x_sub) in 0" 
       ["x_add"; "y_add"; "x_sub"; "y_sub"];
] *)

let function_lambda_tests = [
  t "let_basic_add" "let add : int * int -> int = (lambda (x: int, y: int): x + y) in add(3, 5)" "" "8";
  t "let_basic_sub" "let sub : int * int -> int = (lambda (x: int, y: int): x - y) in sub(27, 9)" "" "18";
  (* basic self function *)
  t "recur" "let rec zero : int -> int = (lambda (x: int): if (x < 0): 0 else: zero(x - 1)) in zero(2)" "" "0";
  (* t "factorial_recursive" "let rec factorial = (lambda (n): if n == 0: 1 else: n * factorial(n - 1)) in factorial(5)" "" "120";
  t "recursive_lambda" "let rec f = (lambda (x): if x == 0: 0 else: f(x - 1)) in f(5)" "" "0";
  (* body calls *)
  t "in_body_call" "(lambda(y): y)(1)" "" "1";
  t "let_in_lambda" "(lambda (a): let x = 5 in 3 + a)(5)" "" "8";
  t "let_mix_args" "let set = (lambda(tup, idx, new_val): tup[idx] := new_val), t = (1, true), _ = set(t, 0, false) in t" "" "(false, true)";
  t "let_polynomial" "let poly = (lambda (a, x, b): a * x + b) in poly(3, 2, 7)" "" "13"; 
  t "if_false_in_lambda" "(lambda (b): if b: 100 else: 10)(false)" "" "10";
  t "if_true_in_lambda" "(lambda (b): if b: 100 else: 10)(true)" "" "100";
  (* interesting because it also shadows *)
  t "multiple_let_shadow" "let x = 5, y = 10, add = (lambda (x, y): x + y) in add(x, y)" "" "15";
  t "multiple_let_body_diff" "let x = 5, y = 10, add = (lambda (x, y): x + y) in add(3, 8)" "" "11";
  (* hehe 5 + 10 + 1 is 16 *)
  t "variable_bound_inside" "let x = 5, y = 10, add = (lambda (a): a + x + y) in add(1)" "" "16";
  t "shadowing" "let x = 5 in let x = 6 in x" "" "6";
  (* some errors *)
  terr "let_not_rec_but_rec" "let x = (lambda (y): if (y > 0): x(y - 1) else: 0) in x(2)" "" "The identifier x, used at ";
  terr "expected_numbers_got_tuple" "(lambda(x, y): x + y)((1, 2))" "" "Call had incorrect arity";
  terr "expected_numbers_got_tuple_v2" "(lambda(x, y): x + y)((1,), (2,))" "" "Arithmatic expected a number";
  terr "expected_numbers_got_boolean" "(lambda(x, y): x + y)(1, true)" "" "Arithmatic expected a number, but got true";
  terr "expected_bool_got_num" "(lambda(x, y): (!(x)) || y)(1, true)" "" "Logic expected a bool, but got 1";
  terr "expected_tuple_got_num" "(lambda (x): x[3])(1)" "" "Get expected a tuple, but got 1";
  terr "lambda_get_third_tuple_too_short" "(lambda (x): x[3])((1, 2))" "" "Tried to access out of bounds index for tuple, index too large";
  terr "lambda_get_neg_idx" "(lambda (x): x[-1])((1, 2))" "" "Tuple recieved a negative index, index too small";
  (* Capturing variables *)
  t "simple_var_capture" "let x = 103 in let f = (lambda: x) in f()" "" "103";
  t "simple_var_capture_2" "let x = false in let f = (lambda (y): x || print(y)) in f(true)" "" "true\ntrue";
  t "simple_var_capture_3" "let x = true in let f = (lambda (y): x || print(y)) in f(true)" "" "true";
  (* TODO this should get fixed when print is *)
  t "capture_multiple_and_mutate" "let a = (1, false), b = 3 in let f = (lambda (x): ((a[x] := b) + x)) in print(a);let c = f(1) in print(a);c" "" "(1, false)\n(1, 3)\n4";
  (* That one error *)
  t "uggggghghgghg_1" "let f = (lambda (x): x) in f(false)" "" "false";
  t "uggggghghgghg_2" "let f = (lambda (x): x) in f(true)" "" "true";
  (* Functions as args *)
  t "simple_function_as_arg" "let apply = (lambda (f, x): f(x)) in apply((lambda (x): !(x)), false)" "" "true";
  t "function_as_a_decl_arg" "def apply(f, x): f(x)\napply((lambda(x): x * -1), 10)" "" "-10";
  t "decl_as_a_decl_arg" "def apply(f, x, y): f(x, y)\ndef add(a, b): a+b\napply(add, 2, 3)" "" "5";
  t "decl_arg_to_lambda" "def add(a, b): a+b\n let apply = (lambda (f, x, y): f(x, y)) in apply(add, 4, -1)" "" "3";
  t "prim1_as_decl_arg" "def apply(f, x): f(x)\napply((lambda (y): add1(y)), 10)" "" "11";
  t "print_as_decl_arg" "def apply(f, x): f(x)\napply((lambda (z): print(z)), 4)" "" "4\n4";
  (* this showcases both equal and equal(...) *)
  t "equal_as_decl_arg_lambda_wrap" "def apply(f, x, y): f(x, y)\napply((lambda(x, y): equal(x, y)), (1, 3), (1, 3))" "" "true";
  t "equal_as_decl_arg_nolambda_wrap" 
       "def apply(f, x, y): f(x, y)\napply(equal, (1, 3), (1, 3))" 
       "" 
       "true";
  t "prim1_as_lam_arg" "let apply = (lambda (f, x): f(x)) in apply((lambda (x): add1(x)), -1)" "" "0";
  t "print_as_lam_arg" "let apply = (lambda (f, x): f(x)) in apply((lambda (x): print(x)), true)" "" "true\ntrue";
  t "equal_as_lam_arg" "let apply = (lambda (f, x, y): f(x, y)) in apply((lambda (x, y): equal(x, y)), (1, 3), (1, 3))" "" "true"; 
  t "pequal_as_lam_arg" "let apply = (lambda (f, x, y): f(x, y)) in apply((lambda (x, y): x == y), (1, 3), (1, 3))" "" "false"; 
  t "equal_int_as_lam_arg" "let apply = (lambda (f, x, y): f(x, y)) in apply((lambda (x, y): equal(x, y)), 1, 1)" "" "true"; 
  t "abs" "let abs = (lambda (x): if x > 0: x else: x * -1) in abs(10) + abs(input())" "-10" "20";
  (* TODO maybe some more cases of prims and natives and fun objs *)

  (* Capture of many datatypes *)
  t "capture_int" "let x = 12, f = (lambda: x) in f()" "" "12";
  t "capture_bool" "let x = false, f = (lambda: x) in f()" "" "false";
  t "capture_tup" "let x = (34,), f = (lambda: x) in f()" "" "(34,)";
  t "capture_lam_omg_also_returning_function" "let y = 21, x = (lambda: y), f = (lambda: x) in f()()" "" "21";
  t "multiple_function_applications_with_args" "let f = (lambda (x): (lambda (y): x + y)), g = (lambda (z): f(z)) in g(1)(2)" "" "3";
  t "capture_multiple_different_things" "let x = 1, y = false, f = (lambda (z): (z[0] >= x) || y) in f((input(), 0))" "3" "true";
  (* Trying to call some weird shit *)
  terr "call_num" "1(true)" "" "Call wasn't closure";
  terr "call_bool" "false(false)" "" "Call wasn't closure";
  terr "call_tuple" "(1,)()" "" "Call wasn't closure";
  terr "call_tuple_with_fun" "let f = (lambda (x): x) in (f,)(2)" "" "Call wasn't closure";
  t "call_id_which_is_fine" "let f = (lambda (x): x), g = f in g(3)" "" "3";
  t "call_unpacked_tuple" "let f_t = (1, (lambda: 2)) in f_t[1]()" "" "2";
  terr "call_one_tuple_function" "let f_t = ((lambda: 2),) in f_t()" "" "Call wasn't closure";
  terr "call_bad_id" "let x = 2 in x(3)" "" "Call wasn't closure";
  t "call_renamed_native" "let x = (lambda (x): print(x)) in x(3)" "" "3\n3";
  t "call_renamed_prim" "let x = (lambda(y): add1(y)) in x(-2)" "" "-1";
  (* We modified the parser to support this *)
  t "call_renamed_native_err" "let x = print in x(3)" "" "3\n3";
  (* but not this *)
  terr "call_renamed_prim_err" "let x = add1 in x(-2)" "" "ParseError";
  t "call_raw_lambda" "(lambda (x): x + 3)(4)" "" "7";
  
  (* Eval order of lambda args *)
  t "eval_order" "let f = (lambda (x, y): print(x + 2) + print(y + 2)) in f(print(1), print(2))" "" "1\n2\n3\n4\n7";
  t "eval_order_body" "let f = (lambda (x, y): print(x + 2) + print(y + 2)) in f(1, 2)" "" "3\n4\n7";
  t "eval_order_args" "let f = (lambda (x, y): x + y) in f(print(1), print(2))" "" "1\n2\n3";
  t "eval_order_p1" "let f = (lambda (x, y): x + print(y)) in f(1, print(2))" "" "2\n2\n3";
  t "eval_order_p2" "let f = (lambda (x, y): x + print(y)) in f(1, 2)" "" "2\n3";
  t "eval_order_p3" "let f = (lambda (x, y): x + print(y)) in f(print(1), 2)" "" "1\n2\n3";
  t "fun_error_redef_overflow_diff_arity" "def overflow(): print(777) \n overflow()" "" "777\n777";
  (* failing due to printing *)
  t "tuple_false_arg" "def f(x): print(x) \n f((false,))" "" "(false,)\n(false,)";
  t "if_in_func" "def f(x): if false: print(true) else: print(false) \n f(123)" "" "false\nfalse";
  t "print_false_two_arg" "def f(x, y): print((x, y)) \n f(false, false)" "" "(false, false)\n(false, false)";
  t "print_false_in_func" "def f(x): print(x) \n f(false)" "" "false\nfalse"; 
  (* TODO this should get fix when we fix our fucked up implementation *)
  (* t "fun_error_redef_print" "def print(x) : add1(x) \n print(2)" "" "2\n2"; *)
   *)
]

let more_fdl_tests = [
  (* nested function call *)
  t "function_in_function_call" "let f = (lambda (x): (lambda (y): x + y)) in f(6666)(2232)" "" "8898";
  t "nested_functions_scope" "let outer = (lambda (x): let inner = (lambda (y): x + y) in inner(2)) in outer(3)" "" "5";
  t "function_returning_function" "let f = (lambda (x): (lambda (y): x + y)) in f(3)(4)" "" "7";
  t "function_as_argument" "let apply2 = (lambda (f, x): f(f(x))) in apply2((lambda (x): x * 2), 4)" "" "16";
  (* Let binding and function *)
  t "let_binding_function" "let a = 5 in let add_five = (lambda (x): x + a) in add_five(3)" "" "8";
  (* Calling a function with tuple argument *)
  t "function_with_tuple" "let f = (lambda (t): t[0] + t[1]) in f((1, 2))" "" "3";
  (* Incorrect number of arguments for function *)
  terr "incorrect_arity" "let add = (lambda (x, y): x + y) in add(1)" "" "Call had incorrect arity";
  terr "invalid_function_call_in_let" "let x = 5 in x(3)" "" "Call wasn't closure";
  terr "calling_number" "1(3)" "" "Call wasn't closure";
  (* Function with boolean argument *)
  t "boolean_argument_function" "let f = (lambda (x): if x: 1 else: 0) in f(true)" "" "1";
  t "function_return_tuple" "let f = (lambda (x): (x, x + 1)) in f(5)" "" "(5, 6)";
  (* Calling a function with invalid tuple argument type *)
  terr "invalid_tuple_index" "(lambda (x): x[3])((1, 2))" "" "Tried to access out of bounds index for tuple, index too large";
  terr "tuple_argument_type_error" "let f = (lambda (x): x + 1) in f((1,))" "" "Arithmatic expected a number, but got";
]

let fdl_errors_in_lambdas = [
  terr "add_took_boolean" "(lambda (x, y): x + y)(true, false)" "" "Arithmatic expected a number, but got false";
  terr "if_takes_closure" "if (lambda (x, y): 3): 2 else: 1" "" "If expected a bool condition, but got";
  terr "if_takes_closure_of_boolean" "if (lambda: true): 2 else: 1" "" "If expected a bool condition, but got";
]

let printing_closures = [
  t "print_some_closure" "(lambda: 1)" "" "<function arity 0>";
  t "print_clos_in_tup" "(0, (lambda (x): (lambda (y): x + y)))" "" "(0, <function arity 1>)";
]

(* These are all things that were broken in (egg,) because we had a half baked implementation... they haven't been fixed yet, so we are leaving them here *)
let failing_tests = [ 
  (* sigint? *)
  t "failing_tup_set" "let a = (1,), b = (2,) in a[0] := b; b[0] := a; a" "" "";

  (* TODO these fail bc :P *)
  t "nil_unpack" "let (a, b) = nil in a" "" "";
  t "nil_get_2" "nil[0]" "" "";
  t "nil_set_2" "nil[0] := ()" "" "";

  (* Desugar wrong arity *)
  (* TODO restore all this bc it has weird things happening rn *)
  t "too_many_args_let_tup_desugar" "let (x, y, z) = (1, 2) in y" "" "";
  t "too_few_args_let_tup_desugar" "let (x, y) = (1, 2, 3) in y" "" "";
  t "nested_incorrect_tup_desugar_1" "let (x, (y, z)) = (1, 2) in x" "" "";
  t "nested_incorrect_tup_desugar_2" "let (x, (y, z)) = (1, (1, 2, 3)) in x" "" "";
  t "nested_incorrect_tup_desugar_3" "let (x, (y, z)) = (1, (2,)) in x" "" "";  
]

(* making sure pass integrations pass and fail integrations fail (tests ones untested above) *)
let integrations = [
  (* do_err/* directory *)
  teprog "do_err/and_got_num.racer" "Logic expected a bool, but got 123";
  teprog "do_err/arith_got_logic.racer" "Arithmatic expected a number, but got false";
  teprog "do_err/if_got_num.racer" "If expected a bool condition, but got 0";
  teprog "do_err/or_got_num.racer" "Logic expected a bool, but got 123";
  teprog "do_err/overflow.racer" "Arithmatic operation overflowed";
  (* do_pass/* directory *)
  tprog_input "do_pass/add_inputs.racer" "3\n4" "7";
  tprog "do_pass/is_odd_mutual_rec_9.racer" "7\n5\n3\n1\ntrue"; 
  tprog "do_pass/more_complex_func.racer" "2\n4\n6\n8\n10\n12\n14\ntrue";
  tprog_input "do_pass/list_program.racer" "true\n1\ntrue\n2\ntrue\n3\ntrue\nfalse\nfalse" "(1, (2, (3, nil)))";
  (* reverses (list 1 2 3) and nil *)
  tprog "do_pass/reverse.racer" "((3, (2, (1, nil))), nil)";
  tprog "do_pass/higher_order.racer" "2";
  (* length of (list 1 2 3) and nil *)
  tprog "do_pass/length.racer" "(3, 0)"; 
  tprog "do_pass/logic_with_lets.racer" "true\ntrue\ntrue\nfalse\nfalse\nfalse";
  tprog "do_pass/long_program1.racer" "-119";
  tprog "do_pass/long_program2.racer" "419";
  tprog "do_pass/long_program3.racer" "1236";
  tprog "do_pass/manylets.racer" "true\n10\n3\n13\n14\ntrue\ntrue";
  tprog "do_pass/print_if.racer" "3\n6\n18";
  tprog "do_pass/scope_and_if.racer" "-1";
  tprog "do_pass/so_many_prints.racer" "false\ntrue\n4\n3\ntrue\ntrue\ntrue\ntrue\n3\ntrue\n31\n32\n32";
  tprog "do_pass/test1.racer" "3";

  tprog "do_pass/func_test.racer" "6";
  tprog "do_pass/in2.racer" "5";
  tprog "do_pass/add_let.racer" "4";
  tprog "do_pass/tail_call.racer" "6";
  tprog "do_pass/tree.racer" 
  "(false, (3, false, false), (3, false, (4, false, false)), (3, false, (4, false, (5, false, false))), (3, (2, false, false), (4, false, (5, false, false))))";

]


(* For some reason these work on their own and fail when all together? *)
(* I think this is a thing that's broken on henry's computer and not mine *)
(* I'm going to leave these here for now *)
let each_work_on_their_own_integrations = [
  (* a program for binary trees *)
  (* true continues, anything other returns whatever the tree is *)
  (* false allows you to insert a number into the tree or listify the tree
     by specifying a non-number *)
  (* tprog_input "do_pass/bt_program.racer" "1" "false";
  tprog_input "do_pass/bt_program.racer" "true\nfalse" "nil";
  tprog_input "do_pass/bt_program.racer" "true\ntrue" "nil"; *)
  tprog_input "do_pass/bt_program.racer" "true\n1\nfalse" "(1, false, false)";
  (* tprog_input "do_pass/bt_program.racer" "true\n1\ntrue\nfalse" "(1, nil)"; *)

  (* fun program where *)
  (* anything but true -> end and return list as is, 
     true -> enter a number to prepend to list
     true -> enter false to run with the sum as first element
     true -> enter true to prepend sum to list  *)
  (* tprog_input "do_pass/list_program.racer" "1" "nil";
  tprog_input "do_pass/list_program.racer" "true\n1\nfalse" "(1, nil)";
  tprog_input "do_pass/list_program.racer" "true\n1\ntrue\n2\ntrue\n3\nfalse" "(3, (2, (1, nil)))"; *)
  tprog_input "do_pass/list_program.racer" "true\n1\ntrue\n2\ntrue\n3\ntrue\ntrue\nfalse" "(6, (3, (2, (1, nil))))";

  (* failing function call integrations tests *)
  (* I think this fails due to a linux thing? *)
  (* tprog_input "do_pass/is_odd_input.racer" "0" "false";
  tprog_input "do_pass/is_odd_input.racer" "2" "false";
  tprog_input "do_pass/is_odd_input.racer" "-1" "true";
  tprog_input "do_pass/is_odd_input.racer" "3" "true"; *)
  tprog_input "do_pass/is_odd_input.racer" "-4" "false";

  (* def a linux thing lmao works fine on mac *)
  (* tprog_input "do_pass/nested_input.racer" "1\n" "false";
  tprog_input "do_pass/nested_input.racer" "false" "false"; *)
  tprog_input "do_pass/nested_input.racer" "true" "123";
]


let heap_size_garbage_collection = [
  (* 24 words for native funcs + 4 for a tuple *)
  tgc "gctest_natives_mem_ok" 24 "1" "" "1";
  tgc "gctest_tuple_mem_ok" 30 "(true, 1, 2)" "" "(true, 1, 2)";
  (* natives have no where to go *)
  tgcerr "gctest_0_mem" 0 "1" "" "Allocation error: needed 6 words, but"; 
  (* tuple has no where to go *)
  tgcerr "gctest_8_mem_tup" 3 "(true, 1, 2)" "" "Allocation error";
  (* takes up 34 words pre garbage collection, natives should be garbaged and we should be able to then allocate within < 34 words *)
  tgcerr "gctest_fails" 5 "def add(x, y): x + y \n def sub(x, y): x - y \n add(5, 3)" "" "Allocation error";
  tgc "gctest_fails2" 30 "def add(x, y): x + y \n def sub(x, y): x - y \n add(5, 3)" "" "8";
  (* These three tests are constructed to intentionally collect tmp as garbage when we try to alloc (6, 7, 8)*)
  tgc "actually_collects_garbage_with_good_heap_size" 31 "def f(): let tmp = (1, 2, 3) in 1 \n let z = (4, 5), y = f() in (6, 7, 8)" "" "(6, 7, 8)";
  tgcerr "actually_collects_garbage_with_bad_heap_size" 10 "def f(): let tmp = (1, 2, 3) in 1 \n let z = (4, 5), y = f() in (6, 7, 8)" "" "Out of memory";
  tgcerr "actually_collects_garbage_with_bad_heap_size_2" 9 "def f(): let tmp = (1, 2, 3) in 1 \n let z = (4, 5), y = f() in (6, 7, 8)" "" "Out of memory";
  tprog "do_pass/very_nested_gc_1.racer" "<function arity 1>\n2";
  tprog "do_pass/gc_in_function_stack_1.racer" "14";
  (* due to alpha renaming, both x's remain on the stack *)
  tgc "gcs_shadow" 28 "let x = (1, 2, 3) in let x = 4 in (5, 6, 7)" "" "(5, 6, 7)";
  tgc "if_no_shadow" 28 "let x = (1, 2, 3) in let y = 4 in (5, 6, 7)" "" "(5, 6, 7)";
  tgc "gc_nested_calls" 34 "def f(x): let a = (x, x+1) in g(x+1) and def g(y): let b = (y, y+1) in 42 \n f(1)" "" "42";
  tgc "gc_inner_tuple_overwrite" 32 "let x = ((1, 2), 3, 4) in let _ = x[0] := 1 in (2, 3, 4)" "" "(2, 3, 4)";
  tgc "gc_inner_tuple" 32 "let x = ((1, 2), 3, 4) in (2, 3, 4)" "" "(2, 3, 4)";
  tgc "gc_fun_inner_tuple" 36 "def f(): let tmp = (1, (2,), 3) in 1 \n let z = (4, 5), y = f() in (6, 7, 8)" "" "(6, 7, 8)";
  tgc "gc_recursive_alloc" 36 "def f(n): if n == 0: (1, 2, 3) else: let x = (n, n+1, n+2) in f(sub1(n)) \n f(3)" "" "(1, 2, 3)";
  (* tgc "gc_tuple_debind_rebind" 20 "def f(): let temp = (1, 2, 3) in temp[0] \n (f(), 2, 3)" "" "(1, 2, 3)"; *)
  tgcerr "gc_tuple_debind_rebind2" 5 "def f(): 1 \n ((1, 2, 3), 2, 3)" "" "Allocation error";
]

let extern_name_override = [
  terr "asm_name_colide1" "let HEAP? = 20 in HEAP?" "" "Unrecognized character: H";
  terr "asm_name_colide2" "let HEAP = 20 in (1, 2, 3, HEAP)" "" "Unrecognized character: H"; 
  terr "asm_name_colide3" "let ?our_code_starts_here = 20 in ?our_code_starts_here" "" "Unrecognized character: ?";
  terr "asm_name_colide4" "let ?error = 20 in ?error" "" "Unrecognized character: ?";
  terr "asm_name_colide5" "let ?set_stack_bottom = 20 in ?set_stack_bottom" "" "Unrecognized character: ?";
  terr "asm_name_colide6" "let ?try_gc = 20 in ?try_gc" "" "Unrecognized character: ?"; 
  terr "overriding_numtag" "let NUM_TAG = 0 in NUM_TAG + 23" "" "Unrecognized character: N";
]

let pre_racer_language_non_alloced =
  []
  @ sanity_tests
  @ not_tests
  @ if_tests
  @ comparison_tests
  @ prim2_tests
  @ prim1_test
  @ ifexp_test
  @ let_tests 
  @ basic_numbers_tests 
  @ big_number 
  @ and_or_op_tests  
  (* @ is_type_tests  *)
  @ prim1_type_checking 
  @ prim2_type_checking
  @ print_tests 
  @ short_circuits_tests 
  @ overflow_tests
  @ tuple_get_tests 
  @ tuple_set_tests 
  @ basic_tuple_tests
  @ extra_tuple_tests
  (*
  @ input_test 
  @ equals_test 
  @ let_egg_tests
  @ decl_tuple_interactions
  @ args_are_correct_in_funcs 
  @ fdl_errors_in_lambdas
  @ fdl_well_scoped_tests *)
  @ function_lambda_tests
  (*
  @ more_fdl_tests
  @ printing_closures
  @ function_calling_tests
  @ function_edge_cases
  @ heap_size_garbage_collection
  @ extern_name_override *)

let pre_racer_language_tests =
  "pre_racer_language_tests"
  >::: [] 
  @ (make_naive pre_racer_language_non_alloced)
  (* @ (make_register pre_racer_language_non_alloced) *)


let integrations = "integrations"
  >::: [
  (* t "nested_underscores_but_this_time_in_a_function" "def f(_, x, _, (y, _)): x + y\nf(1, 2, 3, (4, 5))" "" "6"; *)
  ] 
  (* @ each_work_on_their_own_integrations *)
  (* @ (make_naive integrations) *)
  @ (make_register integrations)
;;


(* first robotics comptition more like free vars cache 
  (this is an extremely specific joke that ik julia will get) *)

(* note that these tests are indirect ones; but good enough for me to *believe* this works *)
let free_vars_cashe_test = [
  tfvs_c "c/simple_2_var_test" "x + y" ["x"; "y"]; 
  tfvs_c "c/simple_nested_lambda" "let f = (lambda (x): x + y) in 0" ["y"];
  tfvs_c "c/function_name_unbound" "f(x)" ["f"; "x"];
  tfvs_c "c/let_bound_var_isnt_caught" "let x = 1 in let f = (lambda (z, y): y + x + a * b(a)) in f(x)" ["a"; "b"];
  tfvs_c "c/let_bound_name_is_fine" "let x = 1 in x + y" ["y"];
  tfvs_c "c/let_ordering_matters" "let f = (lambda (z, y): y + x + a * b(a)) in let x = 1 in f(x)" ["a"; "b"; "x"];
  tfvs_c "c/let_multiple_bound" "let add = (lambda (bogus): x + y) in let sub = (lambda (bogus): y - x) in 2 + 1" ["x"; "y"];
  tfvs_c "c/let_multiple_bound_renamed" 
       "let add = (lambda (bogus): x_add + y_add) in let sub = (lambda (bogus): y_sub - x_sub) in 0" 
       ["x_add"; "y_add"; "x_sub"; "y_sub"];
  tfvs_c "c/let_rec_can_recur" "let rec f = (lambda (x): f(x) + a) in f(3)" ["a"];
  tfvs_c "c/let_rec_can_mutually_recur" "let rec f = (lambda (x): g(x) + a), g = (lambda (y): f(y) + b) in f(3)" ["a"; "b"];
]

(* Tests that come up while writing racer *)
let racer_language_tests = "racer_language_tests"
  >::: []
  @ free_vars_cashe_test
;;


let test_parser = [
  (* Basic types *)
  tparse "parse_no_types" "2" (Program ([], [], (ENumber (2L, ())), ()));
  tparse "parse_single_int" "type a = int \n 2" (Program ([(DType ("a", (TInt ()), ()))], [], (ENumber (2L, ())), ()));
  tparse "parse_single_bool" "type b = bool \n 2" (Program ([(DType ("b", (TBool ()), ()))], [], (ENumber (2L, ())), ()));
  (* product types *)
  tparse "parse_single_prod" 
         "type a = int * bool \n 2" 
         (Program ([(DType ("a", (TProduct ([TInt (); TBool ()], ())), ()))], [], (ENumber (2L, ())), ()));
  tparse "multiple_typ_products" 
         "type a = int * bool \n type b = bool * int \n 2"
         (Program ([(DType ("a", (TProduct ([TInt (); TBool ()], ())), ())); (DType ("b", (TProduct ([TBool (); TInt ()], ())), ()))], 
                   [], (ENumber (2L, ())), ()));
  tparse "parse_multiple_types" 
         "type a = int \n type b = bool \n 2" 
         (Program ([(DType ("a", (TInt ()), ())); (DType ("b", (TBool ()), ()))], [], (ENumber (2L, ())), ()));
  (* function types *)
  tparse "parse_single_function" "type b = bool -> int \n 2" (Program ([(DType ("b", (TFunction (TBool (), TInt (), ())), ()))], [], (ENumber (2L, ())), ()));
  tparse "parse_multiple_functions" "type c = int -> bool \n type d = int * int -> bool \n 2"
         (Program ([(DType ("c", (TFunction (TInt (), TBool (), ())), ())); 
                    (DType ("d", (TFunction ((TProduct ([TInt (); TInt ()], ())), (TBool ()), ())), ()))], 
                  [], (ENumber (2L, ())), ()));
  tparse "parse_function_product_typ" "type c = int -> bool * bool \n type d = int * int -> bool * bool  \n 2"
         (Program ([(DType ("c", (TFunction ((TInt ()), (TProduct ([TBool (); TBool ()], ())), ())), ())); 
                    (DType ("d", (TFunction ((TProduct ([TInt (); TInt ()], ())), (TProduct ([TBool (); TBool ()], ())), ())), ()))], 
                   [], (ENumber (2L, ())), ()));
  terr "parse_err_extra_rarrow" "type c = int -> -> bool \n 2" "" "ParseError";
  (* algebric types *)
  tparse "parse_algebric_type" "type a = | Int of int | Bool of bool \n 2"
         (Program ([(DType ("a", (TAlgebric ([("Int", TInt ()); ("Bool", TBool ())], ())), ()))],
                  [], (ENumber (2L, ())), ()));
  terr "parse_err_algebric_type_non_cap_cname" "type a = | int of int | Bool of bool \n 2" "" "ParseError";
  (* constructors *)
  tparse "parse_constructor" "type a = | Int of int \n Int(2)"
            (Program ([(DType ("a", (TAlgebric ([("Int", TInt ())], ())), ()))],
                      [], 
                      EConstructor ("Int", [(ENumber (2L, ()))], ()), 
                      ()));
  tparse "parse_empty_constructor" "Int ()"
  (Program ([],
            [], 
            EConstructor ("Int", [], ()), 
            ()));      
  tparse "parse_nested_constructor" "Some (Int (2))"
  (Program ([],
            [], 
            EConstructor ("Some", [EConstructor ("Int", [(ENumber (2L, ()))], ())], ()), 
            ()));                     
  (* match expressions *)
  tparse "parse_match_blank" "type a = | Int of int \n match x with | _ -> 2"
  (Program ([(DType ("a", (TAlgebric ([("Int", TInt ())], ())), ()))],
            [], 
            EMatch (EId("x", ()), [(PBlank (), (ENumber (2L, ())))], ()), 
            ()));
  tparse "parse_match_id" "type a = | Int of int \n match x with | y -> 2"
  (Program ([(DType ("a", (TAlgebric ([("Int", TInt ())], ())), ()))],
            [], 
            EMatch (EId("x", ()), [(PId ("y", ()), (ENumber (2L, ())))], ()), 
            ())); 
  tparse "parse_match_literal_bool" "type a = | Int of int \n match x with | true -> 2"
  (Program ([(DType ("a", (TAlgebric ([("Int", TInt ())], ())), ()))],
            [], 
            EMatch (EId("x", ()), [(PLiteral (LBool(true, ()), ()), (ENumber (2L, ())))], ()), 
            ())); 
  tparse "parse_match_literal_num" "type a = | Int of int \n match x with | 4 -> 2"
  (Program ([(DType ("a", (TAlgebric ([("Int", TInt ())], ())), ()))],
            [], 
            EMatch (EId("x", ()), [(PLiteral (LInt(4L, ()), ()), (ENumber (2L, ())))], ()), 
            ())); 
  tparse "parse_match_algeberic_2_args" "match x with | Int (x, false) -> 2"
  (Program ([], [], 
            EMatch (EId("x", ()), 
                    [(PConstructor ("Int", [PId ("x", ()); PLiteral (LBool(false, ()), ())], ()), 
                     (ENumber (2L, ())))], 
                    ()), 
            ()));   
  tparse "parse_match_algeberic_1_args" "match x with | Int (x) -> 2"
  (Program ([], [], 
            EMatch (EId("x", ()), 
                    [(PConstructor ("Int", [PId ("x", ())], ()), 
                      (ENumber (2L, ())))], 
                    ()), 
            ()));   
  tparse "parse_match_algeberic_0_args" "match x with | Int -> 2"
  (Program ([], [], 
            EMatch (EId("x", ()), 
                    [(PConstructor ("Int", [], ()), 
                      (ENumber (2L, ())))], 
                    ()), 
            ()));   
  tparse "parse_match_tuple" "match x with | (x, y) -> 2"
  (Program ([], [], 
            EMatch (EId("x", ()), 
                    [(PTup ([PId ("x", ()); PId ("y", ())], ()), 
                      (ENumber (2L, ())))], 
                    ()), 
            ()));   
  tparse "parse_match_tuple" "match x with | (x, y) -> 2"
  (Program ([], [], 
            EMatch (EId("x", ()), 
                    [(PTup ([PId ("x", ()); PId ("y", ())], ()), 
                      (ENumber (2L, ())))], 
                    ()), 
            ()));    
  tparse "parse_match_nested_tuple" "match x with | (x, (z, y)) -> 2"
  (Program ([], [], 
            EMatch (EId("x", ()), 
                    [(PTup ([PId ("x", ()); PTup ([PId ("z", ()); PId ("y", ())], ())], ()), 
                      (ENumber (2L, ())))], 
                    ()), 
            ()));  
  tparse "parse_match_multiple_branches" "type a = | Int of int \n match x with | 4 -> 2 | _ -> 5"
  (Program ([(DType ("a", (TAlgebric ([("Int", TInt ())], ())), ()))],
            [], 
            EMatch (EId("x", ()),
              [
              (PLiteral (LInt(4L, ()), ()), (ENumber (2L, ())));
              (PBlank (), (ENumber (5L, ())))
              ], 
              ()), 
            ())); 
  tparse "parse_simple_function" 
  "def add(x: int, y: int) -> int : x + y \n add(3, 5)" 
  (Program ([], 
            [[DFun ("add", 
                  [(BName ("x", TInt (), false, ())); (BName ("y", TInt (), false, ()))], 
                  TInt (), 
                  EPrim2 (Plus, EId ("x", ()), EId ("y", ()), ()), 
                  ())]], 
            EApp (EId ("add", ()), [ENumber (3L, ()); ENumber (5L, ())], Unknown, ()), 
            ()));
  tparse "parse_function_noargs" 
  "def add() -> int : 3 \n add()" 
  (Program ([], 
            [[DFun ("add", 
                  [], 
                  TInt (), 
                  ENumber (3L, ()), 
                  ())]], 
            EApp (EId ("add", ()), [], Unknown, ()), 
            ())); 
  tparse "parse_function_mismatch" 
  "(lambda (x: int, y: int) -> int : x && true)" 
  (Program ([], 
            [], 
            ELambda ([(BName ("x", TInt (), false, ())); (BName ("y", TInt (), false, ()))], 
            TInt (), 
            EPrim2 (And, EId ("x", ()), EBool (true, ()), ()), ()), 
            ())); 
  tparse "parse_type_algebra_no_param" "type a = | A | B \n 2"
  (Program ([(DType ("a", (TAlgebric ([("A", TProduct ([], ())); ("B", TProduct ([], ()))], ())), ()))],
            [], 
            (ENumber (2L, ())), 
            ())); 
  tparse "parse_construct_algebra_no_param_nospace" "A()"
  (Program ([],
            [], 
            (EConstructor ("A", [], ())), 
            ())); 
  tparse "parse_construct_algebra_no_param_space" "A ()"
  (Program ([],
            [], 
            (EConstructor ("A", [], ())), 
            ())); 
  tparse "parse_match_complex" "type a = | Some of int \n | None \n match Some(200) with | None -> 100 | Some(x) -> x "
  (Program ([(DType ("a", (TAlgebric ([("Some", TInt ()); ("None", TProduct ([], ()))], ())), ()))],
            [], 
            EMatch (EConstructor("Some", [ENumber(200L, ())], ()),
            [
              (PConstructor ("None", [], ()), (ENumber (100L, ())));
              (PConstructor ("Some", [PId ("x", ())], ()), (EId ("x", ())))
            ], 
              ()), 
            ())); 
  tparse "parse_match_complex_swapped" "type a = | Some of int \n | None \n match Some(200) with | Some(x) -> x | None -> 100"
  (Program ([(DType ("a", (TAlgebric ([("Some", TInt ()); ("None", TProduct ([], ()))], ())), ()))],
            [], 
            EMatch (EConstructor("Some", [ENumber(200L, ())], ()),
            [
              (PConstructor ("Some", [PId ("x", ())], ()), (EId ("x", ())));
              (PConstructor ("None", [], ()), (ENumber (100L, ())));
            ], 
              ()), 
            ())); 
  tparse "parse_no_arg_constructor_match" "type a = | Some of int \n | None \n match None with | Some(x) -> x | None -> 100"
  (Program ([(DType ("a", (TAlgebric ([("Some", TInt ()); ("None", TProduct ([], ()))], ())), ()))],
            [], 
            EMatch (EConstructor("None", [], ()),
            [
              (PConstructor ("Some", [PId ("x", ())], ()), (EId ("x", ())));
              (PConstructor ("None", [], ()), (ENumber (100L, ())));
            ], 
              ()), 
            ())); 
  tparse "parse_no_arg_constructor" "type a = | Some of int \n | None \n None"
  (Program ([(DType ("a", (TAlgebric ([("Some", TInt ()); ("None", TProduct ([], ()))], ())), ()))],
            [], 
            EConstructor("None", [], ()), 
            ())); 
  terr "killed_nil" "nil" "" "The identifier nil, used at <killed_nil, 1:0-1:3>, is not in scope";
  terr "killed_0arg_tup" "()" "" "ParseError";
  terr "killed_1arg_tup" "(1,)" "" "ParseError";
]

let test_typer_checker = [
  terr "duplicate_ids" "type a = int \n type a = int \n 2" "" "The type a, is both defined at <duplicate_ids, 1:0-1:12> and <duplicate_ids, 2:1-2:13>"; 
  terr "duplicate_ids_recurs" "type b = bool \n type a = int \n type a = int \n 2" "" "The type a, is both defined at "; 
  t "no_duplicates" "type a = int \n type b = int \n 2" "" "2";
  terr "duplicate_names" "type a = | Some of int | Some of bool \n 2" "" "There are two constructors with name Some, defined at <duplicate_names, 1:0-1:37>";
  terr "duplicate_names_recurs" "type b = int \n type a = | Some of int | Some of bool \n 2" "" "There are two constructors with name Some,";
  terr "no_recursive_constructor_types" "type c = | Bool of Some of int \n 2" "" "ParseError";
  terr "bind_non_exist_simple" "let a : list = 4 in 2" "" "The type list, used at <bind_non_exist_simple, 1:8-1:12>, is not defined";
  terr "bind_non_exist_function" "let f : int -> list = (lambda (x: int) -> int : x) in 2" "" "The type list, used at ";
  terr "bind_non_exist_tuple" "let t : int * list = (1, 2) in 2" "" "The type list";
  terr "bind_non_exist_function_in" "def add(x: int, y: asd) -> int : x + y \n 2" "" "The type asd";
  terr "bind_non_exist_function_out" "def add(x: int, y: int) -> asd : x + y \n 2" "" "The type asd";
  terr "plus_got_bool" "true + 3" "" "Got bool instead of type int at";
  terr "int_let_got_bool" "let x : int = true in 4" "" "Got bool instead of type int at";
  terr "looking_up_type_env" "let x : int = 1 in x && true" "" "Got int instead of type bool at";
  terr "lambda_incorrect_return_typ" "(lambda (x: int) -> int : false)" "" "Got bool instead of type int";
  terr "lambda_incorrect_given_typ_env" "(lambda (x: int) -> bool : x)" "" "Got int instead of type bool";
  terr "lambda_correctly_shadows" "let x : bool = true in (lambda (x: int) -> bool : x)" "" "Got int instead of type bool";
  (* terr "bind_non_exist_nested_tuple" "let t : (int * list) * bool = ((1, 2), true) in 2" "" ""; *)
  (* terr "bind_non_exist_algebric" "type a = | Some of list \n 2" "" "The type list"; *)
  terr "bind_non_exist_function_return" "let f : int -> list = (lambda (x: int) -> int : x) in f(2)" "" "The type list";
  terr "non-matching-lengths" "let f : int * int -> int = (lambda (x: int, y: int) -> int : x) in f(2)" "" "expected 2 type arguments but got 1";
  terr "non-matching-lengths1" "let f : int * int -> int = (lambda (x: int, y: int) -> int : x) in f(2, 3, 4)" "" "expected 2 type arguments but got 3";
  terr "non-matching-lengths2" "let f : int * int -> int = (lambda (x: int, y: int) -> int : x) in f()" "" "expected 2 type arguments but got 0";
  terr "incorrect_arg_provided" "let f : int * int -> int = (lambda (x: int, y: int) -> int : x) in f(1, true)" "" "Got bool instead of type int at";
  terr "invalid_type_in_lambda" "(lambda (x: int, y: int) -> int : x && y)" "" "Got bool instead of type int at";
  terr "invalid_type_in_lambda" "(lambda (x: int, y: int) -> int : x && true)" "" "Got bool instead of type int at";
  terr "invalid_get_non_imm_num" "(1, 2, 3)[1 + 0]" "" "ParseError";
  terr "invalid_get_non_tuple_non_imm_num" "1[1 + 2]" "" "ParseError";
  terr "invalid_get_non_tuple" "1[1]" "" "Attempted to do tuple action on non-tuple at invalid_get_non_tuple, 1:2-1:4";
  terr "invalid_get_out_of_bounds" "(1, 2, 3)[-1]" "" "The index -1 used at <invalid_get_out_of_bounds, 1:10-1:13> was out of bounds for tuple [0, 3)";
  terr "invalid_get_out_of_bounds1" "(1, 2, 3)[3]" "" "The index 3 used at <invalid_get_out_of_bounds1, 1:10-1:12> was out of bounds for tuple [0, 3)";
  terr "invalid_get_out_of_bounds2" "(1, 2, 3)[123123]" "" "The index 123123 used at <invalid_get_out_of_bounds2, 1:10-1:17> was out of bounds for tuple [0, 3)";
  terr "bounds_err_with_let" "let x: int * int * int = (1, 2, 3) in x[4]" "" "The index 4 used at <bounds_err_with_let, 1:40-1:42> was out of bounds for tuple [0, 3)";
  terr "invalid_tuple_lengths" "let x: int * int = (1, 2, 3) in 2" "" "Got (int, int, int) instead of type (int, int) at invalid_tuple_lengths";
  terr "invalid_tuple" "let x: int * int = 3 in 2" "" "Got int instead of type (int, int) at invalid_tuple, 1:19-1:20";
  (* constructor errors *)
  terr "invalid_constructor_arg_typ" "type x = | Some of int \n Some(true)" "" "Got bool instead of type int at invalid_constructor_arg_typ, 2:6-2:10";
  terr "invalid_constructor_num_arg1" "type x = | Some of int \n Some(1, 2)" "" "The constructor Some, used at <invalid_constructor_num_arg1, 2:1-2:11>, expected 1 arguments but got 2";
  terr "invalid_constructor_num_arg2" "type x = | Some of int \n Some()" "" "The constructor Some, used at <invalid_constructor_num_arg2, 2:1-2:7>, expected 1 arguments but got 0";
  terr "invalid_constructor_num_arg3" "type x = | Some \n Some(3)" "" "The constructor Some, used at <invalid_constructor_num_arg3, 2:1-2:8>, expected 0 arguments but got 1";
  terr "no_foo_constructor_exists" "type x = | Some \n Foo(3)" "" "The constructor named Foo, as used at <no_foo_constructor_exists, 2:1-2:7> wasn't found";
  t "tc-ok" "type x = | Some of int \n let y : x = Some(3) in 3" "" "3";
  terr "tc-invalid-consturctor-in-let" "type x = | Some of bool \n let y : x = Some(3) in 3" "" "Got int instead of type bool at ";
  terr "tc-invalid-consturctor" "type x = | Some of bool \n Some(3)" "" "Got int instead of type bool at ";
  terr "invalid_branching_typs" "match 1 with | x -> x | _ -> true" "" "Got bool instead of type int at invalid_branching_typs";
  terr "invalid_branch_pattern" "match 1 with | (x, y) -> 2" "" "The match at <invalid_branch_pattern, 1:0-1:26>, had an invalid pattern";
  terr "invalid_pattern_nested_tup" "match (1, 2, 3) with | (x, (2, 3), z) -> 3" "" "The match at <invalid_pattern_nested_tup, 1:0-1:42>, had an invalid pattern";
  terr "invalid_pattern_constructor" "type a = | Some of int \n match Some(5) with | Some(3, 2) -> 2" "" "The match at <invalid_pattern_constructor, 2:1-2:37>, had an invalid pattern";
  terr "invalid_pattern_constructor2" "type a = | Some of int \n match Some(5) with | _ -> 2 | Some(true) -> 1" "" "The match at <invalid_pattern_constructor2, 2:1-2:46>, had an invalid pattern";
  terr "invalid_constructor_arg_typ_tup" "type x = | Some of int \n Some((true, true))" "" "Got (bool, bool) instead of type int at invalid_constructor_arg_typ_tup, 2:6-2:18";
  terr "if_not_bool_cond" "if 1: 3 else: 4" "" "Got int instead of type bool";
  terr "let_type_wrong_if" "let x : bool = if true: 3 else: 4 in x" "" "Got int instead of type bool";
  terr "non_matching_branches" "if true: 3 else: !(false)" "" "Got bool instead of type int";
  t "function_ok" "def a(x: int) -> int : x \n a(4) + a(3)" "" "7";
  terr "function_bad" "def a(x: int) -> int : false \n a(4)" "" "Got bool instead of type int at function_bad, 1:23-1:28";
  terr "function_not_ok" "def a(x: bool) -> int : 3 \n a(4)" "" "Got int instead of type bool at function_not_ok";
  t "let-rec-basic-ok-2arg" "let rec add: int * int -> int = (lambda (x : int, y: int) -> int : x + y) in add(2, 3)" "" "5";
  terr "let-rec-bad-arg" "let rec add: int * int -> int = (lambda (x : int, y: int) -> int : x + y) in add(2, false)" "" "Got bool instead of type int at let-rec-bad-arg";
  terr "letnested-rec-bad-arg" "let z : bool = true in let rec add: int * int -> int = (lambda (x : int, y: int) -> int : x + y) in add(2, z)" "" 
        "Got bool instead of type int at";
  t "let-rec-basic-ok-0arg" "let rec add: int = (lambda -> int : 5) in add()" "" "5";
  terr "let-rec-0arg-if" "let rec add: int = (lambda -> int : 5) in if(add()): 4 else: 5" "" "Got int instead of type bool at let-rec-0arg-if, 1:13-1:16";
  t "let-rec-1arg-ok" "let rec self: int -> int = (lambda (x: int) -> int : x) in self(2)" "" "2";
  terr "let-rec-1arg-ok-err" "let rec self: int -> int = (lambda (x: int) -> int : x) in !(self(2))" "" "Got int instead of type bool";
  t "let-rec-2-ok" "let rec self: int -> int = (lambda (x: int) -> int : self2(x)), self2: int -> int = (lambda (x: int) -> int : self(x)) in 2" "" "2";
  terr "let-not-ok" "let self: int -> int = (lambda (x: int) -> int : self2(x)), self2: int -> int = (lambda (x: int) -> int : self(x)) in 2" "" "The identifier self2, used at";
  terr "let-rec-2-not-ok" "let rec self: int -> int = (lambda (x: int) -> int : self2(x)), self2: bool -> bool = (lambda (x: bool) -> bool : self(x)) in 2" "" 
  "Got bool instead of type int at let-rec-2-not-ok, 1:79-1:83
Got int instead of type bool at let-rec-2-not-ok, 1:39-1:42
Got int instead of type bool at let-rec-2-not-ok, 1:21-1:24
Got bool instead of type int at let-rec-2-not-ok, 1:98-1:102";
  terr "let-rec-2-not-ok" "let rec self: int -> int = (lambda (x: int) -> int : self2(x)), self2: bool -> bool = (lambda (x: bool) -> bool : self(x)) in 2" "" 
  "Got bool instead of type int at let-rec-2-not-ok, 1:79-1:83
Got int instead of type bool at let-rec-2-not-ok, 1:39-1:42
Got int instead of type bool at let-rec-2-not-ok, 1:21-1:24
Got bool instead of type int at let-rec-2-not-ok, 1:98-1:102";
  t "let-bind-scope" "let x : int = let rec self: int -> int = (lambda (x: int) -> int : self2(x)), self2: int -> int = (lambda (x: int) -> int : self(x)) in 2 in x + x" "" "4"; 
  terr "seq-type-gets-snd" "if (true; 2): 1 else: 3" "" "Got int instead of type bool at seq-type-gets-snd";
  t "seq-type-gets-snd2" "if (2; true): 1 else: 3" "" "1";
]   


let not_well_formed_patterns = [
  terr "wf-repeat_pid" "match (1, 2) with | (x, x) -> 2" "" "The identifier x, redefined at ";
  terr "wf-repeat_pid2" "match (1, 2) with | (x, x) -> 2" "" "The identifier x, redefined at ";
  terr "wf-repeat_pid3" "match (1, 2) with | (x, _, (x, p)) -> 2" "" "The identifier x, redefined at ";
  terr "wf-repeat_pconst" "match Some (1, 2) with | Some (x, x) -> x" "" "The identifier x";
  terr "wf-repeat_lower_branch" "match (1, 2) with | (x, y) -> x + y | (x, x) -> x" "" "The identifier x";
  terr "wf-repeat_deep_nest" "match (1, (2, (3, 4))) with | (x, (y, (x, z))) -> x + z" "" "The identifier x";
  t "wf-ok" "match (1, 2) with | (x, _) -> x | (_, x) -> x" "" "1";
  terr "wf-repeat_cons_bind" "match (Some (1), Some (2)) with | (Some (x), Some (x)) -> x" "" "The identifier x";
  terr "wf-tup_cons_mix" "match (1, Some (2, 3)) with | (x, Some (x, y)) -> x + y" "" "The identifier x";
  terr "wf-tup_underscore_mix" "match (1, (2, 3)) with | (x, (_, x)) -> x" "" "The identifier x";
  t "wf-ok-let" "let x : int = 4 in match (x, 2) with | (x, 2) -> x" "" "4";
]

let test_matches_and_constructors = [
  t "int_match" "match 1 with | 2 -> 100 | 1 -> 200" "" "200";
  t "true_match" "match true with | true -> 100 | false -> 200" "" "100";
  t "false_match" "match false with | true -> 100 | false -> 200" "" "200";
  t "constructor_match" "type t = | Some of int | None\n match Some(1) with | Some(x) -> x | None -> 0" "" "1";
  t "constructor_match_0_val" "type t = | Some of int | None\n match None() with | Some(x) -> x | None -> 100" "" "100";
  t "tuple_match" "match (1, 2) with | (_, a) -> a + 100 | _ -> 20" "" "102";
  t "blank_match" "match 1 with | _ -> 1 | 1 -> 2" "" "1";
  t "bind_match" "match (1, 2, 3) with | x -> x | _ -> (4, 5, 6)" "" "(1, 2, 3)";
  t "nested_tuple_match" "match (1, (2, (3, 4))) with | (a, (b, (c, d))) -> a + b + c + d | (a, (b, _)) -> a + b | _ -> 0" "" "10";
  terr "basic_branches_fail" "match 1 with | 2 -> 1" "" "Failed to match";
  t "ok_to_tuple_match" "let x : int * int = match 1 with | 1 -> (1, 1) in x" "" "(1, 1)";
  terr "bad_tuple_match" "let x : int * bool = match 1 with | 1 -> (1, 1) in x" "" "Got int instead of type bool at bad_tuple_match"; 
  (* these runs forever *)
  t "nested_constructor_match" "type t = | Some of t | None\n match Some(Some(None())) with | Some(None) -> 1 | Some(Some(None)) -> 2 | Some(Some(p)) -> 3 | Some(_) -> 4 | _ -> 5" "" "2";
  (* tprog "do_pass/complex_pattern_match_1.racer" "3"; *)
]

let final_project_tests = "final_project_tests"
  >::: []
  @ (make_naive test_parser)
  @ (make_naive test_typer_checker)
  @ (make_naive test_matches_and_constructors)
  @ (make_naive not_well_formed_patterns)

let test_test = "test_test"
  >::: (make_naive [
    (* whatever u want here for quick tests *)
    (* t "prim2_let_plus" "let x : int = 3 in 4 + x" "" "7";
    t "def1" "def x(y: int, z: int) -> int : y + z \n 2" "" "2"; *)
    ])
;;



(* each test takes 0.18 seconds on my system, this builds up so i place olds one together here *)
(* let () = run_test_tt_main pre_racer_language_tests *)

(* Integrations for do/pass and do/err *)
(* let () = run_test_tt_main integrations *)

(* racing racer tests :D *)
(* let () = run_test_tt_main racer_language_tests *)

(* For easy testing changes while working *)
(* let () = run_test_tt_main test_test *)

(* final project related unit tests *)
let () = run_test_tt_main final_project_tests

(* Requires a clean make, so we only run it every once in a while, important ones are manually tested *)
(* let () = run_test_tt_main ("integrations" >::: [input_file_test_suite ()]) *)
