(* Regression tests for finite-field rewrite checking. The positive cases are the
   rewrite steps of the QF_FF certificates in the Pulse corpus (field-2, 3, 5, 7
   and 17 cases), which the checker previously reported as unmet obligations
   because `FF<p>` terms were opaque. The negative cases show that a step which
   is not a ring identity modulo p, mixes moduli, uses a non-canonical numeral,
   or needs a unit that does not exist is still rejected. *)
module Z3FiniteFieldLemmaTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module FF = Z3FiniteFieldLemma
module TN = Z3TheoryNormalize
module L = FStar.List.Tot

let num (p n:int) : expr =
  App { decl_name = "ff"; domain = []; range = FF.ff_sort p;
        interp = Some FF.op_ff_num; int_params = [p; n] } []

let const (p:int) (name:string) : expr =
  App { decl_name = name; domain = []; range = FF.ff_sort p;
        interp = None; int_params = [] } []

let field (p:int) (name:string) (k:decl_kind) (args:list expr) : expr =
  App { decl_name = name; domain = FF.ff_domain p args; range = FF.ff_sort p;
        interp = Some k; int_params = [p] } args

let add (p:int) (args:list expr) : expr = field p "ff.add" FF.op_ff_add args
let mul (p:int) (args:list expr) : expr = field p "ff.mul" FF.op_ff_mul args
let neg (p:int) (a:expr) : expr = field p "ff.neg" FF.op_ff_neg [a]
let bitsum (p:int) (args:list expr) : expr = field p "ff.bitsum" FF.op_ff_bitsum args
let eq (a b:expr) : expr = mk_eq_expr a b

let x17 = const 17 "x"
let y17 = const 17 "y"

(* --- field-17/case-01: bitsum folding and numeral disequality --------- *)

let test_bitsum_constant_folding () : Lemma (FF.equivalent (bitsum 17 [num 17 7; num 17 2]) (num 17 11)) =
  assert_norm (FF.equivalent (bitsum 17 [num 17 7; num 17 2]) (num 17 11))

let test_numeral_disequality_is_false () : Lemma (FF.equivalent (eq (num 17 11) (num 17 2)) false_expr) =
  assert_norm (FF.equivalent (eq (num 17 11) (num 17 2)) false_expr)

let test_numeral_equality_is_true () : Lemma (FF.equivalent (eq (num 5 1) (num 5 1)) true_expr) =
  assert_norm (FF.equivalent (eq (num 5 1) (num 5 1)) true_expr)

(* --- field-2/case-01 -------------------------------------------------- *)

let test_binary_field_disequality () : Lemma (FF.equivalent (eq (num 2 1) (num 2 0)) false_expr) =
  assert_norm (FF.equivalent (eq (num 2 1) (num 2 0)) false_expr)

let test_binary_field_double_is_zero () : Lemma (FF.equivalent (eq (add 2 [const 2 "x"; const 2 "x"]) (num 2 0)) true_expr) =
  assert_norm (FF.equivalent (eq (add 2 [const 2 "x"; const 2 "x"]) (num 2 0)) true_expr)

(* --- numeral folding for add, mul and neg in several fields ---------- *)

let test_constant_folding_f5 () : Lemma (
  FF.equivalent (add 5 [num 5 3; num 5 3]) (num 5 1) /\
  FF.equivalent (mul 5 [num 5 3; num 5 4]) (num 5 2) /\
  FF.equivalent (neg 5 (num 5 1)) (num 5 4) /\
  FF.equivalent (neg 5 (num 5 4)) (num 5 1) /\
  FF.equivalent (bitsum 5 [num 5 1; num 5 2]) (num 5 0)) =
  assert_norm (
    FF.equivalent (add 5 [num 5 3; num 5 3]) (num 5 1) /\
    FF.equivalent (mul 5 [num 5 3; num 5 4]) (num 5 2) /\
    FF.equivalent (neg 5 (num 5 1)) (num 5 4) /\
    FF.equivalent (neg 5 (num 5 4)) (num 5 1) /\
    FF.equivalent (bitsum 5 [num 5 1; num 5 2]) (num 5 0))

let test_constant_folding_f7 () : Lemma (
  FF.equivalent (bitsum 7 [num 7 6; num 7 2]) (num 7 3) /\
  FF.equivalent (bitsum 7 [num 7 0; num 7 1]) (num 7 2) /\
  FF.equivalent (neg 7 (num 7 2)) (num 7 5) /\
  FF.equivalent (add 7 [num 7 6; num 7 5]) (num 7 4)) =
  assert_norm (
    FF.equivalent (bitsum 7 [num 7 6; num 7 2]) (num 7 3) /\
    FF.equivalent (bitsum 7 [num 7 0; num 7 1]) (num 7 2) /\
    FF.equivalent (neg 7 (num 7 2)) (num 7 5) /\
    FF.equivalent (add 7 [num 7 6; num 7 5]) (num 7 4))

(* --- identities with symbolic atoms (field-17, field-5, field-7) ------ *)

let test_addition_commutes () : Lemma (
  FF.equivalent (add 17 [y17; num 17 5]) (add 17 [num 17 5; y17]) /\
  FF.equivalent (add 17 [x17; y17]) (add 17 [y17; x17])) =
  assert_norm (
    FF.equivalent (add 17 [y17; num 17 5]) (add 17 [num 17 5; y17]) /\
    FF.equivalent (add 17 [x17; y17]) (add 17 [y17; x17]))

let test_negation_is_scaling () : Lemma (
  FF.equivalent (neg 17 y17) (mul 17 [num 17 16; y17]) /\
  FF.equivalent (neg 17 (add 17 [num 17 5; y17])) (mul 17 [num 17 16; add 17 [num 17 5; y17]]) /\
  FF.equivalent (neg 7 (mul 7 [num 7 6; const 7 "x"])) (const 7 "x")) =
  assert_norm (
    FF.equivalent (neg 17 y17) (mul 17 [num 17 16; y17]) /\
    FF.equivalent (neg 17 (add 17 [num 17 5; y17])) (mul 17 [num 17 16; add 17 [num 17 5; y17]]) /\
    FF.equivalent (neg 7 (mul 7 [num 7 6; const 7 "x"])) (const 7 "x"))

let test_sum_of_equal_terms () : Lemma (
  FF.equivalent (add 17 [x17; x17]) (mul 17 [num 17 2; x17])) =
  assert_norm (FF.equivalent (add 17 [x17; x17]) (mul 17 [num 17 2; x17]))

let test_multiplication_is_flattened_and_reordered () : Lemma (
  FF.equivalent (mul 5 [mul 5 [const 5 "x"; const 5 "x"]; mul 5 [num 5 4; const 5 "x"]])
                (mul 5 [num 5 4; const 5 "x"; const 5 "x"; const 5 "x"]) /\
  FF.equivalent (mul 17 [add 17 [x17; y17]; mul 17 [x17; y17]])
                (mul 17 [x17; y17; add 17 [x17; y17]])) =
  assert_norm (
    FF.equivalent (mul 5 [mul 5 [const 5 "x"; const 5 "x"]; mul 5 [num 5 4; const 5 "x"]])
                  (mul 5 [num 5 4; const 5 "x"; const 5 "x"; const 5 "x"]) /\
    FF.equivalent (mul 17 [add 17 [x17; y17]; mul 17 [x17; y17]])
                  (mul 17 [x17; y17; add 17 [x17; y17]]))

let test_neutral_and_absorbing_numerals () : Lemma (
  FF.equivalent (add 7 [num 7 0; const 7 "y"]) (const 7 "y") /\
  FF.equivalent (mul 7 [const 7 "y"; num 7 0]) (num 7 0) /\
  FF.equivalent (mul 7 [mul 7 [num 7 6; const 7 "x"]; num 7 1]) (mul 7 [num 7 6; const 7 "x"]) /\
  FF.equivalent (mul 5 [num 5 4; num 5 0]) (num 5 0)) =
  assert_norm (
    FF.equivalent (add 7 [num 7 0; const 7 "y"]) (const 7 "y") /\
    FF.equivalent (mul 7 [const 7 "y"; num 7 0]) (num 7 0) /\
    FF.equivalent (mul 7 [mul 7 [num 7 6; const 7 "x"]; num 7 1]) (mul 7 [num 7 6; const 7 "x"]) /\
    FF.equivalent (mul 5 [num 5 4; num 5 0]) (num 5 0))

(* A conditional term is an opaque atom, but its position in a sum is irrelevant. *)
let ite17 : expr =
  App (Z3ArrayRewrite.term_ite_decl (FF.ff_sort 17)) [eq x17 y17; y17; num 17 0]

let test_conditional_atoms_commute () : Lemma (
  FF.equivalent (add 17 [ite17; mul 17 [num 17 2; x17]])
                (add 17 [mul 17 [num 17 2; x17]; ite17])) =
  assert_norm (
    FF.equivalent (add 17 [ite17; mul 17 [num 17 2; x17]])
                  (add 17 [mul 17 [num 17 2; x17]; ite17]))

(* --- equalities whose difference is cancelled or rescaled by a unit --- *)

(* field-17/case-04: the y terms cancel and 16 * 5 = 12 is a nonzero constant. *)
let test_cancellation_to_false () : Lemma (
  FF.equivalent (eq (mul 17 [num 17 16; add 17 [num 17 5; y17]]) (mul 17 [num 17 16; y17])) false_expr) =
  assert_norm (
    FF.equivalent (eq (mul 17 [num 17 16; add 17 [num 17 5; y17]]) (mul 17 [num 17 16; y17])) false_expr)

(* field-17/case-02: isolating y; the difference polynomials differ by the unit -1. *)
let test_isolating_a_variable () : Lemma (
  FF.equivalent
    (eq (add 17 [num 17 8; bitsum 17 [x17; num 17 2]]) (add 17 [mul 17 [num 17 6; x17]; y17]))
    (eq y17 (add 17 [num 17 8; mul 17 [num 17 11; x17]; bitsum 17 [x17; num 17 2]]))) =
  assert_norm (
    FF.equivalent
      (eq (add 17 [num 17 8; bitsum 17 [x17; num 17 2]]) (add 17 [mul 17 [num 17 6; x17]; y17]))
      (eq y17 (add 17 [num 17 8; mul 17 [num 17 11; x17]; bitsum 17 [x17; num 17 2]])))

(* field-17/case-05: dividing by the leading coefficient 12 (a unit modulo 17). *)
let test_rescaling_by_a_unit () : Lemma (
  FF.equivalent
    (eq (mul 17 [num 17 12; y17; add 17 [num 17 12; y17]]) (num 17 8))
    (eq (mul 17 [y17; add 17 [num 17 12; y17]]) (num 17 12))) =
  assert_norm (
    FF.equivalent
      (eq (mul 17 [num 17 12; y17; add 17 [num 17 12; y17]]) (num 17 8))
      (eq (mul 17 [y17; add 17 [num 17 12; y17]]) (num 17 12)))

(* field-3/case-02 and field-7/case-05: y = 2*y iff y = 0, and x = 6*x iff x = 0. *)
let test_rescaling_to_zero_equation () : Lemma (
  FF.equivalent (eq (const 3 "y") (mul 3 [num 3 2; const 3 "y"])) (eq (const 3 "y") (num 3 0)) /\
  FF.equivalent (eq (const 7 "x") (mul 7 [num 7 6; const 7 "x"])) (eq (const 7 "x") (num 7 0))) =
  assert_norm (
    FF.equivalent (eq (const 3 "y") (mul 3 [num 3 2; const 3 "y"])) (eq (const 3 "y") (num 3 0)) /\
    FF.equivalent (eq (const 7 "x") (mul 7 [num 7 6; const 7 "x"])) (eq (const 7 "x") (num 7 0)))

(* field-5/case-04: 3 = 4*x^3 iff x^3 = 2. *)
let test_cubic_equation () : Lemma (
  FF.equivalent (eq (num 5 3) (mul 5 [num 5 4; const 5 "x"; const 5 "x"; const 5 "x"]))
                (eq (mul 5 [const 5 "x"; const 5 "x"; const 5 "x"]) (num 5 2))) =
  assert_norm (
    FF.equivalent (eq (num 5 3) (mul 5 [num 5 4; const 5 "x"; const 5 "x"; const 5 "x"]))
                  (eq (mul 5 [const 5 "x"; const 5 "x"; const 5 "x"]) (num 5 2)))

(* The full normalizing entry point used by rewrite steps also accepts them. *)
let test_normalizing_entry_point () : Lemma (
  TN.equivalent (bitsum 17 [num 17 7; num 17 2]) (num 17 11) /\
  TN.equivalent (eq (num 17 11) (num 17 2)) false_expr /\
  TN.equivalent (add 17 [y17; num 17 5]) (add 17 [num 17 5; y17]) /\
  TN.equivalent (eq (mul 17 [num 17 12; y17; add 17 [num 17 12; y17]]) (num 17 8))
                (eq (mul 17 [y17; add 17 [num 17 12; y17]]) (num 17 12))) =
  assert_norm (
    TN.equivalent (bitsum 17 [num 17 7; num 17 2]) (num 17 11) /\
    TN.equivalent (eq (num 17 11) (num 17 2)) false_expr /\
    TN.equivalent (add 17 [y17; num 17 5]) (add 17 [num 17 5; y17]) /\
    TN.equivalent (eq (mul 17 [num 17 12; y17; add 17 [num 17 12; y17]]) (num 17 8))
                  (eq (mul 17 [y17; add 17 [num 17 12; y17]]) (num 17 12)))

(* ------------------------------------------------------------------ *)
(* Rejections                                                          *)
(* ------------------------------------------------------------------ *)

(* Different polynomials are not equivalent, whatever the field. *)
let test_distinct_polynomials_are_rejected () : Lemma (
  not (FF.equivalent (add 17 [x17; num 17 1]) (add 17 [x17; num 17 2])) /\
  not (FF.equivalent (add 17 [x17; y17]) (add 17 [x17; const 17 "z"])) /\
  not (FF.equivalent (mul 17 [x17; x17]) x17)) =
  assert_norm (
    not (FF.equivalent (add 17 [x17; num 17 1]) (add 17 [x17; num 17 2])) /\
    not (FF.equivalent (add 17 [x17; y17]) (add 17 [x17; const 17 "z"])) /\
    not (FF.equivalent (mul 17 [x17; x17]) x17))

(* x*x = x holds for every element of F_2 but follows only from the field equation,
   which needs primality; the checker does not derive it. *)
let test_field_equation_is_not_assumed () : Lemma (
  not (FF.equivalent (mul 2 [const 2 "x"; const 2 "x"]) (const 2 "x")) /\
  not (FF.equivalent (eq (mul 5 [const 5 "x"; const 5 "x"; const 5 "x"; const 5 "x"; const 5 "x"]) (const 5 "x")) true_expr)) =
  assert_norm (
    not (FF.equivalent (mul 2 [const 2 "x"; const 2 "x"]) (const 2 "x")) /\
    not (FF.equivalent (eq (mul 5 [const 5 "x"; const 5 "x"; const 5 "x"; const 5 "x"; const 5 "x"]) (const 5 "x")) true_expr))

let test_equalities_are_not_forced () : Lemma (
  not (FF.equivalent (eq x17 (num 17 0)) true_expr) /\
  not (FF.equivalent (eq x17 (num 17 0)) false_expr) /\
  not (FF.equivalent (eq (num 17 3) (num 17 3)) false_expr) /\
  not (FF.equivalent (eq (num 17 3) (num 17 4)) true_expr)) =
  assert_norm (
    not (FF.equivalent (eq x17 (num 17 0)) true_expr) /\
    not (FF.equivalent (eq x17 (num 17 0)) false_expr) /\
    not (FF.equivalent (eq (num 17 3) (num 17 3)) false_expr) /\
    not (FF.equivalent (eq (num 17 3) (num 17 4)) true_expr))

(* A rescaling that is not a multiplication by a unit is rejected. *)
let test_non_proportional_equations_are_rejected () : Lemma (
  not (FF.equivalent (eq (mul 17 [num 17 2; x17]) (num 17 1)) (eq x17 (num 17 1))) /\
  not (FF.equivalent (eq (add 17 [x17; num 17 1]) (num 17 0)) (eq (add 17 [x17; num 17 2]) (num 17 0)))) =
  assert_norm (
    not (FF.equivalent (eq (mul 17 [num 17 2; x17]) (num 17 1)) (eq x17 (num 17 1))) /\
    not (FF.equivalent (eq (add 17 [x17; num 17 1]) (num 17 0)) (eq (add 17 [x17; num 17 2]) (num 17 0))))

(* Modulo 4 the element 2 has no inverse, so 2*x = 0 does not imply x = 0.
   Nothing in the checker assumes that the modulus is prime. *)
let test_non_unit_rescaling_is_rejected () : Lemma (
  not (FF.equivalent (eq (mul 4 [num 4 2; const 4 "x"]) (num 4 0)) (eq (const 4 "x") (num 4 0))) /\
  not (FF.equivalent (eq (const 4 "x") (num 4 0)) (eq (mul 4 [num 4 2; const 4 "x"]) (num 4 0))) /\
  FF.equivalent (eq (mul 3 [num 3 2; const 3 "x"]) (num 3 0)) (eq (const 3 "x") (num 3 0))) =
  assert_norm (
    not (FF.equivalent (eq (mul 4 [num 4 2; const 4 "x"]) (num 4 0)) (eq (const 4 "x") (num 4 0))) /\
    not (FF.equivalent (eq (const 4 "x") (num 4 0)) (eq (mul 4 [num 4 2; const 4 "x"]) (num 4 0))) /\
    FF.equivalent (eq (mul 3 [num 3 2; const 3 "x"]) (num 3 0)) (eq (const 3 "x") (num 3 0)))

(* Numerals must be canonical residues of a modulus of at least 2. *)
let test_malformed_numerals_are_rejected () : Lemma (
  FF.numeral (num 17 16) == Some (17, 16) /\
  FF.numeral (num 17 17) == None /\
  FF.numeral (num 17 (-1)) == None /\
  FF.numeral (num 1 0) == None /\
  FF.numeral (num 0 0) == None /\
  FF.numeral (num (-7) 0) == None /\
  not (FF.equivalent (num 17 17) (num 17 0)) /\
  not (FF.equivalent (eq (num 17 17) (num 17 0)) true_expr) /\
  not (FF.equivalent (eq (num 1 0) (num 1 0)) true_expr)) =
  assert_norm (
    FF.numeral (num 17 16) == Some (17, 16) /\
    FF.numeral (num 17 17) == None /\
    FF.numeral (num 17 (-1)) == None /\
    FF.numeral (num 1 0) == None /\
    FF.numeral (num 0 0) == None /\
    FF.numeral (num (-7) 0) == None /\
    not (FF.equivalent (num 17 17) (num 17 0)) /\
    not (FF.equivalent (eq (num 17 17) (num 17 0)) true_expr) /\
    not (FF.equivalent (eq (num 1 0) (num 1 0)) true_expr))

(* A numeral whose declared sort names another modulus is not a numeral. *)
let wrong_sort_numeral : expr =
  App { decl_name = "ff"; domain = []; range = FF.ff_sort 19;
        interp = Some FF.op_ff_num; int_params = [17; 3] } []

let test_modulus_mismatch_is_rejected () : Lemma (
  FF.numeral wrong_sort_numeral == None /\
  not (FF.equivalent (add 17 [num 17 3; num 17 4]) (num 17 8)) /\
  not (FF.equivalent (add 17 [num 17 3; num 19 4]) (num 17 7)) /\
  not (FF.equivalent (eq (num 17 3) (num 19 3)) true_expr) /\
  not (FF.equivalent (eq wrong_sort_numeral (num 17 3)) true_expr)) =
  assert_norm (
    FF.numeral wrong_sort_numeral == None /\
    not (FF.equivalent (add 17 [num 17 3; num 17 4]) (num 17 8)) /\
    not (FF.equivalent (add 17 [num 17 3; num 19 4]) (num 17 7)) /\
    not (FF.equivalent (eq (num 17 3) (num 19 3)) true_expr) /\
    not (FF.equivalent (eq wrong_sort_numeral (num 17 3)) true_expr))

(* An operation whose declaration or arguments do not carry the same modulus is opaque. *)
let mixed_sum : expr =
  App { decl_name = "ff.add"; domain = [FF.ff_sort 17; FF.ff_sort 19];
        range = FF.ff_sort 17; interp = Some FF.op_ff_add; int_params = [17] }
      [num 17 1; num 19 1]

let wrong_arity_negation : expr =
  App { decl_name = "ff.neg"; domain = [FF.ff_sort 17; FF.ff_sort 17];
        range = FF.ff_sort 17; interp = Some FF.op_ff_neg; int_params = [17] }
      [num 17 1; num 17 2]

let unary_sum : expr =
  App { decl_name = "ff.add"; domain = [FF.ff_sort 17];
        range = FF.ff_sort 17; interp = Some FF.op_ff_add; int_params = [17] }
      [num 17 1]

let test_ill_formed_operations_are_opaque () : Lemma (
  FF.operation (App?.decl mixed_sum) (App?.args mixed_sum) == None /\
  FF.operation (App?.decl wrong_arity_negation) (App?.args wrong_arity_negation) == None /\
  FF.operation (App?.decl unary_sum) (App?.args unary_sum) == None /\
  not (FF.equivalent mixed_sum (num 17 2)) /\
  not (FF.equivalent wrong_arity_negation (num 17 16)) /\
  not (FF.equivalent unary_sum (num 17 1))) =
  assert_norm (
    FF.operation (App?.decl mixed_sum) (App?.args mixed_sum) == None /\
    FF.operation (App?.decl wrong_arity_negation) (App?.args wrong_arity_negation) == None /\
    FF.operation (App?.decl unary_sum) (App?.args unary_sum) == None /\
    not (FF.equivalent mixed_sum (num 17 2)) /\
    not (FF.equivalent wrong_arity_negation (num 17 16)) /\
    not (FF.equivalent unary_sum (num 17 1)))

(* Terms that are not finite-field terms never reach the polynomial procedure. *)
let test_other_sorts_are_ignored () : Lemma (
  not (FF.equivalent true_expr false_expr) /\
  not (FF.equivalent (Var 0 (FF.ff_sort 17)) (num 17 0)) /\
  not (FF.equivalent (eq (Var 0 (FF.ff_sort 17)) (num 17 0)) true_expr)) =
  assert_norm (
    not (FF.equivalent true_expr false_expr) /\
    not (FF.equivalent (Var 0 (FF.ff_sort 17)) (num 17 0)) /\
    not (FF.equivalent (eq (Var 0 (FF.ff_sort 17)) (num 17 0)) true_expr))

(* The entry point used by rewrite steps rejects wrong constant folding too. *)
let test_normalizing_entry_point_rejects () : Lemma (
  not (TN.equivalent (bitsum 17 [num 17 7; num 17 2]) (num 17 12)) /\
  not (TN.equivalent (eq (num 17 11) (num 17 11)) false_expr) /\
  not (TN.equivalent (add 17 [y17; num 17 5]) (add 17 [num 17 6; y17]))) =
  assert_norm (
    not (TN.equivalent (bitsum 17 [num 17 7; num 17 2]) (num 17 12)) /\
    not (TN.equivalent (eq (num 17 11) (num 17 11)) false_expr) /\
    not (TN.equivalent (add 17 [y17; num 17 5]) (add 17 [num 17 6; y17])))
