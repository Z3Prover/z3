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

(* --- a conditional term compared with a numeral ----------------------- *)

let ite_term (p:int) (c t e:expr) : expr =
  App (Z3ArrayRewrite.term_ite_decl (FF.ff_sort p)) [c; t; e]

let conj (a b:expr) : expr =
  App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Conjunction [a; b]) [a; b]

let x3 = const 3 "x"
let y3 = const 3 "y"
let x7 = const 7 "x"
let y7 = const 7 "y"
let same3 = eq x3 y3
let same7 = eq y7 x7
let double_y3 = bitsum 3 [y3; y3]
let z3 = const 3 "z"

(* field-3/case-02: the then branch 2 differs from 1, so only the else branch can be 1.
   (Here `ff.bitsum y y` is 3*y = 0 in F_3, so the else branch is decided as well; the
   rule needs only the then branch.) *)
let else_live : expr = eq (ite_term 3 same3 (num 3 2) double_y3) (num 3 1)
let else_live_result : expr = conj (eq double_y3 (num 3 1)) (mk_not_expr same3)

(* field-7/case-01: neither branch (5 and 1) is 3. *)
let both_dead : expr = eq (ite_term 7 same7 (num 7 5) (num 7 1)) (num 7 3)
let both_dead_result : expr = conj false_expr same7

(* Branches that really are symbolic: only the else branch, respectively only the then
   branch, can be 1. *)
let live_eq : expr = eq y3 (num 3 1)
let else_y : expr = eq (ite_term 3 same3 (num 3 2) y3) (num 3 1)
let else_y_result : expr = conj live_eq (mk_not_expr same3)
let then_live : expr = eq (ite_term 3 same3 y3 (num 3 2)) (num 3 1)
let then_live_result : expr = conj live_eq same3

let test_ite_equal_numeral_else_branch () : Lemma (
  FF.equivalent else_live else_live_result /\ TN.equivalent else_live else_live_result) =
  assert_norm (FF.equivalent else_live else_live_result /\ TN.equivalent else_live else_live_result)

let test_ite_equal_numeral_symbolic_else_branch () : Lemma (
  FF.equivalent else_y else_y_result /\ TN.equivalent else_y else_y_result) =
  assert_norm (FF.equivalent else_y else_y_result /\ TN.equivalent else_y else_y_result)

let test_ite_equal_numeral_no_branch () : Lemma (
  FF.equivalent both_dead both_dead_result /\ TN.equivalent both_dead both_dead_result) =
  assert_norm (FF.equivalent both_dead both_dead_result /\ TN.equivalent both_dead both_dead_result)

let test_ite_equal_numeral_then_branch () : Lemma (
  FF.equivalent then_live then_live_result /\ TN.equivalent then_live then_live_result) =
  assert_norm (FF.equivalent then_live then_live_result /\ TN.equivalent then_live then_live_result)

(* The surviving branch may be stated as any equality with a unit-proportional
   difference: 2*y = 0 iff y = 0 in F_3. *)
let test_ite_equal_numeral_rescaled_branch () : Lemma (
  FF.equivalent (eq (ite_term 3 same3 (num 3 2) (mul 3 [num 3 2; y3])) (num 3 0))
                (conj (eq y3 (num 3 0)) (mk_not_expr same3))) =
  assert_norm (
    FF.equivalent (eq (ite_term 3 same3 (num 3 2) (mul 3 [num 3 2; y3])) (num 3 0))
                  (conj (eq y3 (num 3 0)) (mk_not_expr same3)))

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

(* ------------------------------------------------------------------ *)
(* Rejections for a conditional term compared with a numeral           *)
(* ------------------------------------------------------------------ *)

(* The surviving branch is paired with the condition that selects it. *)
let test_ite_equal_numeral_wrong_polarity_is_rejected () : Lemma (
  not (FF.equivalent else_y (conj live_eq same3)) /\
  not (FF.equivalent then_live (conj live_eq (mk_not_expr same3))) /\
  not (TN.equivalent else_y (conj live_eq same3))) =
  assert_norm (
    not (FF.equivalent else_y (conj live_eq same3)) /\
    not (FF.equivalent then_live (conj live_eq (mk_not_expr same3))) /\
    not (TN.equivalent else_y (conj live_eq same3)))

(* A conclusion that is not the equality of the surviving branch is rejected, as
   are conjunctions that are not binary. *)
let test_ite_equal_numeral_false_conclusions_are_rejected () : Lemma (
  not (FF.equivalent else_y false_expr) /\
  not (FF.equivalent else_y true_expr) /\
  not (FF.equivalent else_y (mk_not_expr same3)) /\
  not (FF.equivalent else_y (conj false_expr (mk_not_expr same3))) /\
  not (FF.equivalent else_y (conj (eq y3 (num 3 2)) (mk_not_expr same3))) /\
  not (FF.equivalent else_y (conj (eq z3 (num 3 1)) (mk_not_expr same3))) /\
  not (FF.equivalent else_y
         (App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Conjunction [live_eq; mk_not_expr same3; true_expr])
              [live_eq; mk_not_expr same3; true_expr])) /\
  not (FF.equivalent both_dead (conj true_expr same7)) /\
  not (FF.equivalent both_dead (mk_not_expr same7)) /\
  not (TN.equivalent else_y (conj false_expr (mk_not_expr same3)))) =
  assert_norm (
    not (FF.equivalent else_y false_expr) /\
    not (FF.equivalent else_y true_expr) /\
    not (FF.equivalent else_y (mk_not_expr same3)) /\
    not (FF.equivalent else_y (conj false_expr (mk_not_expr same3))) /\
    not (FF.equivalent else_y (conj (eq y3 (num 3 2)) (mk_not_expr same3))) /\
    not (FF.equivalent else_y (conj (eq z3 (num 3 1)) (mk_not_expr same3))) /\
    not (FF.equivalent else_y
           (App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Conjunction [live_eq; mk_not_expr same3; true_expr])
                [live_eq; mk_not_expr same3; true_expr])) /\
    not (FF.equivalent both_dead (conj true_expr same7)) /\
    not (FF.equivalent both_dead (mk_not_expr same7)) /\
    not (TN.equivalent else_y (conj false_expr (mk_not_expr same3))))

(* The condition of the conclusion must be the condition of the conditional term. *)
let test_ite_equal_numeral_condition_mismatch_is_rejected () : Lemma (
  not (FF.equivalent else_y (conj live_eq (mk_not_expr (eq y3 x3)))) /\
  not (FF.equivalent else_y (conj live_eq (mk_not_expr (eq x3 x3)))) /\
  not (FF.equivalent else_y (conj live_eq (mk_not_expr true_expr))) /\
  not (FF.equivalent then_live (conj live_eq (eq y3 x3))) /\
  not (FF.equivalent both_dead (conj false_expr (eq x7 x7))) /\
  not (TN.equivalent else_y (conj live_eq (mk_not_expr (eq y3 x3))))) =
  assert_norm (
    not (FF.equivalent else_y (conj live_eq (mk_not_expr (eq y3 x3)))) /\
    not (FF.equivalent else_y (conj live_eq (mk_not_expr (eq x3 x3)))) /\
    not (FF.equivalent else_y (conj live_eq (mk_not_expr true_expr))) /\
    not (FF.equivalent then_live (conj live_eq (eq y3 x3))) /\
    not (FF.equivalent both_dead (conj false_expr (eq x7 x7))) /\
    not (TN.equivalent else_y (conj live_eq (mk_not_expr (eq y3 x3)))))

(* The condition is never assumed: the equality of the surviving branch alone, or paired
   with a trivial conjunct instead of the condition, is not the conditional term. *)
let test_ite_equal_numeral_condition_is_never_assumed () : Lemma (
  not (FF.equivalent else_y live_eq) /\
  not (FF.equivalent then_live live_eq) /\
  not (FF.equivalent both_dead same7) /\
  not (FF.equivalent else_y (conj live_eq true_expr)) /\
  not (FF.equivalent then_live (conj true_expr live_eq)) /\
  not (FF.equivalent else_y (conj live_eq live_eq)) /\
  not (TN.equivalent else_y live_eq) /\
  not (TN.equivalent else_y (conj live_eq true_expr))) =
  assert_norm (
    not (FF.equivalent else_y live_eq) /\
    not (FF.equivalent then_live live_eq) /\
    not (FF.equivalent both_dead same7) /\
    not (FF.equivalent else_y (conj live_eq true_expr)) /\
    not (FF.equivalent then_live (conj true_expr live_eq)) /\
    not (FF.equivalent else_y (conj live_eq live_eq)) /\
    not (TN.equivalent else_y live_eq) /\
    not (TN.equivalent else_y (conj live_eq true_expr)))

(* A branch is dropped only when it is a constant different from the numeral: a
   branch equal to the numeral, or a symbolic branch, stays. *)
let test_ite_equal_numeral_undecided_branch_is_rejected () : Lemma (
  not (FF.equivalent (eq (ite_term 3 same3 (num 3 1) y3) (num 3 1))
                     (conj live_eq (mk_not_expr same3))) /\
  not (FF.equivalent (eq (ite_term 3 same3 (num 3 1) y3) (num 3 1))
                     (conj live_eq same3)) /\
  not (FF.equivalent (eq (ite_term 3 same3 (num 3 1) (num 3 1)) (num 3 1)) (conj false_expr same3)) /\
  not (FF.equivalent (eq (ite_term 3 same3 (num 3 1) (num 3 1)) (num 3 1)) (conj false_expr (mk_not_expr same3))) /\
  not (FF.equivalent (eq (ite_term 3 same3 x3 y3) (num 3 1)) (conj live_eq (mk_not_expr same3))) /\
  not (FF.equivalent (eq (ite_term 3 same3 double_y3 y3) (num 3 1)) (conj false_expr same3)) /\
  not (TN.equivalent (eq (ite_term 3 same3 (num 3 1) y3) (num 3 1))
                     (conj live_eq (mk_not_expr same3)))) =
  assert_norm (
    not (FF.equivalent (eq (ite_term 3 same3 (num 3 1) y3) (num 3 1))
                       (conj live_eq (mk_not_expr same3))) /\
    not (FF.equivalent (eq (ite_term 3 same3 (num 3 1) y3) (num 3 1))
                       (conj live_eq same3)) /\
    not (FF.equivalent (eq (ite_term 3 same3 (num 3 1) (num 3 1)) (num 3 1)) (conj false_expr same3)) /\
    not (FF.equivalent (eq (ite_term 3 same3 (num 3 1) (num 3 1)) (num 3 1)) (conj false_expr (mk_not_expr same3))) /\
    not (FF.equivalent (eq (ite_term 3 same3 x3 y3) (num 3 1)) (conj live_eq (mk_not_expr same3))) /\
    not (FF.equivalent (eq (ite_term 3 same3 double_y3 y3) (num 3 1)) (conj false_expr same3)) /\
    not (TN.equivalent (eq (ite_term 3 same3 (num 3 1) y3) (num 3 1))
                       (conj live_eq (mk_not_expr same3))))

(* Ill-typed terms: a condition that is not Boolean, branches of different sorts,
   a numeral of another modulus, and a conditional term over another sort. *)
let ill_typed_condition : expr = eq (ite_term 3 x3 (num 3 2) y3) (num 3 1)
let mixed_branches : expr =
  eq (App (Z3ArrayRewrite.term_ite_decl (FF.ff_sort 3)) [same3; num 3 2; num 5 1]) (num 3 1)
let mixed_numeral : expr = eq (ite_term 3 same3 (num 3 2) y3) (num 5 1)
let int_sort : sort = BaseSort "Int"
let int_const (name:string) : expr =
  App { decl_name = name; domain = []; range = int_sort; interp = None; int_params = [] } []
let int_ite : expr =
  eq (App { decl_name = "if"; domain = [bool_sort; int_sort; int_sort]; range = int_sort;
            interp = Some op_ite; int_params = [] }
         [same3; int_const "a"; int_const "b"]) (int_const "k")

let test_ite_equal_numeral_ill_typed_is_rejected () : Lemma (
  not (FF.equivalent ill_typed_condition (conj live_eq (mk_not_expr x3))) /\
  not (FF.equivalent ill_typed_condition (conj live_eq x3)) /\
  not (FF.equivalent mixed_branches (conj (eq (num 5 1) (num 3 1)) (mk_not_expr same3))) /\
  not (FF.equivalent mixed_branches (conj false_expr same3)) /\
  not (FF.equivalent mixed_numeral (conj live_eq (mk_not_expr same3))) /\
  not (FF.equivalent mixed_numeral (conj (eq y3 (num 5 1)) (mk_not_expr same3))) /\
  not (FF.equivalent int_ite (conj (eq (int_const "b") (int_const "k")) (mk_not_expr same3))) /\
  not (FF.equivalent else_y (conj (eq y3 wrong_sort_numeral) (mk_not_expr same3))) /\
  not (TN.equivalent ill_typed_condition (conj live_eq (mk_not_expr x3)))) =
  assert_norm (
    not (FF.equivalent ill_typed_condition (conj live_eq (mk_not_expr x3))) /\
    not (FF.equivalent ill_typed_condition (conj live_eq x3)) /\
    not (FF.equivalent mixed_branches (conj (eq (num 5 1) (num 3 1)) (mk_not_expr same3))) /\
    not (FF.equivalent mixed_branches (conj false_expr same3)) /\
    not (FF.equivalent mixed_numeral (conj live_eq (mk_not_expr same3))) /\
    not (FF.equivalent mixed_numeral (conj (eq y3 (num 5 1)) (mk_not_expr same3))) /\
    not (FF.equivalent int_ite (conj (eq (int_const "b") (int_const "k")) (mk_not_expr same3))) /\
    not (FF.equivalent else_y (conj (eq y3 wrong_sort_numeral) (mk_not_expr same3))) /\
    not (TN.equivalent ill_typed_condition (conj live_eq (mk_not_expr x3))))

(* Modulo 4 the element 2 has no inverse: the branch 2 is still different from 0 by a
   nonzero constant, but 2*y = 0 is not rewritten to y = 0. *)
let test_ite_equal_numeral_uses_no_unit () : Lemma (
  (let c = eq (const 4 "x") (const 4 "y") in
   let y = const 4 "y" in
   let a = eq (ite_term 4 c (num 4 2) (mul 4 [num 4 2; y])) (num 4 0) in
   FF.equivalent a (conj (eq (mul 4 [num 4 2; y]) (num 4 0)) (mk_not_expr c)) /\
   not (FF.equivalent a (conj (eq y (num 4 0)) (mk_not_expr c))))) =
  assert_norm (
    (let c = eq (const 4 "x") (const 4 "y") in
     let y = const 4 "y" in
     let a = eq (ite_term 4 c (num 4 2) (mul 4 [num 4 2; y])) (num 4 0) in
     FF.equivalent a (conj (eq (mul 4 [num 4 2; y]) (num 4 0)) (mk_not_expr c)) /\
     not (FF.equivalent a (conj (eq y (num 4 0)) (mk_not_expr c)))))
