(* G2 first-slice witnesses (PROTOTYPE, not in the manifest): the Sorted
   semantics (Z3SortedSemantics over Z3SortedInteger, ghost specification),
   instantiated by Z3SortedRoot over the ONE typed root carrier family, gives
   the root truth on production AST for EVERY root model i, so the
   corrected-root witnesses of Z3TypedRootTests (O1, Real order and
   division, lambda/array equality, beta, quantifiers) hold under the Sorted
   semantics too. Mutants are positively proved false. Negative controls show
   that the agreement NEEDS the root contract: over the non-root
   interpretations of Z3TypedRootTests (nullary (+)() = 1, always-false
   is-cons) the Sorted layer and the interpretation disagree. *)
module Z3SortedRootTests

open Z3AstTheory
open Z3ValueTheory
open FStar.List.Tot
open FStar.Real
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module A = Z3LinearArithmeticAst
module D = Z3Definitions
module L = FStar.List.Tot
module TR = Z3TypedRoot
module I = Z3SortedInteger
module T = Z3SortedSemantics
module SR = Z3SortedRoot
module RT = Z3TypedRootTests

(* Sorted truth over a root interpretation i (empty schema). *)
let struth (u:TR.uninterpreted) (i:TR.interp u RT.sch) (scope:list sort) (rho:RT.env u scope) (e:expr)
  : GTot bool =
  T.truth_at RT.sch (TR.booleans u) (SR.root_scalars u) i scope rho e

let bool_closed (e:expr) (scope:list sort) : prop = D.scoped scope e /\ get_sort e == bool_sort

let agree (u:TR.uninterpreted) (i:RT.model u) (scope:list sort) (rho:RT.env u scope) (e:expr)
  : Lemma (requires bool_closed e scope)
          (ensures struth u i scope rho e == RT.bool_v (RT.ev u i scope rho e)) =
  SR.lemma_truth_agreement u RT.sch i scope rho e

(* --- Real arrays: O1 under the Sorted semantics, every root model ------- *)

let sorted_o1 (u:TR.uninterpreted) (i:RT.model u) (rho:RT.env u RT.scope1)
  : Lemma (struth u i RT.scope1 rho RT.o1_half_e == true /\
           struth u i RT.scope1 rho RT.o1_third_e == false) =
  assert_norm (get_sort RT.o1_half_e == bool_sort /\ get_sort RT.o1_third_e == bool_sort);
  agree u i RT.scope1 rho RT.o1_half_e;
  agree u i RT.scope1 rho RT.o1_third_e;
  RT.o1_half u i rho;
  RT.o1_third u i rho

(* --- Real order and division ------------------------------------------- *)

let sorted_reals (u:TR.uninterpreted) (i:RT.model u) (rho:RT.env u [])
  : Lemma (struth u i [] rho RT.c_order == true /\ struth u i [] rho RT.c_div == true /\
           struth u i [] rho RT.c_half_r == true) =
  assert_norm (get_sort RT.c_order == bool_sort /\ get_sort RT.c_div == bool_sort /\
               get_sort RT.c_half_r == bool_sort);
  agree u i [] rho RT.c_order; agree u i [] rho RT.c_div; agree u i [] rho RT.c_half_r;
  RT.compare_real_third_half u i [] rho;
  RT.division_by_two u i [] rho;
  RT.forall_halving_real u i [] rho

(* --- Array (function) equality: ghost, extensional -------------------- *)

(* lambda x. x + 0 = lambda x. x is TRUE and lambda x. x = lambda x. x + 1 is
   FALSE under the Sorted ghost equality; select(lambda x. x + 1, 2) = 3. *)
let sorted_lambda_equality (u:TR.uninterpreted) (i:RT.model u) (rho:RT.env u [])
  : Lemma (struth u i [] rho RT.c_ext == true /\ struth u i [] rho RT.c_ident == false /\
           struth u i [] rho RT.c_beta == true) =
  assert_norm (get_sort RT.c_ext == bool_sort /\ get_sort RT.c_ident == bool_sort /\
               get_sort RT.c_beta == bool_sort);
  agree u i [] rho RT.c_ext; agree u i [] rho RT.c_ident; agree u i [] rho RT.c_beta;
  RT.plus_zero_is_identity u i [] rho;
  RT.identity_not_successor u i [] rho;
  RT.beta u i [] rho

(* --- Quantifiers and Int arithmetic --------------------------------------- *)

let sorted_quantifiers (u:TR.uninterpreted) (i:RT.model u) (rho:RT.env u [])
  : Lemma (struth u i [] rho RT.c_fa_pz == true /\ struth u i [] rho RT.c_half_i == false /\
           struth u i [] rho RT.c_hetero == true) =
  assert_norm (get_sort RT.c_fa_pz == bool_sort /\ get_sort RT.c_half_i == bool_sort /\
               get_sort RT.c_hetero == bool_sort);
  agree u i [] rho RT.c_fa_pz; agree u i [] rho RT.c_half_i; agree u i [] rho RT.c_hetero;
  RT.forall_plus_zero u i [] rho;
  RT.forall_halving_int_false u i [] rho;
  RT.forall_hetero u i [] rho

let sorted_arith (u:TR.uninterpreted) (i:RT.model u) (rho:RT.env u [])
  : Lemma (struth u i [] rho RT.c_arith == true) =
  assert_norm (get_sort RT.c_arith == bool_sort);
  agree u i [] rho RT.c_arith;
  RT.arith_int u i [] rho

(* --- The nullary policy is ONE policy: Sorted's runtime classifier and the
       root classifier both read nullary + / * as the empty sum / product --- *)

let nullary_classifiers ()
  : Lemma (T.classify (TR.empty_sum_decl TR.int_s) == T.Other /\
           I.classify (TR.empty_sum_decl TR.int_s) == I.Calculate A.Add /\
           I.classify (TR.empty_product_decl TR.int_s) == I.Calculate A.Mul /\
           TR.classify RT.sigma (TR.empty_sum_decl TR.int_s) == TR.Arith TR.int_s A.Add) =
  assert_norm (T.classify (TR.empty_sum_decl TR.int_s) == T.Other /\
               T.classify (TR.empty_product_decl TR.int_s) == T.Other);
  assert_norm (I.classify (TR.empty_sum_decl TR.int_s) == I.Calculate A.Add /\
               I.classify (TR.empty_product_decl TR.int_s) == I.Calculate A.Mul);
  TR.lemma_classify_empty_sum RT.sch TR.int_s

let sorted_empty_sum (u:TR.uninterpreted) (i:RT.model u)
  : Lemma (TR.int_of RT.sch (I.application RT.sch (TR.booleans u) (SR.root_integers u) i
                               (TR.empty_sum_decl TR.int_s) []) == 0) =
  nullary_classifiers ();
  SR.lemma_integer_layer u RT.sch i (TR.empty_sum_decl TR.int_s) [];
  RT.empty_int_values u i

(* --- Classifier mutants stay free in BOTH classifiers ------------------ *)

let classifier_mutants ()
  : Lemma (I.classify (RT.mk "+" op_mul [TR.int_s; TR.int_s] TR.int_s []) == I.Other /\
           TR.classify RT.sigma (RT.mk "+" op_mul [TR.int_s; TR.int_s] TR.int_s []) == TR.Other /\
           I.classify (TR.nullary_decl TR.int_s "-" op_arith_sub) == I.Other /\
           I.classify (RT.mk "+" op_plus [TR.int_s; TR.int_s; TR.int_s] TR.int_s []) == I.Other /\
           I.classify TR.native_plus_int == I.Calculate A.Add) =
  assert_norm (I.classify (RT.mk "+" op_mul [TR.int_s; TR.int_s] TR.int_s []) == I.Other);
  assert_norm (TR.classify RT.sigma (RT.mk "+" op_mul [TR.int_s; TR.int_s] TR.int_s []) == TR.Other);
  assert_norm (I.classify (TR.nullary_decl TR.int_s "-" op_arith_sub) == I.Other);
  assert_norm (I.classify (RT.mk "+" op_plus [TR.int_s; TR.int_s; TR.int_s] TR.int_s []) == I.Other);
  assert_norm (I.classify TR.native_plus_int == I.Calculate A.Add)

(* --- Negative controls: the agreement needs the root contract ---------- *)

(* Over the non-root interpretation with (+)() = 1, the Sorted integer layer
   still computes the empty sum 0, so Sorted and that interpretation DIFFER. *)
let wrong_model_disagrees (u:TR.uninterpreted) (uf:TR.symbols u RT.sch)
  : Lemma (TR.int_of RT.sch (I.application RT.sch (TR.booleans u) (SR.root_integers u) (RT.bad_empty_sum u uf)
                               (TR.empty_sum_decl TR.int_s) []) == 0 /\
           TR.int_of RT.sch ((RT.bad_empty_sum u uf).V.application (TR.empty_sum_decl TR.int_s) []) == 1 /\
           ~(TR.root_model u RT.sch (RT.bad_empty_sum u uf))) =
  nullary_classifiers ();
  RT.bad_empty_sum_not_root u uf

(* Over the non-root always-false is-cons interpretation (list schema), the
   Sorted datatype layer still says is-cons(cons 1 nil) = true. *)
let cons_one_nil_v (u:TR.uninterpreted) : TR.tvalue u RT.lsch RT.l_s =
  RT.member_facts ();
  S.constructor_value RT.lsch RT.cons_case [TR.make #u #RT.lsigma TR.int_s 1; RT.nil_v u]

(* The Sorted side: core and integer classifiers say Other, so the Sorted
   datatype layer answers from the tree. *)
let sorted_is_cons (u:TR.uninterpreted) (i:TR.interp u RT.lsch)
  : Lemma (TR.truth RT.lsch (T.application RT.lsch (TR.booleans u) (SR.root_scalars u) i
                               RT.is_cons_decl [cons_one_nil_v u]) == true) =
  RT.member_facts (); RT.recognizer_facts ();
  assert_norm (T.classify RT.is_cons_decl == T.Other /\ I.classify RT.is_cons_decl == I.Other)

let wrong_recognizer_disagrees (u:TR.uninterpreted) (uf:TR.symbols u RT.lsch)
  : Lemma (TR.truth RT.lsch ((RT.wrong_recognizer u uf).V.application RT.is_cons_decl [cons_one_nil_v u]) == false /\
           TR.truth RT.lsch (T.application RT.lsch (TR.booleans u) (SR.root_scalars u) (RT.wrong_recognizer u uf)
                               RT.is_cons_decl [cons_one_nil_v u]) == true /\
           ~(TR.root_model u RT.lsch (RT.wrong_recognizer u uf))) =
  sorted_is_cons u (RT.wrong_recognizer u uf);
  RT.wrong_recognizer_not_root u uf

(* --- Joint positive witness: ONE standard root model per (u, uf) -------- *)

let sorted_facts (u:TR.uninterpreted) (i:TR.interp u RT.sch) (rho:RT.env u []) (rho1:RT.env u RT.scope1) : prop =
  struth u i RT.scope1 rho1 RT.o1_half_e == true /\ struth u i RT.scope1 rho1 RT.o1_third_e == false /\
  struth u i [] rho RT.c_ext == true /\ struth u i [] rho RT.c_ident == false /\
  struth u i [] rho RT.c_fa_pz == true /\ struth u i [] rho RT.c_half_i == false /\
  struth u i [] rho RT.c_order == true /\ struth u i [] rho RT.c_arith == true

let standard_joint_sorted (u:TR.uninterpreted) (uf:TR.symbols u RT.sch) (rho:RT.env u []) (rho1:RT.env u RT.scope1)
  : Lemma (TR.root_model u RT.sch (TR.standard u RT.sch uf) /\ sorted_facts u (TR.standard u RT.sch uf) rho rho1) =
  TR.lemma_standard_root u RT.sch uf;
  let i : RT.model u = TR.standard u RT.sch uf in
  sorted_o1 u i rho1;
  sorted_lambda_equality u i rho;
  sorted_quantifiers u i rho;
  sorted_reals u i rho;
  sorted_arith u i rho
