module Z3IndependentFiniteFieldReplay

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module FF = Z3SortedFiniteField
module D = Z3ExprScope
module R = Z3ClauseSyntax
module Witness = Z3IndependentFiniteFieldWitness
module E = FStar.Math.Euclid

let rewrite (p:int) (a b:expr) : bool =
  p >= 2 && D.scoped [] a && D.scoped [] b && get_sort a = get_sort b &&
  FF.equivalent a b &&
  (not (FF.term_equivalent a b) || FF.shared_modulus a b = Some p) &&
  (not (FF.eq_truth_equivalent a b) || FF.atom_modulus a = Some p) &&
  (not (FF.eq_truth_equivalent b a) || FF.atom_modulus b = Some p) &&
  (not (FF.eq_eq_equivalent a b) ||
   (match FF.atom_modulus a with Some q -> q = p | None -> FF.atom_modulus b = Some p)) &&
  (not (FF.ite_eq_equivalent a b) || FF.ite_eq_sound_at_modulus p a b)

let clause (p:int) (e:expr) : bool =
  FF.find_modulus e = Some p && FF.exhaustive_clause e

let pac_with_evidence (p:int) (c:FF.certificate) (e:expr)
                      (evidence:option (int & list int)) : bool =
  p >= 2 && FF.find_modulus_args c.pac_premises = Some p &&
  D.scoped_args [] c.pac_premises && D.scoped [] e &&
  get_sort e = bool_sort && (FF.check c e || Witness.check_with_evidence c e evidence)

let pac_for_prime (p:int{E.is_prime p}) (c:FF.certificate) (e:expr) : bool =
  FF.find_modulus_args c.pac_premises = Some p &&
  D.scoped_args [] c.pac_premises && D.scoped [] e &&
  get_sort e = bool_sort && (FF.check c e || Witness.check_for_prime p c e)

let pac (p:int) (c:FF.certificate) (e:expr) : bool =
  pac_with_evidence p c e None

let lemma_rewrite (#base:sort -> Type0) (s:S.checked_schema) (p:pos)
                  (m:FF.model base s p) (a b:expr)
  : Lemma (requires rewrite p a b)
          (ensures T.truth s m.FF.booleans m.FF.scalar_model (FF.override s p m) (R.mk_eq_expr a b)) =
  FF.lemma_equivalent_sound s p m (T.empty_environment (S.signature s)) a b;
  T.lemma_equality s m.FF.booleans m.FF.scalar_model (FF.override s p m) a b

let lemma_clause (#base:sort -> Type0) (s:S.checked_schema) (p:pos)
                 (m:FF.model base s p) (e:expr)
  : Lemma (requires clause p e)
          (ensures T.truth s m.FF.booleans m.FF.scalar_model (FF.override s p m) e) =
  FF.lemma_exhaustive_clause_sound s p m (T.empty_environment (S.signature s)) e

let lemma_pac_with_evidence (#base:sort -> Type0) (s:S.checked_schema) (p:pos)
              (m:FF.model base s p) (c:FF.certificate) (e:expr)
              (evidence:option (int & list int))
  : Lemma (requires pac_with_evidence p c e evidence)
          (ensures T.truth s m.FF.booleans m.FF.scalar_model (FF.override s p m) e) =
  if FF.check c e then FF.lemma_check_sound s p m c e
  else Witness.lemma_check_with_evidence_sound s p m c e evidence

let lemma_pac_for_prime (#base:sort -> Type0) (s:S.checked_schema) (p:int{E.is_prime p})
              (m:FF.model base s p) (c:FF.certificate) (e:expr)
  : Lemma (requires pac_for_prime p c e)
          (ensures T.truth s m.FF.booleans m.FF.scalar_model (FF.override s p m) e) =
  if FF.check c e then FF.lemma_check_sound s p m c e
  else Witness.lemma_check_for_prime_sound s p m c e

let lemma_pac (#base:sort -> Type0) (s:S.checked_schema) (p:pos)
              (m:FF.model base s p) (c:FF.certificate) (e:expr)
  : Lemma (requires pac p c e)
          (ensures T.truth s m.FF.booleans m.FF.scalar_model (FF.override s p m) e) =
  lemma_pac_with_evidence s p m c e None

let test_sort = FF.ff_sort 5
let test_number (n:int) : expr =
  App { decl_name = "ff"; domain = []; range = test_sort;
        interp = Some FF.op_ff_num; int_params = [5; n] } []
let test_x : expr =
  App { decl_name = "x"; domain = []; range = test_sort;
        interp = None; int_params = [] } []
let test_add (a b:expr) : expr =
  App { decl_name = "ff.add"; domain = [test_sort; test_sort]; range = test_sort;
        interp = Some FF.op_ff_add; int_params = [5] } [a; b]

let lemma_replay_controls ()
  : Lemma (rewrite 5 (test_add test_x (test_number 0)) test_x /\
           not (rewrite 5 (test_add test_x (test_number 1)) test_x) /\
           not (rewrite 7 (test_add test_x (test_number 0)) test_x) /\
           not (rewrite 1 test_x test_x) /\
           not (rewrite 5 (test_add (Var 0 test_sort) (test_number 0)) (Var 0 test_sort)) /\
           clause 5 (R.mk_eq_expr (test_add test_x (test_number 0)) test_x) /\
           not (clause 5 (R.mk_eq_expr test_x (test_number 0))) /\
           not (clause 5 (R.mk_eq_expr (test_add (Var 0 test_sort) (test_number 0)) (Var 0 test_sort))) /\
           not (clause 7 (R.mk_eq_expr (test_add test_x (test_number 0)) test_x))) =
  assert_norm (rewrite 5 (test_add test_x (test_number 0)) test_x);
  assert_norm (not (rewrite 5 (test_add test_x (test_number 1)) test_x));
  assert_norm (not (rewrite 7 (test_add test_x (test_number 0)) test_x));
  assert_norm (not (rewrite 1 test_x test_x));
  assert_norm (not (rewrite 5 (test_add (Var 0 test_sort) (test_number 0)) (Var 0 test_sort)));
  assert_norm (clause 5 (R.mk_eq_expr (test_add test_x (test_number 0)) test_x));
  assert_norm (not (clause 5 (R.mk_eq_expr test_x (test_number 0))));
  assert_norm (not (clause 5 (R.mk_eq_expr (test_add (Var 0 test_sort) (test_number 0)) (Var 0 test_sort))));
  assert_norm (not (clause 7 (R.mk_eq_expr (test_add test_x (test_number 0)) test_x)))
