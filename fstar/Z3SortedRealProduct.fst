module Z3SortedRealProduct

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open FStar.Real
open FStar.List.Tot
module A = Z3LinearArithmeticAst
module B = Z3BoundedBoolEquiv
module D = Z3Definitions
module L = FStar.List.Tot
module LIN = Z3SortedRealLinear
module R = Z3ResolutionProofTheory
module RL = Z3SortedReal
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

let zero : expr = App (RL.real_numeral_decl 0 1) []
let positive (e:expr) : expr = App RL.real_gt_decl [e; zero]

let lemma_positive_shape (e:expr)
  : Lemma (requires D.scoped [] e /\ get_sort e == A.real_s)
          (ensures D.scoped [] (positive e) /\
                   A.comparison (positive e) == Some (A.Gt, e, zero) /\
                   R.formula_clause (positive e) == [positive e]) =
  assert_norm (get_sort zero == A.real_s);
  assert (A.application RL.real_gt_decl [e; zero] bool_sort ">" op_arith_gt)

let positive_product (s:S.checked_schema) (facts:list expr) (p:expr) : bool =
  match p with
  | App f [x; y] ->
    RL.classify f = RL.Calculate A.Mul &&
    D.scoped [] p &&
    LIN.refutes s facts (positive x) && LIN.refutes s facts (positive y) &&
    LIN.refutes s (positive p :: facts) R.false_expr
  | _ -> false

let product (e:expr) : bool =
  match e with App f [_; _] -> RL.classify f = RL.Calculate A.Mul | _ -> false

let product_literal (e:expr) : option expr =
  match A.literal 16 true e with
  | Some (_, _, x, y) -> if product x then Some x else if product y then Some y else None
  | None -> None

let rec candidate (s:S.checked_schema) (facts rest:list expr)
  : Tot (p:option expr{Some? p ==> positive_product s facts (Some?.v p)}) (decreases rest) =
  match rest with
  | [] -> None
  | e :: tail ->
    (match product_literal e with
     | Some p -> if positive_product s facts p then Some p else candidate s facts tail
     | None -> candidate s facts tail)

let check (s:S.checked_schema) (facts:list expr) : bool =
  if not (RL.real_primitive s) || L.length facts > 30 then false
  else if None? (arguments_budget 4096 facts) then false
  else Some? (candidate s facts facts)

let lemma_positive_meaning (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (reals:RL.carrier base) (e:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped [] e /\ get_sort e == A.real_s)
          (ensures T.truth s bc model other (positive e) <==>
                   RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) e >. 0.0R) =
  let rho = T.empty_environment (S.signature s) in
  lemma_positive_shape e;
  LIN.lemma_comparison s bc model other reals [] rho (positive e) e zero A.Gt;
  RL.lemma_real_numeral_at s bc model other reals [] rho (RL.real_numeral_decl 0 1) 0 1

let lemma_positive (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (reals:RL.carrier base) (facts:list expr) (e:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    D.scoped [] e /\ get_sort e == A.real_s /\ LIN.refutes s facts (positive e))
          (ensures RL.real_at s bc model other reals [] (T.empty_environment (S.signature s)) e >. 0.0R) =
  let c = positive e in
  lemma_positive_shape e;
  if not (T.truth s bc model other c) then (
    assert (R.formula_clause c == [c]);
    LIN.lemma_refutes s bc model other reals facts c);
  lemma_positive_meaning s bc model other reals e

#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0"
let lemma_multiply_positive (x y:real)
  : Lemma (requires x >. 0.0R /\ y >. 0.0R) (ensures x *. y >. 0.0R) = ()
#pop-options

let lemma_positive_product (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (reals:RL.carrier base) (facts:list expr) (p:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    positive_product s facts p)
          (ensures False) =
  match p with
  | App f [x; y] ->
    let rho = T.empty_environment (S.signature s) in
    RL.lemma_real_binary_at s bc model other reals [] rho f x y A.Mul;
    lemma_positive s bc model other reals facts x;
    lemma_positive s bc model other reals facts y;
    lemma_multiply_positive (RL.real_at s bc model other reals [] rho x)
                            (RL.real_at s bc model other reals [] rho y);
    let c = positive p in
    lemma_positive_meaning s bc model other reals p;
    assert (T.truth s bc model other c);
    assert_norm (R.formula_clause R.false_expr == []);
    assert_norm (not (B.geval_args (T.truth s bc model other) B.Or []));
    LIN.lemma_refutes s bc model other reals (c :: facts) R.false_expr
  | _ -> ()

let lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (reals:RL.carrier base) (facts:list expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\ check s facts)
          (ensures False) =
  lemma_positive_product s bc model other reals facts (Some?.v (candidate s facts facts))
