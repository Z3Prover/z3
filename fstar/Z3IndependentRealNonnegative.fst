module Z3IndependentRealNonnegative

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open FStar.Real
module A = Z3LinearArithmeticAst
module B = Z3BoundedBoolEquiv
module D = Z3ExprScope
module L = FStar.List.Tot
module LIN = Z3SortedRealLinear
module R = Z3ClauseSyntax
module RL = Z3SortedReal
module RP = Z3SortedRealProduct
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

let product (s:S.checked_schema) (facts:list expr) (p:expr) : bool =
  match p with
  | App f [x; y] ->
    RL.classify f = RL.Calculate A.Mul && D.scoped [] p &&
    ((LIN.refutes s facts (RP.bound true x) && LIN.refutes s facts (RP.bound true y)) ||
     (LIN.refutes s facts (RP.bound false x) && LIN.refutes s facts (RP.bound false y))) &&
    LIN.refutes s (RP.bound true p :: facts) R.false_expr
  | _ -> false

let rec candidate (s:S.checked_schema) (facts:list expr) (fuel:nat) (rest:list expr)
  : Tot (p:option expr{Some? p ==> product s facts (Some?.v p)}) (decreases fuel) =
  if fuel = 0 then None
  else match rest with
  | [] -> None
  | p :: tail -> if product s facts p then Some p else candidate s facts (fuel - 1) tail

let witness (s:S.checked_schema) (facts:list expr) : option expr =
  candidate s facts 32 (L.concatMap (RP.products 16) facts)

let check (s:S.checked_schema) (facts:list expr) : bool =
  RL.real_primitive s && L.length facts <= 30 &&
  Some? (arguments_budget 4096 facts) && Some? (witness s facts)

#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0"
let lemma_multiply (x y:real)
  : Lemma (requires (x >=. 0.0R /\ y >=. 0.0R) \/ (x <=. 0.0R /\ y <=. 0.0R))
          (ensures x *. y >=. 0.0R) = ()
#pop-options

let lemma_product (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (reals:RL.carrier base) (facts:list expr) (p:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    product s facts p)
          (ensures False) =
  match p with
  | App f [x; y] ->
    let rho = T.empty_environment (S.signature s) in
    RL.lemma_real_binary_at s bc model other reals [] rho f x y A.Mul;
    if LIN.refutes s facts (RP.bound true x) && LIN.refutes s facts (RP.bound true y) then (
      RP.lemma_bound s bc model other reals facts true x;
      RP.lemma_bound s bc model other reals facts true y)
    else (
      RP.lemma_bound s bc model other reals facts false x;
      RP.lemma_bound s bc model other reals facts false y);
    lemma_multiply (RL.real_at s bc model other reals [] rho x)
                   (RL.real_at s bc model other reals [] rho y);
    let c = RP.bound true p in
    RP.lemma_bound_meaning s bc model other reals true p;
    assert (T.truth s bc model other c);
    assert_norm (R.formula_clause R.false_expr == []);
    assert_norm (not (B.geval_args (T.truth s bc model other) B.Or []));
    LIN.lemma_refutes s bc model other reals (c :: facts) R.false_expr
  | _ -> ()

let lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (reals:RL.carrier base) (facts:list expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    check s facts)
          (ensures False) =
  lemma_product s bc model other reals facts (Some?.v (witness s facts))
