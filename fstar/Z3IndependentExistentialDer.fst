module Z3IndependentExistentialDer

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module D = Z3ExprScope
module R = Z3ClauseSyntax
module N = Z3NnfReplay
module C = Z3CanonicalOps

let witness (t:sort) (a b:expr) : option expr =
  match a, b with
  | Var n s, term ->
    if n = 0 && s = t && get_sort term = t && D.scoped [] term then Some term else None
  | term, Var n s ->
    if n = 0 && s = t && get_sort term = t && D.scoped [] term then Some term else None
  | _, _ -> None

let check (q e:expr) : bool =
  e = R.true_expr &&
  (match q with
   | Quantifier Exists_k [t] s (App f [a; b]) ->
     s = bool_sort && f = R.eq_decl t && Some? (witness t a b)
   | _ -> false)

let lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (q e:expr)
  : Lemma (requires E.exists_model s bc other /\ D.scoped [] q /\ D.scoped [] e /\ check q e)
          (ensures T.evaluate s bc eq other q == T.evaluate s bc eq other e) =
  match q with
  | Quantifier Exists_k [t] _ (App _ [a; b]) ->
    let term = Some?.v (witness t a b) in
    let sigma = S.signature s in
    let rho = T.empty_environment sigma in
    let value = T.evaluate s bc eq other term in
    let vs : V.arguments base sigma [t] = [value] in
    let extended = V.extend sigma [] [t] vs rho in
    Q.lemma_closed_values sigma (T.interpretation s bc eq other) rho [term];
    N.lemma_exists_truth s bc eq other [] rho [t] (R.mk_eq_expr a b);
    T.lemma_equality_at s bc eq other [t] extended a b;
    T.lemma_evaluate_core_at s bc eq other [] rho C.true_decl [];
    N.lemma_same_truth s bc eq other [] rho q e;
    N.lemma_same_at s bc eq other [] rho q e
  | _ -> ()
