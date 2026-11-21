module Z3SortedQuantifierInstantiation

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module B = Z3SortedBinding
module D = Z3ExprScope
module C = Z3CanonicalOps
module R = Z3ClauseSyntax
module Syntax = Z3QuantifierInstantiationSyntax
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

let rec lemma_reverse_sorts (args acc:list expr) (ss sacc:list sort)
  : Lemma (requires sorts_match args ss /\ sorts_match acc sacc)
          (ensures sorts_match (L.rev_acc args acc) (L.rev_acc ss sacc))
          (decreases args) =
  match args, ss with
  | a :: rest, s :: tail -> lemma_reverse_sorts rest (a :: acc) tail (s :: sacc)
  | _, _ -> ()

let lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (args:list expr) (formula:expr)
  : Lemma (requires Q.forall_elimination_model s bc other /\
                    D.scoped [] formula /\ Syntax.check args formula)
          (ensures T.truth s bc eq other formula) =
  match formula with
  | App f [App n [Quantifier Forall_k bs t body]; inst] ->
    assert (f == R.or_decl [App n [Quantifier Forall_k bs t body]; inst]);
    assert (n == R.not_decl);
    assert_norm (T.classify R.not_decl == T.Negation);
    assert_norm (T.classify (R.or_decl [App n [Quantifier Forall_k bs t body]; inst]) ==
                 T.Nary Z3BoundedBoolEquiv.Or);
    D.lemma_scoped_reverse_acc [] args [];
    lemma_reverse_sorts args [] bs [];
    let sigma = S.signature s in
    let i = T.interpretation s bc eq other in
    let rho = T.empty_environment sigma in
    let scope = L.rev bs in
    let actuals = L.rev args in
    let vs = V.evaluate_args sigma i [] rho actuals scope in
    let function_body = V.typed_body sigma bs bool_sort
      (V.evaluate_body sigma i [] rho bs body) in
    LP.append_l_nil scope;
    B.lemma_substitute sigma i [] rho actuals scope body inst;
    T.lemma_negation s bc eq other n (Quantifier Forall_k bs t body);
    T.lemma_nary s bc eq other f [App n [Quantifier Forall_k bs t body]; inst]
      Z3BoundedBoolEquiv.Or;
    Q.lemma_or_pair (T.truth s bc eq other) (App n [Quantifier Forall_k bs t body]) inst;
    Q.lemma_forall_elimination s bc other bs function_body vs;
    assert (function_body vs == V.evaluate sigma i [] rho inst)
  | _ -> ()
