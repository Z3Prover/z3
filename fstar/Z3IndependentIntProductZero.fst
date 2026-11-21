module Z3IndependentIntProductZero

open Z3AstTheory
module A = Z3LinearArithmeticAst
module AR = Z3SortedArithmetic
module D = Z3ExprScope
module I = Z3SortedInteger
module L = FStar.List.Tot
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

let rec lemma_arguments_zero (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (args:list expr) (ss:list sort) (factor:expr)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\
                    I.integer_sorts ss /\ L.mem factor args /\
                    AR.integer s bc model other scope rho factor == 0)
          (ensures I.product (I.numbers s model.T.integers ss
                    (T.evaluate_arguments_at s bc model other scope rho args ss)) == 0)
          (decreases args) =
  match args, ss with
  | a :: rest, t :: tail ->
    V.lemma_sort_eq (get_sort a) t;
    if a <> factor then
      lemma_arguments_zero s bc model other scope rho rest tail factor
  | _, _ -> ()

let lemma_product_zero (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (f:func_decl) (args:list expr) (factor:expr)
  : Lemma (requires D.scoped scope (App f args) /\
                    I.classify f == I.Calculate A.Mul /\ L.mem factor args /\
                    AR.integer s bc model other scope rho factor == 0)
          (ensures AR.integer s bc model other scope rho (App f args) == 0) =
  AR.lemma_application s bc model other scope rho f args;
  lemma_arguments_zero s bc model other scope rho args f.domain factor
