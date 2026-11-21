module Z3IndependentArrayReplay

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module A = Z3SortedArray
module AF = Z3IndependentArrayFamily
module AI = Z3IndependentArrayInterpretation
module R = Z3ClauseSyntax
module Root = Z3SortedRootDocument

let rec lemma_supported (u:TR.uninterpreted) (sch:S.checked_schema) (e:expr)
  : Lemma (supported (S.signature sch) e == A.supported (AF.family u (S.signature sch)) e)
    (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ args -> lemma_supported_args u sch args
  | Quantifier _ _ _ body -> lemma_supported u sch body

and lemma_supported_args (u:TR.uninterpreted) (sch:S.checked_schema) (es:list expr)
  : Lemma (supported_args (S.signature sch) es == A.supported_args (AF.family u (S.signature sch)) es)
    (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    lemma_supported u sch e;
    lemma_supported_args u sch rest

let lemma_clause_model (u:TR.uninterpreted) (sch:S.checked_schema) (root:TR.interp u sch) (e:expr)
  : Lemma (requires TR.root_model u sch root /\
                    A.model sch (TR.booleans u) (SR.root_scalars u) root (AF.family u (S.signature sch)) /\
                    clause (S.signature sch) e)
          (ensures Root.root_holds u sch root e) =
  let sigma = S.signature sch in
  let m = AF.family u sigma in
  let rho = T.empty_environment sigma in
  lemma_supported u sch e;
  A.lemma_array_lemma sch (TR.booleans u) (SR.root_scalars u) root m [] rho e;
  Root.lemma_holds_agreement u sch root e

let lemma_clause (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch) (e:expr)
  : Lemma (requires clause (S.signature sch) e)
          (ensures Root.root_holds u sch (TR.standard u sch (AI.symbols u sch uf)) e) =
  AI.lemma_root_inhabited u sch uf;
  AI.lemma_model u sch uf;
  lemma_clause_model u sch (TR.standard u sch (AI.symbols u sch uf)) e

let lemma_rewrite_model (u:TR.uninterpreted) (sch:S.checked_schema)
  (root:TR.interp u sch) (a b:expr)
  : Lemma (requires TR.root_model u sch root /\
                    A.model sch (TR.booleans u) (SR.root_scalars u) root (AF.family u (S.signature sch)) /\
                    rewrite (S.signature sch) a b)
          (ensures Root.root_holds u sch root (R.mk_eq_expr a b)) =
  let sigma = S.signature sch in
  let m = AF.family u sigma in
  let rho = T.empty_environment sigma in
  lemma_supported u sch a;
  lemma_supported u sch b;
  A.lemma_equivalent sch (TR.booleans u) (SR.root_scalars u) root m [] rho search_fuel a b;
  T.lemma_equality sch (TR.booleans u) (SR.root_scalars u) root a b;
  Root.lemma_holds_agreement u sch root (R.mk_eq_expr a b)

let lemma_rewrite (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch) (a b:expr)
  : Lemma (requires rewrite (S.signature sch) a b)
          (ensures Root.root_holds u sch (TR.standard u sch (AI.symbols u sch uf))
                    (R.mk_eq_expr a b)) =
  AI.lemma_root_inhabited u sch uf;
  AI.lemma_model u sch uf;
  lemma_rewrite_model u sch (TR.standard u sch (AI.symbols u sch uf)) a b
