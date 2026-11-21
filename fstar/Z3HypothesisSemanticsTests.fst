module Z3HypothesisSemanticsTests

open Z3AstTheory
module H = Z3HypothesisSemantics
module C = Z3ClausalSemantics
module R = Z3ClauseSyntax
module U = Z3UnifiedProofSyntax

let p = Var 0 bool_sort
let q = Var 1 bool_sort
let r = Var 2 bool_sort
let valid (e:expr) = get_sort e = bool_sort
let neg_p = R.mk_not_expr p
let disj = App (R.or_decl [neg_p; q]) [neg_p; q]

let direct_complement (rho:C.valuation)
  : Lemma (requires H.complements_from_false rho valid /\ H.clause_from_formula rho valid /\
                    not (rho neg_p) /\ rho r)
          (ensures rho p /\ rho r) =
  assert_norm (U.remaining_hypotheses [p; r] neg_p == [r] /\
               H.valid_list valid [p; r] /\ valid neg_p /\ H.valid_list valid (R.formula_clause neg_p));
  H.lemma_remaining rho valid [p; r] neg_p

let disjunction_complement (rho:C.valuation)
  : Lemma (requires H.complements_from_false rho valid /\ H.clause_from_formula rho valid /\
                    not (rho disj) /\ rho r)
          (ensures rho p /\ rho r) =
  assert_norm (U.remaining_hypotheses [p; r] disj == [r] /\
               H.valid_list valid [p; r] /\ valid disj /\ H.valid_list valid (R.formula_clause disj));
  H.lemma_remaining rho valid [p; r] disj
