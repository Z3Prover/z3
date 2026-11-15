module Z3IndependentArrayPreservationTests

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3ExprScope
module TR = Z3TypedRoot
module T = Z3SortedSemantics
module R = Z3ClauseSyntax
module A = Z3SortedArray
module AI = Z3IndependentArrayInterpretation
module AP = Z3IndependentArrayPreservation
module Root = Z3SortedRootDocument
module TT = Z3TypedRootTests

let int_s = TR.int_s
let arr_s = ArraySort [int_s] int_s
let schema : S.checked_schema = { S.sorts = []; S.cases = [] }
let array_decl : func_decl =
  { decl_name = "a"; domain = []; range = arr_s; interp = None; int_params = [] }
let array = App array_decl []
let select_body = App (A.select_decl int_s int_s) [array; Var 0 int_s]
let quantified = Quantifier Forall_k [int_s] bool_sort (R.mk_eq_expr select_body (Var 0 int_s))
let lambda = Quantifier Lambda_k [int_s] arr_s select_body
let lambda_equality = R.mk_eq_expr lambda lambda
let selected = App (A.ext_decl int_s int_s) [array; array]
let nested_selected = Quantifier Forall_k [int_s] bool_sort (R.mk_eq_expr selected (Var 0 int_s))
let malformed_decl = { A.ext_decl int_s int_s with decl_name = "other" }
let malformed = App malformed_decl [array; array]
let datatype_accessor = App TT.head_decl [App TT.nil_decl []]

let guard_controls ()
  : Lemma (AP.safe [] quantified /\ AP.safe [] lambda_equality /\
           AP.safe [] malformed /\ not (AP.safe [] selected) /\
           not (AP.safe [] nested_selected) /\
           AP.safe (S.signature TT.lsch) datatype_accessor /\
           D.scoped [] quantified /\ D.scoped [] lambda_equality /\
           AP.eligible [] 100 [quantified; lambda_equality] /\
           not (AP.eligible [] 1 [quantified; lambda_equality]) /\
           not (AP.eligible [] 100 [nested_selected]) /\
           Some? (S.find_accessor TT.head_decl TT.lsch.S.cases) /\
           TT.nil_decl <> TT.cons_decl) =
  assert_norm (AP.safe [] quantified);
  assert_norm (AP.safe [] lambda_equality);
  assert_norm (AP.safe [] malformed);
  assert_norm (not (AP.safe [] selected));
  assert_norm (not (AP.safe [] nested_selected));
  assert_norm (AP.safe (S.signature TT.lsch) datatype_accessor);
  assert_norm (D.scoped [] quantified);
  assert_norm (D.scoped [] lambda_equality);
  assert_norm (AP.eligible [] 100 [quantified; lambda_equality]);
  assert_norm (not (AP.eligible [] 1 [quantified; lambda_equality]));
  assert_norm (not (AP.eligible [] 100 [nested_selected]));
  assert_norm (Some? (S.find_accessor TT.head_decl TT.lsch.S.cases));
  assert_norm (TT.nil_decl <> TT.cons_decl)

let original_assertions (u:TR.uninterpreted) (uf:TR.symbols u schema)
  : Lemma (
    Root.root_truths u schema (TR.standard u schema (AI.symbols u schema uf))
      [quantified; lambda_equality] ==
    Root.root_truths u schema (TR.standard u schema uf) [quantified; lambda_equality]) =
  guard_controls ();
  AP.lemma_eligible_truths u schema uf 100 [quantified; lambda_equality]

let noncanonical_application (u:TR.uninterpreted) (uf:TR.symbols u schema)
  : Lemma (
    let rho = T.empty_environment (S.signature schema) in
    Z3DatatypeValue.evaluate (S.signature schema) (TR.standard u schema (AI.symbols u schema uf))
      [] rho malformed ==
    Z3DatatypeValue.evaluate (S.signature schema) (TR.standard u schema uf) [] rho malformed) =
  guard_controls ();
  assert_norm (D.scoped [] malformed);
  AP.lemma_evaluate u schema uf [] (T.empty_environment (S.signature schema)) malformed

let datatype_fallback (u:TR.uninterpreted) (uf:TR.symbols u TT.lsch)
  : Lemma (
    let rho = T.empty_environment (S.signature TT.lsch) in
    Z3DatatypeValue.evaluate (S.signature TT.lsch) (TR.standard u TT.lsch (AI.symbols u TT.lsch uf))
      [] rho datatype_accessor ==
    Z3DatatypeValue.evaluate (S.signature TT.lsch) (TR.standard u TT.lsch uf)
      [] rho datatype_accessor) =
  guard_controls ();
  assert_norm (D.scoped [] datatype_accessor);
  AP.lemma_evaluate u TT.lsch uf [] (T.empty_environment (S.signature TT.lsch)) datatype_accessor
