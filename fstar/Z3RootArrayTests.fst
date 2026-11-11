module Z3RootArrayTests

open Z3AstTheory
open Z3ValueTheory
module A = Z3RootArray
module TR = Z3TypedRoot
module RD = Z3SortedRootDocument
module S = Z3DatatypeSignature
module SP = Z3SortedProof
module P = Z3ProofDocument
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory

let schema : S.checked_schema = { S.sorts = []; S.cases = [] }

let constant (name:string) (s:sort) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = [] } []

let rec nested (depth:nat) : Tot sort (decreases depth) =
  if depth = 0 then TR.real_s else ArraySort [TR.int_s] (nested (depth - 1))

let read (d r:sort) (a index:expr) : expr = App (TR.select_decl [d] r) [a; index]
let write (d r:sort) (a index v:expr) : expr = App (TR.store_decl [d] r) [a; index; v]

let equation (d r:sort) : expr =
  let a = constant "a" (ArraySort [d] r) in
  let index = constant "i" d in
  let v = constant "v" r in
  R.mk_eq_expr (read d r (write d r a index v) index) v

let entry (rule:U.rule) (formula:expr) (ids:list int) : P.entry =
  { P.rule = rule; formula = formula; premise_ids = ids }

let refutation (e:expr) : P.document =
  let negated = R.mk_not_expr e in
  { P.declarations = []; expressions = []; assertions = [negated];
    entries = [entry U.RewriteRule e []; entry U.Asserted negated [];
               entry U.UnitResolution R.false_expr [0; 1]]; root = 2 }

let nested_values_and_indices ()
  : Lemma (
    A.valid (S.signature schema) (equation TR.int_s (nested 4)) /\
    A.valid (S.signature schema) (equation (nested 3) (nested 2)) /\
    SP.check_document_epsilon schema (refutation (equation TR.int_s (nested 4))) == Some 1 /\
    A.check_document schema (refutation (equation TR.int_s (nested 4))) == RD.RootCertified /\
    A.check_document schema (refutation (equation (nested 3) (nested 2))) == RD.RootCertified) =
  assert_norm (A.valid (S.signature schema) (equation TR.int_s (nested 4)));
  assert_norm (A.valid (S.signature schema) (equation (nested 3) (nested 2)));
  assert_norm (SP.check_document_epsilon schema (refutation (equation TR.int_s (nested 4))) == Some 1);
  assert_norm (A.check_document schema (refutation (equation TR.int_s (nested 4))) == RD.RootCertified);
  assert_norm (A.check_document schema (refutation (equation (nested 3) (nested 2))) == RD.RootCertified)

let a = constant "a" (ArraySort [TR.int_s] (nested 2))
let index = constant "i" TR.int_s
let other_index = constant "j" TR.int_s
let v = constant "v" (nested 2)
let other_value = constant "w" (nested 2)
let stored = write TR.int_s (nested 2) a index v
let selected = read TR.int_s (nested 2) stored index
let wrong_index = R.mk_eq_expr (read TR.int_s (nested 2) stored other_index) v
let wrong_value = R.mk_eq_expr selected other_value
let fake_select =
  let f = TR.select_decl [TR.int_s] (nested 2) in
  App { f with decl_name = "fake-select" } [stored; index]

let mutations_stay_pending ()
  : Lemma (
    not (A.valid (S.signature schema) wrong_index) /\
    not (A.valid (S.signature schema) wrong_value) /\
    not (A.valid (S.signature schema) (R.mk_eq_expr fake_select v)) /\
    A.check_document schema (refutation wrong_index) == RD.RootPending 1 /\
    A.check_document schema (refutation wrong_value) == RD.RootPending 1) =
  assert_norm (not (A.valid (S.signature schema) wrong_index));
  assert_norm (not (A.valid (S.signature schema) wrong_value));
  assert_norm (not (A.valid (S.signature schema) (R.mk_eq_expr fake_select v)));
  assert_norm (A.check_document schema (refutation wrong_index) == RD.RootPending 1);
  assert_norm (A.check_document schema (refutation wrong_value) == RD.RootPending 1)

let malformed : P.document =
  let e = equation TR.int_s (nested 2) in
  let doc = refutation e in
  { doc with P.entries = [entry U.RewriteRule e [0]; entry U.Asserted (R.mk_not_expr e) [];
                          entry U.UnitResolution R.false_expr [0; 1]] }

let malformed_reference_rejected ()
  : Lemma (A.check_document schema malformed == RD.RootRejected) =
  assert_norm (A.check_document schema malformed == RD.RootRejected)

let reversed_equation ()
  : Lemma (
    A.valid (S.signature schema) (R.mk_eq_expr v selected) /\
    A.check_document schema (refutation (R.mk_eq_expr v selected)) == RD.RootCertified) =
  assert_norm (A.valid (S.signature schema) (R.mk_eq_expr v selected));
  assert_norm (A.check_document schema (refutation (R.mk_eq_expr v selected)) == RD.RootCertified)

let arbitrary_root_models (u:TR.uninterpreted) (i:TR.interp u schema) (doc:P.document)
  : Lemma (requires TR.root_model u schema i /\ A.check_document schema doc == RD.RootCertified)
          (ensures not (RD.root_truths u schema i doc.P.assertions)) =
  A.lemma_certified u schema i doc
