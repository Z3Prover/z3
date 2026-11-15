module Z3IndependentCheckerTests

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module Root = Z3SortedRootDocument
module C = Z3IndependentChecker
module Skolem = Z3IndependentSkolemRoot
module DReplay = Z3IndependentDependentReplay
module Definition = Z3IndependentDefinitionDocument

let schema : S.schema = { S.sorts = []; S.cases = [] }
let asserted : P.entry = { P.rule = U.Asserted; P.formula = R.false_expr; P.premise_ids = [] }
let doc : P.document = {
  P.declarations = []; P.expressions = []; P.assertions = [R.false_expr];
  P.entries = [asserted]; P.root = 0;
}

let certified ()
  : Lemma (C.check schema doc == Root.RootCertified) =
  assert_norm (Root.check_root_document_epsilon schema doc == Root.RootCertified)

let missing_root ()
  : Lemma (C.check schema { doc with P.root = 1 } == Root.RootRejected) =
  assert_norm (Root.check_root_document_epsilon schema { doc with P.root = 1 } == Root.RootRejected)

let distinct_preserves_certified_and_rejected ()
  : Lemma (C.check_distinct schema doc == Root.RootCertified /\
           C.check_distinct schema { doc with P.root = 1 } == Root.RootRejected) =
  certified ();
  missing_root ()

let skolem_preserves_certified_and_rejected ()
  : Lemma (C.check_skolem schema doc == Root.RootCertified /\
           C.check_skolem schema { doc with P.root = 1 } == Root.RootRejected) =
  certified ();
  missing_root ()

let skolem_preserves_nonpending (schema:S.schema) (doc:P.document)
  : Lemma (requires not (Root.RootPending? (C.check schema doc)))
          (ensures C.check_skolem schema doc == C.check schema doc) =
  ()

let definition_preserves_nonpending (schema:S.schema) (doc:P.document)
  : Lemma (requires not (Root.RootPending? (C.check schema doc)))
          (ensures C.check_definition schema doc == C.check schema doc) =
  ()

let definition_gate_preserves_eligibility (schema:S.checked_schema) (doc:P.document)
  : Lemma (Definition.eligible schema doc ==
           (Definition.has_definition doc.P.entries && Definition.eligible schema doc)) =
  if not (Definition.has_definition doc.P.entries) then
    Definition.lemma_no_definitions schema doc

let skolem_retry_gate () : Lemma (
  C.skolem_without_definitions [] false == false /\
  C.skolem_without_definitions [{ asserted with P.rule = U.Skolemization }] false == true /\
  C.skolem_without_definitions
    [{ asserted with P.rule = U.Skolemization }; { asserted with P.rule = U.DefinitionIntroduction }]
    false == false) =
  assert_norm (C.skolem_without_definitions [] false == false);
  assert_norm (C.skolem_without_definitions [{ asserted with P.rule = U.Skolemization }] false == true);
  assert_norm (C.skolem_without_definitions
    [{ asserted with P.rule = U.Skolemization }; { asserted with P.rule = U.DefinitionIntroduction }]
    false == false)

let mixed_retry_gate () : Lemma (
  not (C.skolem_with_definitions [{ asserted with P.rule = U.Skolemization }] false false) /\
  C.skolem_with_definitions
    [{ asserted with P.rule = U.Skolemization }; { asserted with P.rule = U.DefinitionIntroduction }]
    false false /\
  C.skolem_with_definitions
    [{ asserted with P.rule = U.DefinitionIntroduction }; { asserted with P.rule = U.Skolemization }]
    false false) =
  assert_norm (not (C.skolem_with_definitions
    [{ asserted with P.rule = U.Skolemization }] false false));
  assert_norm (C.skolem_with_definitions
    [{ asserted with P.rule = U.Skolemization }; { asserted with P.rule = U.DefinitionIntroduction }]
    false false);
  assert_norm (C.skolem_with_definitions
    [{ asserted with P.rule = U.DefinitionIntroduction }; { asserted with P.rule = U.Skolemization }]
    false false)

let prior_definition_verdict (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = C.check schema doc in
  match base with
  | Root.RootPending _ ->
    if Some? (C.definition_augmented schema doc) then Root.RootCertified else base
  | _ -> base

let definition_preserves_prior_nonpending (schema:S.schema) (doc:P.document)
  : Lemma (requires not (Root.RootPending? (prior_definition_verdict schema doc)))
          (ensures C.check_definition schema doc == prior_definition_verdict schema doc) =
  ()

let prior_definition_skolem_verdict (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = C.check schema doc in
  match base with
  | Root.RootPending _ ->
    if Some? (C.definition_augmented schema doc) ||
       (C.skolem_without_definitions doc.P.entries false &&
        S.valid schema && Skolem.check schema doc = Root.RootCertified)
    then Root.RootCertified else base
  | _ -> base

let definition_preserves_prior_skolem_nonpending (schema:S.schema) (doc:P.document)
  : Lemma (requires not (Root.RootPending? (prior_definition_skolem_verdict schema doc)))
          (ensures C.check_definition schema doc == prior_definition_skolem_verdict schema doc) =
  ()

let prior_combined_verdict (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = C.check schema doc in
  match base with
  | Root.RootPending _ ->
    if Some? (C.definition_augmented schema doc) || Some? (C.combined_augmented schema doc) ||
       (C.skolem_without_definitions doc.P.entries false &&
        S.valid schema && Skolem.check schema doc = Root.RootCertified)
    then Root.RootCertified else base
  | _ -> base

let definition_preserves_prior_combined_nonpending (schema:S.schema) (doc:P.document)
  : Lemma (requires not (Root.RootPending? (prior_combined_verdict schema doc)))
          (ensures C.check_definition schema doc == prior_combined_verdict schema doc) =
  ()

let prior_dependent_combined_verdict (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = C.check schema doc in
  match base with
  | Root.RootPending _ ->
    if Some? (C.definition_augmented schema doc) || Some? (C.combined_augmented schema doc) ||
       Some? (C.combined_dependent_augmented schema doc) ||
       (C.skolem_without_definitions doc.P.entries false &&
        S.valid schema && Skolem.check schema doc = Root.RootCertified)
    then Root.RootCertified else base
  | _ -> base

let definition_preserves_prior_dependent_nonpending (schema:S.schema) (doc:P.document)
  : Lemma (requires not (Root.RootPending? (prior_dependent_combined_verdict schema doc)))
          (ensures C.check_definition schema doc == prior_dependent_combined_verdict schema doc) =
  ()

let prior_binder_combined_verdict (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = C.check schema doc in
  match base with
  | Root.RootPending _ ->
    if Some? (C.definition_augmented schema doc) || Some? (C.combined_augmented schema doc) ||
       Some? (C.combined_dependent_augmented schema doc) ||
       Some? (C.combined_binder_augmented schema doc) ||
       (C.skolem_without_definitions doc.P.entries false &&
        S.valid schema && Skolem.check schema doc = Root.RootCertified)
    then Root.RootCertified else base
  | _ -> base

let definition_preserves_prior_binder_nonpending (schema:S.schema) (doc:P.document)
  : Lemma (requires not (Root.RootPending? (prior_binder_combined_verdict schema doc)))
          (ensures C.check_definition schema doc == prior_binder_combined_verdict schema doc) =
  ()

let prior_definition_free_dependent_verdict (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = C.check schema doc in
  match base with
  | Root.RootPending _ ->
    if Some? (C.definition_augmented schema doc) || Some? (C.combined_augmented schema doc) ||
       Some? (C.combined_dependent_augmented schema doc) || Some? (C.combined_binder_augmented schema doc) ||
       (C.skolem_without_definitions doc.P.entries false &&
        S.valid schema && Skolem.check schema doc = Root.RootCertified) ||
       (not (C.has_definition doc.P.entries) && S.valid schema &&
        DReplay.may_change schema doc && Skolem.check_dependent schema doc = Root.RootCertified)
    then Root.RootCertified else base
  | _ -> base

let definition_preserves_prior_free_dependent_nonpending (schema:S.schema) (doc:P.document)
  : Lemma (requires not (Root.RootPending? (prior_definition_free_dependent_verdict schema doc)))
          (ensures C.check_definition schema doc == prior_definition_free_dependent_verdict schema doc) =
  ()

let former_skolem_verdict (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = C.check schema doc in
  match base with
  | Root.RootPending _ ->
    if S.valid schema && Skolem.check schema doc = Root.RootCertified
    then Root.RootCertified else base
  | _ -> base

let expanded_preserves_previous_nonpending (schema:S.schema) (doc:P.document)
  : Lemma (requires not (Root.RootPending? (former_skolem_verdict schema doc)))
          (ensures C.check_skolem schema doc == former_skolem_verdict schema doc) =
  ()

let unpruned_skolem_verdict (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = C.check schema doc in
  match base with
  | Root.RootPending _ ->
    if S.valid schema &&
       (Skolem.check schema doc = Root.RootCertified ||
        Skolem.check_dependent schema doc = Root.RootCertified ||
        Skolem.check_binder schema doc = Root.RootCertified)
    then Root.RootCertified else base
  | _ -> base

let pruning_preserves_skolem_verdict (schema:S.schema) (doc:P.document)
  : Lemma (C.check_skolem schema doc == unpruned_skolem_verdict schema doc) =
  if S.valid schema && not (Skolem.contexts_may_differ schema doc) then
    Skolem.lemma_same_context_verdict schema doc

let prior_skolem_verdict (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = C.check schema doc in
  match base with
  | Root.RootPending _ ->
    if S.valid schema &&
       (Skolem.check schema doc = Root.RootCertified ||
        (Skolem.contexts_may_differ schema doc &&
         Skolem.check_dependent schema doc = Root.RootCertified))
    then Root.RootCertified else base
  | _ -> base

let binder_preserves_prior_nonpending (schema:S.schema) (doc:P.document)
  : Lemma (requires not (Root.RootPending? (prior_skolem_verdict schema doc)))
          (ensures C.check_skolem schema doc == prior_skolem_verdict schema doc) =
  ()

let pending ()
  : Lemma (C.check schema
             { doc with P.entries = [{ asserted with P.rule = U.Unverified "unknown" }] } ==
           Root.RootPending 1) =
  assert_norm (Root.check_root_document_epsilon schema
                 { doc with P.entries = [{ asserted with P.rule = U.Unverified "unknown" }] } ==
               Root.RootPending 1)

let diagnostic_agrees (schema:S.schema) (doc:P.document)
  : Lemma (Z3SortedProof.diagnostic_result (C.diagnose schema doc) ==
           Z3SortedProof.check_document_epsilon schema doc) =
  let _ = C.diagnose schema doc in ()
