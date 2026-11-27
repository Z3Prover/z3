module Z3IndependentArrayGroundDocument

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module SP = Z3SortedProof
module Root = Z3SortedRootDocument
module Array = Z3IndependentArrayDocument
module AP = Z3IndependentArrayPreservation
module AI = Z3IndependentArrayInterpretation
module AF = Z3IndependentArrayFamily
module Ground = Z3IndependentGroundDocument
module GroundModel = Z3IndependentGroundDefinition
module GroundRoot = Z3IndependentGroundDefinitionRoot

let selected (schema:S.schema) (doc:P.document) : option P.document =
  if S.valid schema && Ground.within_budget doc then
    match Ground.choose schema doc with
    | Some c ->
      if Array.within_budget doc &&
         AP.eligible (S.signature schema) Array.max_assertions doc.P.assertions &&
         Array.has_candidates schema doc then
        let augmented = Array.augment schema (Ground.augment doc (fst c)) in
        if Root.check_root_document_epsilon schema augmented = Root.RootCertified
        then Some augmented else None
      else None
    | None -> None
  else None

let lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires Some? (selected schema doc))
          (ensures not (Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions)) =
  match Ground.choose schema doc with
  | None -> ()
  | Some (entry, d) ->
    let bc = TR.booleans u in
    let eq = SR.root_scalars u in
    let extended = TR.standard u schema (AI.symbols u schema symbols) in
    let grounded = GroundModel.override schema bc eq extended doc.P.assertions entry.P.formula d in
    let ground_doc = Ground.augment doc entry in
    AI.lemma_root_inhabited u schema symbols;
    AI.lemma_model u schema symbols;
    GroundRoot.lemma_override_root u schema bc eq doc.P.assertions entry.P.formula d extended;
    GroundRoot.lemma_override_array_model u schema bc eq doc.P.assertions entry.P.formula d
      extended (AF.family u (S.signature schema));
    GroundModel.lemma_inputs schema bc eq extended doc.P.assertions entry.P.formula d;
    GroundModel.lemma_definition schema bc eq extended doc.P.assertions entry.P.formula d;
    SP.lemma_truths_append schema bc eq grounded doc.P.assertions [entry.P.formula];
    Root.lemma_truths_agreement u schema extended doc.P.assertions;
    Root.lemma_truths_agreement u schema grounded doc.P.assertions;
    Root.lemma_truths_agreement u schema grounded ground_doc.P.assertions;
    assert (Root.root_truths u schema grounded ground_doc.P.assertions ==
            Root.root_truths u schema extended doc.P.assertions);
    Array.lemma_augment_truths_model u schema ground_doc grounded;
    AP.lemma_eligible_truths u schema symbols Array.max_assertions doc.P.assertions;
    Root.lemma_root_certified_epsilon u schema (Array.augment schema ground_doc) grounded
