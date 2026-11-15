module Z3IndependentRootReplay

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module Root = Z3SortedRootDocument
module SP = Z3SortedProof
module TR = Z3TypedRoot
module DS = Z3SortedDependentSkolem
module Fallback = Z3IndependentCertificateFallback
module Cached = Z3IndependentCachedReplay
module U = Z3UnifiedProofSyntax

let prepare (schema:S.checked_schema) (doc:P.document)
  : result:(P.document & list (DS.definition schema)){
      fst result == SP.elaborate_full schema doc /\
      snd result == SP.dependent_context schema doc (SP.epsilon_context schema doc)} =
  let epsilon = SP.epsilon_context schema doc in
  let dependent = SP.dependent_context schema doc epsilon in
  SP.elaborate_dependent schema dependent (SP.elaborate_epsilon schema epsilon doc),
  dependent

let gate (schema:S.checked_schema) (doc:P.document)
         (dependent:list (DS.definition schema)) (checked:option nat) : Root.root_verdict =
  match checked with
  | None -> Root.RootRejected
  | Some n ->
    if n > 0 then Root.RootPending n
    else if Root.root_covered schema doc &&
            TR.supported_expressions (S.signature schema) (DS.closures schema dependent)
    then Root.RootCertified
    else Root.RootUncovered

let check (schema:S.schema) (doc:P.document) =
  if S.valid schema then
    let expanded, dependent = prepare schema doc in
    gate schema doc dependent (SP.check_document schema expanded)
  else Root.RootRejected

let check_diagnosed (schema:S.schema) (doc:P.document) =
  if S.valid schema then
    let expanded, dependent = prepare schema doc in
    let checked, diagnostic = SP.check_document_diagnosed schema expanded in
    gate schema doc dependent checked, diagnostic
  else Root.RootRejected, P.DocumentRejected P.LogicalDeclarations None None

let recover_cached (schema:S.checked_schema) (doc:P.document)
                   (assertions:list Z3AstTheory.expr) (memo:Cached.cache schema assertions)
                   (base:Root.root_verdict)
  : result:Root.root_verdict{result == Fallback.recover schema doc base} =
  if base = Root.RootUncovered && Fallback.has_candidates doc.P.entries then
    let repaired = Fallback.repair doc in
    let expanded, dependent = prepare schema repaired in
    let diagnostic, _ =
      if expanded.P.assertions = assertions
      then Cached.diagnose_document schema expanded (Cached.seal schema assertions memo)
      else Cached.diagnose_document schema expanded (Cached.empty schema expanded.P.assertions) in
    SP.lemma_diagnose_document schema expanded;
    if gate schema repaired dependent (SP.diagnostic_result diagnostic) = Root.RootCertified
    then Root.RootCertified else base
  else base

let rec has_certificates (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest ->
    match e.P.rule with
    | U.QuantifierIntroduction _ -> true
    | _ -> has_certificates rest

let check_recovering (schema:S.schema) (doc:P.document) =
  if not (has_certificates doc.P.entries)
  then Fallback.recover schema doc (check schema doc)
  else if S.valid schema then
    let expanded, dependent = prepare schema doc in
    let diagnostic, memo =
      Cached.diagnose_document schema expanded (Cached.empty schema expanded.P.assertions) in
    SP.lemma_diagnose_document schema expanded;
    let base = gate schema doc dependent (SP.diagnostic_result diagnostic) in
    recover_cached schema doc expanded.P.assertions memo base
  else Root.RootRejected

let check_recovering_diagnosed (schema:S.schema) (doc:P.document) =
  if not (has_certificates doc.P.entries) then
    let base, diagnostic = check_diagnosed schema doc in
    Fallback.recover schema doc base, diagnostic
  else if S.valid schema then
    let expanded, dependent = prepare schema doc in
    let diagnostic, memo =
      Cached.diagnose_document schema expanded (Cached.empty schema expanded.P.assertions) in
    SP.lemma_diagnose_document schema expanded;
    let base = gate schema doc dependent (SP.diagnostic_result diagnostic) in
    recover_cached schema doc expanded.P.assertions memo base, diagnostic
  else Root.RootRejected, P.DocumentRejected P.LogicalDeclarations None None
