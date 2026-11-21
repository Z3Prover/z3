module Z3IndependentCertificateFallback

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module R = Z3SortedRootDocument
module T = Z3TypedRoot
module U = Z3UnifiedProofSyntax
module N = Z3NnfReplay

let candidate (e:P.entry) : bool =
  match e.P.rule with
  | U.QuantifierIntroduction c -> N.consumed_root c && not (N.certificate_scoped c)
  | _ -> false

let rec has_candidates (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest -> candidate e || has_candidates rest

let rec repair_entries (entries:list P.entry) : Tot (list P.entry) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    let rule =
      if candidate e
      then U.QuantifierIntroduction { U.binder_entries = []; U.binder_root = 0 }
      else e.P.rule in
    { e with P.rule = rule } :: repair_entries rest

let repair (doc:P.document) : result:P.document{result.P.assertions == doc.P.assertions} =
  { doc with P.entries = repair_entries doc.P.entries }

let recover (schema:S.schema) (doc:P.document) (base:R.root_verdict) : R.root_verdict =
  if base = R.RootUncovered && has_candidates doc.P.entries &&
     R.check_root_document_epsilon schema (repair doc) = R.RootCertified
  then R.RootCertified else base

let lemma_certified (u:T.uninterpreted) (schema:S.checked_schema)
                    (doc:P.document) (base:R.root_verdict) (model:T.interp u schema)
  : Lemma (requires base == R.check_root_document_epsilon schema doc /\
                    recover schema doc base == R.RootCertified /\ T.root_model u schema model)
          (ensures not (R.root_truths u schema model doc.P.assertions)) =
  if base = R.RootCertified then R.lemma_root_certified_epsilon u schema doc model
  else R.lemma_root_certified_epsilon u schema (repair doc) model
