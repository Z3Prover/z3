module Z3IndependentDistinctReplayTests

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module DR = Z3SortedDistinctRoot
module Replay = Z3IndependentDistinctReplay

let standard_model_refutation (u:TR.uninterpreted) (schema:S.checked_schema)
                              (symbols:TR.symbols u schema) (doc:P.document)
  : Lemma (requires Root.check_root_document_epsilon schema (Replay.augment doc) == Root.RootCertified)
          (ensures not (Root.root_truths u schema
            (TR.standard u schema (DR.standard_symbols u schema symbols)) doc.P.assertions)) =
  DR.lemma_root_inhabited u schema symbols;
  DR.lemma_distinct_model u schema symbols;
  Replay.lemma_certified u schema doc (TR.standard u schema (DR.standard_symbols u schema symbols))
