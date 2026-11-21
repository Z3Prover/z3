module Z3IndependentArrayDocument

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module AI = Z3IndependentArrayInterpretation
module AP = Z3IndependentArrayPreservation
module Replay = Z3IndependentArrayReplay
module A = Z3SortedArray
module AF = Z3IndependentArrayFamily
module SR = Z3SortedRoot
module SP = Z3SortedProof

let max_work : nat = 2000000

let eligible_entry (schema:S.schema) (entry:P.entry) : bool =
  match entry.P.rule with
  | U.Unverified "th-lemma" ->
    if None? (expression_budget Replay.max_nodes entry.P.formula) then false
    else
      Replay.clause (S.signature schema) entry.P.formula ||
      (match U.classify_fact entry.P.formula with
       | Some (U.Equal a b) ->
         entry.P.formula = R.mk_eq_expr a b && Replay.rewrite (S.signature schema) a b
       | _ -> false)
  | U.RewriteRule ->
    if entry.P.premise_ids <> [] ||
       None? (expression_budget Replay.max_nodes entry.P.formula) then false
    else
      (match U.classify_fact entry.P.formula with
       | Some (U.Equal a b) ->
         entry.P.formula = R.mk_eq_expr a b && Replay.rewrite (S.signature schema) a b
       | _ -> false)
  | _ -> false

let rec budget_entries (fuel:nat) (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> true
  | entry :: rest ->
    if fuel = 0 then false
    else match entry.P.rule with
    | U.Unverified "th-lemma" ->
      (match expression_budget (fuel - 1) entry.P.formula with
       | None -> false
       | Some remaining -> budget_entries remaining rest)
    | U.RewriteRule ->
      if entry.P.premise_ids <> [] then budget_entries (fuel - 1) rest
      else
        (match expression_budget (fuel - 1) entry.P.formula with
         | None -> false
         | Some remaining -> budget_entries remaining rest)
    | _ -> budget_entries (fuel - 1) rest

let within_budget (doc:P.document) : bool = budget_entries max_work doc.P.entries

let rec any_candidate (schema:S.schema) (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | entry :: rest -> eligible_entry schema entry || any_candidate schema rest

let has_candidates (schema:S.schema) (doc:P.document) : bool =
  any_candidate schema doc.P.entries

let rec lemma_core_array_supports (u:TR.uninterpreted) (schema:S.checked_schema) (e:expr)
  : Lemma (requires SP.array_sorts_supported (S.signature schema) e)
          (ensures A.supported (AF.family u (S.signature schema)) e)
          (decreases e) =
  (match get_sort e with
   | ArraySort [index] element ->
     assert (not (V.contains_datatype (S.signature schema) (get_sort e)));
     assert ((AF.family u (S.signature schema)).A.supports index element)
   | _ -> ());
  match e with
  | App _ args -> lemma_core_array_supports_args u schema args
  | Quantifier _ _ _ body -> lemma_core_array_supports u schema body
  | _ -> ()

and lemma_core_array_supports_args (u:TR.uninterpreted) (schema:S.checked_schema)
                                   (es:list expr)
  : Lemma (requires SP.array_sorts_supported_args (S.signature schema) es)
          (ensures A.supported_args (AF.family u (S.signature schema)) es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    lemma_core_array_supports u schema e;
    lemma_core_array_supports_args u schema rest

let lemma_core_array_support (u:TR.uninterpreted) (schema:S.checked_schema) (e:expr)
  : Lemma (requires SP.array_lemma_supported schema e)
          (ensures A.supported (AF.family u (S.signature schema)) e) =
  lemma_core_array_supports u schema e

let rec has_core_candidates (schema:S.checked_schema) (entries:list P.entry)
  : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | entry :: rest -> SP.array_lemma_entry schema entry || has_core_candidates schema rest

let core_selected (schema:S.schema) (doc:P.document) : option P.document =
  if not (S.valid schema) then None
  else if within_budget doc &&
          AP.eligible (S.signature schema) max_assertions doc.P.assertions &&
          has_core_candidates schema doc.P.entries &&
          SP.check_document_array schema doc == Some 0
  then Some doc
  else None

let rec extra_assertions (schema:S.schema) (entries:list P.entry) : Tot (list expr) (decreases entries) =
  match entries with
  | [] -> []
  | entry :: rest ->
    if eligible_entry schema entry then entry.P.formula :: extra_assertions schema rest
    else extra_assertions schema rest

let rec replay_entries_acc (schema:S.schema) (entries:list P.entry) (acc:list P.entry)
  : Tot (list P.entry) (decreases entries) =
  match entries with
  | [] -> acc
  | entry :: rest ->
    replay_entries_acc schema rest
      ((if eligible_entry schema entry
        then { entry with P.rule = U.Asserted; P.premise_ids = [] }
        else entry) :: acc)

let augment (schema:S.schema) (doc:P.document) : P.document =
  { doc with P.assertions = doc.P.assertions @ extra_assertions schema doc.P.entries;
             P.entries = rev (replay_entries_acc schema doc.P.entries []) }

let selected (schema:S.schema) (doc:P.document) : option P.document =
  match core_selected schema doc with
  | Some selected -> Some selected
  | None ->
    if S.valid schema && within_budget doc &&
       AP.eligible (S.signature schema) max_assertions doc.P.assertions &&
       has_candidates schema doc then
      let augmented = augment schema doc in
      if Root.check_root_document_epsilon schema augmented = Root.RootCertified
      then Some augmented else None
    else None

let check (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = Root.check_root_document_epsilon schema doc in
  match base with
  | Root.RootPending _ ->
    if Some? (selected schema doc) then Root.RootCertified else base
  | _ -> base

let lemma_eligible_model (u:TR.uninterpreted) (schema:S.checked_schema)
                         (model:TR.interp u schema) (entry:P.entry)
  : Lemma (requires TR.root_model u schema model /\
                    A.model schema (TR.booleans u) (SR.root_scalars u) model
                      (AF.family u (S.signature schema)) /\ eligible_entry schema entry)
          (ensures Root.root_holds u schema model entry.P.formula) =
  match entry.P.rule with
  | U.Unverified "th-lemma" ->
    if Replay.clause (S.signature schema) entry.P.formula then
      Replay.lemma_clause_model u schema model entry.P.formula
    else
      (match U.classify_fact entry.P.formula with
       | Some (U.Equal a b) -> Replay.lemma_rewrite_model u schema model a b
       | _ -> ())
  | U.RewriteRule ->
    (match U.classify_fact entry.P.formula with
     | Some (U.Equal a b) -> Replay.lemma_rewrite_model u schema model a b
     | _ -> ())
  | _ -> ()

let rec lemma_extras_model (u:TR.uninterpreted) (schema:S.checked_schema)
                           (model:TR.interp u schema) (entries:list P.entry)
  : Lemma (requires TR.root_model u schema model /\
                    A.model schema (TR.booleans u) (SR.root_scalars u) model
                      (AF.family u (S.signature schema)))
          (ensures Root.root_truths u schema model (extra_assertions schema entries))
          (decreases entries) =
  match entries with
  | [] -> ()
  | entry :: rest ->
    if eligible_entry schema entry then lemma_eligible_model u schema model entry;
    lemma_extras_model u schema model rest

let rec lemma_append (u:TR.uninterpreted) (schema:S.checked_schema) (model:TR.interp u schema)
                     (xs ys:list expr)
  : Lemma (Root.root_truths u schema model (xs @ ys) ==
           (Root.root_truths u schema model xs && Root.root_truths u schema model ys))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_append u schema model rest ys

let lemma_augment_truths_model (u:TR.uninterpreted) (schema:S.checked_schema)
                               (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires TR.root_model u schema model /\
                    A.model schema (TR.booleans u) (SR.root_scalars u) model
                      (AF.family u (S.signature schema)))
          (ensures Root.root_truths u schema model (augment schema doc).P.assertions ==
                   Root.root_truths u schema model doc.P.assertions) =
  lemma_extras_model u schema model doc.P.entries;
  lemma_append u schema model doc.P.assertions (extra_assertions schema doc.P.entries)

let lemma_augment_truths (u:TR.uninterpreted) (schema:S.checked_schema)
                         (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires AP.eligible (S.signature schema) max_assertions doc.P.assertions)
          (ensures Root.root_truths u schema
                     (TR.standard u schema (AI.symbols u schema symbols))
                     (augment schema doc).P.assertions ==
                   Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions) =
  let extended = TR.standard u schema (AI.symbols u schema symbols) in
  AI.lemma_root_inhabited u schema symbols;
  AI.lemma_model u schema symbols;
  lemma_augment_truths_model u schema doc extended;
  AP.lemma_eligible_truths u schema symbols max_assertions doc.P.assertions

let lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
                    (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires check schema doc == Root.RootCertified)
          (ensures not (Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions)) =
  let original = TR.standard u schema symbols in
  let extended = TR.standard u schema (AI.symbols u schema symbols) in
  match Root.check_root_document_epsilon schema doc with
  | Root.RootPending _ ->
    if Some? (core_selected schema doc) then (
      AI.lemma_root_inhabited u schema symbols;
      let model = AI.lemma_model u schema symbols in
      let family = AF.family u (S.signature schema) in
      let kernel : SP.array_kernel schema (TR.booleans u) (SR.root_scalars u) extended = {
        SP.family = family;
        SP.model = model;
        SP.supports = lemma_core_array_support u schema
      } in
      Root.lemma_root_check_document_array u schema extended kernel doc;
      AP.lemma_eligible_truths u schema symbols max_assertions doc.P.assertions)
    else (
      AI.lemma_root_inhabited u schema symbols;
      lemma_augment_truths u schema doc symbols;
      Root.lemma_root_certified_epsilon u schema (augment schema doc) extended;
      ())
  | _ ->
    TR.lemma_standard_root u schema symbols;
    Root.lemma_root_certified_epsilon u schema doc original
