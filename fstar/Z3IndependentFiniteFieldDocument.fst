module Z3IndependentFiniteFieldDocument

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module FF = Z3SortedFiniteField
module FR = Z3IndependentFiniteFieldRoot
module Replay = Z3IndependentFiniteFieldReplay
module Witness = Z3IndependentFiniteFieldWitness
module E = FStar.Math.Euclid

let proven_prime (p:int) (evidence:option (int & list int))
  : option (q:int{q == p /\ E.is_prime q}) =
  if Witness.prime_with_evidence p evidence then Some p else None

let eligible_with_prime (p:int) (prime:option (q:int{q == p /\ E.is_prime q}))
                        (entry:P.entry) : bool =
  entry.P.premise_ids = [] &&
  (match entry.P.rule, U.classify_fact entry.P.formula with
  | U.RewriteRule, Some (U.Equal a b) ->
    entry.P.formula = R.mk_eq_expr a b && Replay.rewrite p a b
  | U.Unverified "th-lemma", Some (U.Holds e) -> Replay.clause p e
  | U.FiniteFieldPac c, Some (U.Holds e) ->
    Replay.clause p e ||
    (match prime with Some q -> Replay.pac_for_prime q c e | None -> Replay.pac p c e)
  | _, _ -> false)

let rec extra_assertions (p:int) (prime:option (q:int{q == p /\ E.is_prime q}))
  (entries:list P.entry) : Tot (list expr) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    if eligible_with_prime p prime e then e.P.formula :: extra_assertions p prime rest
    else extra_assertions p prime rest

let rec any_candidate (p:int) (prime:option (q:int{q == p /\ E.is_prime q}))
  (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest -> eligible_with_prime p prime e || any_candidate p prime rest

let has_candidates (p:int) (doc:P.document) : bool = any_candidate p None doc.P.entries

let rec entry_modulus (entries:list P.entry) : Tot (option int) (decreases entries) =
  match entries with
  | [] -> None
  | e :: rest ->
    if e.P.premise_ids <> [] then entry_modulus rest
    else
      (match e.P.rule with
       | U.RewriteRule | U.Unverified "th-lemma" | U.FiniteFieldPac _ ->
         (match FF.find_modulus e.P.formula with
          | Some p -> Some p
          | None -> entry_modulus rest)
       | _ -> entry_modulus rest)

let modulus (doc:P.document) : option int = entry_modulus doc.P.entries

let rec replay_entries_acc (p:int) (prime:option (q:int{q == p /\ E.is_prime q}))
  (entries:list P.entry) (acc:list P.entry)
  : Tot (list P.entry) (decreases entries) =
  match entries with
  | [] -> acc
  | e :: rest ->
    replay_entries_acc p prime rest
      ((if eligible_with_prime p prime e then { e with P.rule = U.Asserted } else e) :: acc)

let augment (p:int) (doc:P.document) : P.document =
  { doc with P.assertions = doc.P.assertions @ extra_assertions p None doc.P.entries;
             P.entries = rev (replay_entries_acc p None doc.P.entries []) }

let has_candidates_with_evidence (p:int) (doc:P.document)
  (evidence:option (int & list int)) : bool =
  any_candidate p (proven_prime p evidence) doc.P.entries

let augment_with_evidence (p:int) (doc:P.document)
  (evidence:option (int & list int)) : P.document =
  let prime = proven_prime p evidence in
  { doc with P.assertions = doc.P.assertions @ extra_assertions p prime doc.P.entries;
             P.entries = rev (replay_entries_acc p prime doc.P.entries []) }

let lemma_eligible (u:TR.uninterpreted) (schema:S.checked_schema)
                   (p:int{p > 1 /\ not (V.datatype_sort (S.signature schema) (FF.ff_sort p))})
                   (symbols:TR.symbols u schema)
                   (prime:option (q:int{q == p /\ E.is_prime q})) (entry:P.entry)
  : Lemma (requires eligible_with_prime p prime entry)
          (ensures Root.root_holds u schema
            (TR.standard u schema (FR.field_symbols u schema p symbols)) entry.P.formula) =
  let root = TR.standard u schema (FR.field_symbols u schema p symbols) in
  FR.lemma_root_inhabited u schema p symbols;
  (match entry.P.rule, U.classify_fact entry.P.formula with
   | U.RewriteRule, Some (U.Equal a b) -> FR.lemma_rewrite u schema p symbols a b
   | U.Unverified "th-lemma", Some (U.Holds e) -> FR.lemma_clause u schema p symbols e
   | U.FiniteFieldPac c, Some (U.Holds e) ->
     if Replay.clause p e then FR.lemma_clause u schema p symbols e
     else (match prime with
           | Some q -> FR.lemma_pac_for_prime u schema q symbols c e
           | None -> FR.lemma_pac u schema p symbols c e)
   | _, _ -> ());
  Root.lemma_holds_agreement u schema root entry.P.formula

let rec lemma_extras (u:TR.uninterpreted) (schema:S.checked_schema)
                     (p:int{p > 1 /\ not (V.datatype_sort (S.signature schema) (FF.ff_sort p))})
                     (symbols:TR.symbols u schema)
                     (prime:option (q:int{q == p /\ E.is_prime q})) (entries:list P.entry)
  : Lemma (Root.root_truths u schema
            (TR.standard u schema (FR.field_symbols u schema p symbols)) (extra_assertions p prime entries))
          (decreases entries) =
  match entries with
  | [] -> assert_norm (extra_assertions p prime [] == [])
  | e :: rest ->
    assert_norm (extra_assertions p prime (e :: rest) ==
      (if eligible_with_prime p prime e then e.P.formula :: extra_assertions p prime rest
       else extra_assertions p prime rest));
    let root = TR.standard u schema (FR.field_symbols u schema p symbols) in
    assert_norm (Root.root_truths u schema root (e.P.formula :: extra_assertions p prime rest) ==
      (Root.root_holds u schema root e.P.formula &&
       Root.root_truths u schema root (extra_assertions p prime rest)));
    if eligible_with_prime p prime e then lemma_eligible u schema p symbols prime e;
    lemma_extras u schema p symbols prime rest

let rec lemma_append (u:TR.uninterpreted) (schema:S.checked_schema) (model:TR.interp u schema)
                     (xs ys:list expr)
  : Lemma (Root.root_truths u schema model (xs @ ys) ==
           (Root.root_truths u schema model xs && Root.root_truths u schema model ys))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_append u schema model rest ys

let lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
                    (p:int{p > 1 /\ not (V.datatype_sort (S.signature schema) (FF.ff_sort p))})
                    (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires Root.check_root_document_epsilon schema (augment p doc) == Root.RootCertified)
          (ensures not (Root.root_truths u schema
            (TR.standard u schema (FR.field_symbols u schema p symbols)) doc.P.assertions)) =
  let root = TR.standard u schema (FR.field_symbols u schema p symbols) in
  FR.lemma_root_inhabited u schema p symbols;
  lemma_extras u schema p symbols None doc.P.entries;
  lemma_append u schema root doc.P.assertions (extra_assertions p None doc.P.entries);
  Root.lemma_root_certified_epsilon u schema (augment p doc) root

let lemma_certified_with_evidence (u:TR.uninterpreted) (schema:S.checked_schema)
                    (p:int{p > 1 /\ not (V.datatype_sort (S.signature schema) (FF.ff_sort p))})
                    (doc:P.document) (symbols:TR.symbols u schema)
                    (evidence:option (int & list int))
  : Lemma (requires Root.check_root_document_epsilon schema
                    (augment_with_evidence p doc evidence) == Root.RootCertified)
          (ensures not (Root.root_truths u schema
            (TR.standard u schema (FR.field_symbols u schema p symbols)) doc.P.assertions)) =
  let root = TR.standard u schema (FR.field_symbols u schema p symbols) in
  let prime = proven_prime p evidence in
  FR.lemma_root_inhabited u schema p symbols;
  lemma_extras u schema p symbols prime doc.P.entries;
  lemma_append u schema root doc.P.assertions (extra_assertions p prime doc.P.entries);
  Root.lemma_root_certified_epsilon u schema (augment_with_evidence p doc evidence) root
