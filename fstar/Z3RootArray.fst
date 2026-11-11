module Z3RootArray

open Z3AstTheory
open FStar.List.Tot
module L = FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module D = Z3Definitions
module TR = Z3TypedRoot
module RD = Z3SortedRootDocument
module P = Z3ProofDocument
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module SP = Z3SortedProof

(* Only closed, supported array identities become additional assertions.
   The theorem below removes them from the refutation's assumptions. *)
let read_over_write (sigma:V.signature) (lhs rhs:expr) : bool =
  match lhs with
  | App select [App store [a; index; v]; index'] ->
    (match get_sort a with
     | ArraySort [d] r ->
       select = TR.select_decl [d] r && store = TR.store_decl [d] r &&
       TR.free sigma (get_sort a) && index = index' && v = rhs
     | _ -> false)
  | _ -> false

let valid (sigma:V.signature) (e:expr) : bool =
  if not (Some? (expression_budget 4096 e)) then false
  else if not (D.scoped [] e && TR.supported_expression sigma e) then false
  else match e with
  | App f [a; b] ->
    TR.classify sigma f = TR.Equality (get_sort a) &&
    (read_over_write sigma a b || read_over_write sigma b a)
  | _ -> false

let lemma_read_over_write (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                          (lhs rhs:expr)
  : Lemma (requires TR.root_model u sch i /\ D.scoped [] lhs /\ D.scoped [] rhs /\
                    read_over_write (S.signature sch) lhs rhs)
          (ensures V.evaluate (S.signature sch) i [] (RD.empty_root u sch) lhs ==
                   V.evaluate (S.signature sch) i [] (RD.empty_root u sch) rhs) =
  let sigma = S.signature sch in
  let rho = RD.empty_root u sch in
  match lhs with
  | App select [App store [a; index; v]; _] ->
    (match get_sort a with
     | ArraySort [d] r ->
       V.lemma_sort_eq (get_sort index) d;
       V.lemma_sort_eq (get_sort v) r;
       TR.lemma_classify_select sigma [d] r;
       TR.lemma_classify_store sigma [d] r;
       TR.lemma_classified_theory sch select;
       TR.lemma_classified_theory sch store;
       let av = V.evaluate sigma i [] rho a in
       let iv = V.evaluate sigma i [] rho index in
       let vv = V.evaluate sigma i [] rho v in
       assert_norm (TR.store_arguments #u #sch [d] r av [iv] vv == [av; iv; vv]);
       assert (V.evaluate_args sigma i [] rho [a; index; v] store.domain == [av; iv; vv]);
       assert (V.evaluate sigma i [] rho (App store [a; index; v]) ==
               i.application store [av; iv; vv]);
       assert (V.evaluate_args sigma i [] rho [App store [a; index; v]; index] select.domain ==
               [i.application store [av; iv; vv]; iv]);
       assert (V.evaluate sigma i [] rho lhs ==
               i.application select [i.application store [av; iv; vv]; iv]);
       TR.law_select_store_same i [d] r av [iv] vv
     | _ -> ())
  | _ -> ()

let lemma_valid (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (e:expr)
  : Lemma (requires TR.root_model u sch i /\ valid (S.signature sch) e)
          (ensures RD.root_holds u sch i e) =
  let sigma = S.signature sch in
  let rho = RD.empty_root u sch in
  match e with
  | App f [a; b] ->
    if read_over_write sigma a b then lemma_read_over_write u sch i a b
    else lemma_read_over_write u sch i b a;
    V.lemma_sort_eq (get_sort b) (get_sort a);
    TR.lemma_classified_theory sch f;
    TR.law_equality i f (get_sort a)
      (V.evaluate sigma i [] rho a) (V.evaluate sigma i [] rho b)
  | _ -> ()

let discharge (sigma:V.signature) (e:P.entry) : bool =
  (e.P.rule = U.RewriteRule || e.P.rule = U.Unverified "th-lemma") &&
  valid sigma e.P.formula

let rec axioms (sigma:V.signature) (entries:list P.entry)
  : Tot (list expr) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    if discharge sigma e then e.P.formula :: axioms sigma rest
    else axioms sigma rest

let rec prepare_entries (sigma:V.signature) (entries:list P.entry)
  : Tot (list P.entry) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    (if discharge sigma e then { e with P.rule = U.Asserted } else e) ::
      prepare_entries sigma rest

let prepare (schema:S.schema) (doc:P.document) : P.document =
  let sigma = S.signature schema in
  { doc with P.assertions = doc.P.assertions @ axioms sigma doc.P.entries;
             P.entries = prepare_entries sigma doc.P.entries }

let finish (schema:S.schema) (doc:P.document) (result:option nat) : RD.root_verdict =
  match result with
  | None -> RD.RootRejected
  | Some n ->
    if n > 0 then RD.RootPending n
    else if RD.root_covered schema doc &&
            TR.supported_expressions (S.signature schema) (RD.dependent_closures schema doc)
    then RD.RootCertified else RD.RootUncovered

let lemma_finish (schema:S.schema) (doc:P.document)
  : Lemma (finish schema doc (SP.check_document_epsilon schema doc) ==
           RD.check_root_document_epsilon schema doc) = ()

let check_document (schema:S.schema) (doc:P.document) : RD.root_verdict =
  if not (RD.root_covered schema doc) then RD.RootUncovered
  else finish schema (prepare schema doc) (SP.check_document_epsilon schema (prepare schema doc))

let check_document_diagnosed (schema:S.schema) (doc:P.document)
  : RD.root_verdict & option P.document_diagnostic =
  if not (RD.root_covered schema doc) then (RD.RootUncovered, None)
  else
    let prepared = prepare schema doc in
    let result, diagnostic = SP.check_document_epsilon_diagnosed schema prepared in
    let verdict = finish schema prepared result in
    (verdict, (if verdict = RD.RootUncovered then None else Some diagnostic))

let lemma_diagnosed (schema:S.schema) (doc:P.document)
  : Lemma (fst (check_document_diagnosed schema doc) == check_document schema doc) = ()

let rec lemma_axioms (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                     (entries:list P.entry)
  : Lemma (requires TR.root_model u sch i)
          (ensures RD.root_truths u sch i (axioms (S.signature sch) entries))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    if discharge (S.signature sch) e then lemma_valid u sch i e.P.formula;
    lemma_axioms u sch i rest

let rec lemma_truths_append (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                           (xs ys:list expr)
  : Lemma (RD.root_truths u sch i (xs @ ys) ==
           (RD.root_truths u sch i xs && RD.root_truths u sch i ys))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_truths_append u sch i rest ys

let lemma_certified (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                    (doc:P.document)
  : Lemma (requires TR.root_model u sch i /\ check_document sch doc == RD.RootCertified)
          (ensures RD.root_covered sch doc /\ not (RD.root_truths u sch i doc.P.assertions)) =
  lemma_finish sch (prepare sch doc);
  RD.lemma_root_certified_epsilon u sch (prepare sch doc) i;
  lemma_axioms u sch i doc.P.entries;
  lemma_truths_append u sch i doc.P.assertions (axioms (S.signature sch) doc.P.entries)

let lemma_standard_certified (u:TR.uninterpreted) (sch:S.checked_schema)
                             (uf:TR.symbols u sch) (doc:P.document)
  : Lemma (requires check_document sch doc == RD.RootCertified)
          (ensures not (RD.root_truths u sch (TR.standard u sch uf) doc.P.assertions)) =
  TR.lemma_standard_root u sch uf;
  lemma_certified u sch (TR.standard u sch uf) doc
