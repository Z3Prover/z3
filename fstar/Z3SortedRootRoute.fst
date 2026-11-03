(*
   Z3SortedRootRoute.fst

   The Root-model theorems and the coverage gate of the opt-in route of
   `Z3SortedRoute` (`verified-dag-v1` on the Sorted/datatype route), the
   counterparts of `Z3SortedRootDocument`'s epsilon section. Like it, this
   module is verification-only: no native route calls anything defined here.

   * `lemma_root_check_document_epsilon_route`: for EVERY root model `i`
     (`TR.root_model u sch i`, R1-R6), if the route's epsilon check accepts
     (`Some 0`), the ORIGINAL assertions are not all root-true in `i`. It is
     `Z3SortedRoute.lemma_check_document_epsilon_route` at the root
     interpretation's choice (`RD.root_choice`) and at the universal and
     existential laws of the SAME `i` (derived from R1, never assumed), with
     the same one consistent choice extension as the default epsilon route
     (`SP.full_extension`), so the original assertions, the generated choice
     equations and dependent closures, the original-input freshness, the
     hypothesis discharge and the root `false` are the default's own checks.
   * `check_root_document_epsilon_route`: the route's decision is reused
     unchanged and coverage only narrows certification. It differs from
     `RD.check_root_document_epsilon` in the one place the route differs from
     the default: the scope guard of the certificates the replay consumes.
     Coverage reads two certificates per consumed quantifier introduction: the
     DOCUMENT's (whose inner Skolem steps the elaboration collects and whose
     entry formulas are covered as by default) and the COMPANION's (the
     prepared certificate the route replays: every entry formula and binder
     sort covered, and the route's own scope guard passes, `route_scoped`,
     which is the guard `NRC.replay_dag` runs). A consumed certificate without
     a prepared companion is not certified (`RootUncovered`), whatever
     else decides the document.
   * `lemma_root_certified_epsilon_route`: a `RootCertified` verdict implies
     the schema is supported, the original assertions, generated equations
     and dependent closures are typed and covered, and some ORIGINAL assertion
     is root-false in every root model; `lemma_certified_companion_node` and
     `lemma_certified_companion_sorts` give the coverage of the terms of the
     companion the route reads.
   * `lemma_root_read_view_epsilon_route`: the decision and the gate read only
     the read view of the document (`RD.read_view`): the native tables and
     every rule payload other than the quantifier-instantiation arguments, the
     Farkas coefficients, the Skolemization label and the binder
     certificates never change them. The companions are an input of the route,
     not of the document, and enter the decision and the gate unchanged.
*)
module Z3SortedRootRoute

open Z3AstTheory
open Z3ValueTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module D = Z3Definitions
module L = FStar.List.Tot
module I = Z3ProofIndex
module TR = Z3TypedRoot
module T = Z3SortedSemantics
module SR = Z3SortedRoot
module SP = Z3SortedProof
module P = Z3ProofDocument
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module E = Z3SortedSkolem
module SK = Z3Skolemization
module NR = Z3NnfReplay
module NRC = Z3NnfReplayChecked
module RD = Z3SortedRootDocument
module SRt = Z3SortedRoute
module DD = Z3DagDocument
module DG = Z3DagGuard
module DS = Z3SortedDependentSkolem

(* ---------------------------------------------------------------------- *)
(* 1. The document theorem under every root model                           *)
(* ---------------------------------------------------------------------- *)

let lemma_root_check_document_epsilon_route (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                                            (cs:DD.companions) (doc:P.document)
  : Lemma (requires TR.root_model u sch i /\ SRt.check_document_epsilon_route cs sch doc == Some 0)
          (ensures not (RD.root_truths u sch i doc.P.assertions)) =
  RD.lemma_forall_model u sch i;
  RD.lemma_exists_model u sch i;
  SRt.lemma_check_document_epsilon_route sch (TR.booleans u) (SR.root_scalars u) (RD.root_choice u sch) i cs doc;
  RD.lemma_truths_agreement u sch i doc.P.assertions

(* ---------------------------------------------------------------------- *)
(* 2. Coverage of what the route reads                                      *)
(* ---------------------------------------------------------------------- *)

(* The scope guard the route runs on a prepared certificate (`NRC.replay_dag`):
   the classification of the certificate's own entries (the cache the replay
   builds) and the DAG guard at the budget of the mode. *)
let route_scoped (p:DD.prepared) : bool =
  match NR.judgments_of p.DD.pcert.U.binder_entries I.Empty 0 with
  | None -> false
  | Some cache ->
    DG.DagChecked? (DG.dag_guard (DD.dag_budget (U.count_cells 0 p.DD.pcert.U.binder_entries))
                      p.DD.pgraph p.DD.pcert cache p.DD.phandles)

(* The terms of an entry the document side reads: its formula, the
   instantiation arguments and, of a consumed certificate, every entry formula
   and binder sort (the elaboration collects the inner Skolem steps of the
   document's own certificate). *)
let entry_supported (sigma:V.signature) (e:P.entry) : bool =
  D.scoped [] e.P.formula && TR.supported_expression sigma e.P.formula &&
  D.scoped_args [] (RD.rule_terms e.P.rule) && TR.supported_expressions sigma (RD.rule_terms e.P.rule) &&
  (match e.P.rule with
   | U.QuantifierIntroduction c -> not (NR.consumed_root c) || RD.binder_entries_covered sigma c.U.binder_entries
   | _ -> true)

let rec entries_supported (sigma:V.signature) (es:list P.entry) : Tot bool (decreases es) =
  match es with [] -> true | e :: rest -> entry_supported sigma e && entries_supported sigma rest

(* The companion side: the prepared certificate the route replays, covered
   and scoped by the route's guard. A consumed certificate without one is
   not covered. *)
let companion_covered (sigma:V.signature) (prep:DD.preparation) (r:U.rule) : bool =
  match r with
  | U.QuantifierIntroduction c ->
    not (NR.consumed_root c) ||
    (match prep with
     | DD.Ready p _ -> RD.binder_entries_covered sigma p.DD.pcert.U.binder_entries && route_scoped p
     | DD.Unready _ _ -> false)
  | _ -> true

let entry_covered_route (sigma:V.signature) (prep:DD.preparation) (e:P.entry) : bool =
  entry_supported sigma e && companion_covered sigma prep e.P.rule

(* The entries from index `i`: the entry at index `n` of the list has the
   preparation recorded for index `i + n`. *)
let rec entries_covered_route (sigma:V.signature) (cs:DD.companions) (i:nat) (es:list P.entry)
  : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: rest -> entry_covered_route sigma (DD.preparation_of cs i) e && entries_covered_route sigma cs (i + 1) rest

let root_covered_route (schema:S.schema) (cs:DD.companions) (doc:P.document) : bool =
  TR.supported schema &&
  D.scoped_args [] doc.P.assertions &&
  TR.supported_expressions (S.signature schema) doc.P.assertions &&
  entries_covered_route (S.signature schema) cs 0 doc.P.entries

(* The gate: the route's decision is reused unchanged; coverage only narrows
   certification (an uncovered document is `RootUncovered`, never a rejected
   proof). *)
let check_root_document_epsilon_route (schema:S.schema) (cs:DD.companions) (doc:P.document) : RD.root_verdict =
  match SRt.check_document_epsilon_route cs schema doc with
  | None -> RD.RootRejected
  | Some n ->
    if n > 0 then RD.RootPending n
    else if root_covered_route schema cs doc && TR.supported_expressions (S.signature schema) (RD.dependent_closures schema doc)
    then RD.RootCertified
    else RD.RootUncovered

let rec lemma_covered_route_supported (sigma:V.signature) (cs:DD.companions) (i:nat) (es:list P.entry)
  : Lemma (requires entries_covered_route sigma cs i es) (ensures entries_supported sigma es) (decreases es) =
  match es with [] -> () | _ :: rest -> lemma_covered_route_supported sigma cs (i + 1) rest

let rec lemma_covered_route_index (sigma:V.signature) (cs:DD.companions) (i:nat) (es:list P.entry) (n:nat)
  : Lemma (requires entries_covered_route sigma cs i es /\ n < L.length es)
          (ensures entry_covered_route sigma (DD.preparation_of cs (i + n)) (L.index es n))
          (decreases es) =
  match es with
  | _ :: rest -> if n > 0 then lemma_covered_route_index sigma cs (i + 1) rest (n - 1)
  | [] -> ()

(* The generated choice equations are built from covered entry formulas. *)
let lemma_equation_supported (s:S.checked_schema) (e:P.entry) (d:E.definition s) (a b:expr)
  : Lemma (requires entry_supported (S.signature s) e /\
                    U.classify_fact e.P.formula == Some (U.Observational a b) /\
                    E.definition_of s a b == Some d)
          (ensures D.scoped [] (R.mk_eq_expr a b) /\
                   TR.supported_expression (S.signature s) (R.mk_eq_expr a b)) =
  E.lemma_definition_parts s a b d;
  RD.lemma_oeq_sides (S.signature s) e.P.formula a b;
  RD.lemma_boolean_equation_covered (S.signature s) a b

let rec lemma_epsilon_equations_supported (s:S.checked_schema) (ds:list (E.definition s)) (es:list P.entry)
  : Lemma (requires entries_supported (S.signature s) es)
          (ensures D.scoped_args [] (SP.epsilon_equations s ds es) /\
                   TR.supported_expressions (S.signature s) (SP.epsilon_equations s ds es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    lemma_epsilon_equations_supported s ds rest;
    (match SP.nnf_certificate e with
     | Some c -> RD.lemma_inner_equations_covered s ds c.U.binder_entries (SP.epsilon_equations s ds rest)
     | None -> ());
    if SP.epsilon_entry s ds e then (
      match SP.epsilon_definition s e, U.classify_fact e.P.formula with
      | Some d, Some (U.Observational a b) -> lemma_equation_supported s e d a b
      | _, _ -> ())

(* An accepted route document has typed, Boolean original assertions: the
   route's own check tests them. *)
let lemma_route_assertions_typed (s:S.checked_schema) (cs:DD.companions) (doc:P.document)
  : Lemma (requires Some? (SRt.check_document_route cs s doc)) (ensures RD.typed_assertions doc.P.assertions) =
  RD.lemma_typed_assertions s doc.P.assertions

let lemma_route_assertions_typed_epsilon (schema:S.schema) (cs:DD.companions) (doc:P.document)
  : Lemma (requires Some? (SRt.check_document_epsilon_route cs schema doc))
          (ensures RD.typed_assertions doc.P.assertions) =
  let ds = SP.epsilon_context schema doc in
  let dds = SP.dependent_context schema doc ds in
  let closed = SP.elaborate_epsilon schema ds doc in
  lemma_route_assertions_typed schema cs (SP.elaborate_full schema doc);
  if dds <> [] then RD.lemma_typed_prefix closed.P.assertions (DS.closures schema dds);
  if ds <> [] then RD.lemma_typed_prefix doc.P.assertions (SP.epsilon_equations schema ds doc.P.entries)

(* ---------------------------------------------------------------------- *)
(* 3. The certified theorem                                                 *)
(* ---------------------------------------------------------------------- *)

let lemma_root_certified_epsilon_route (u:TR.uninterpreted) (sch:S.checked_schema) (cs:DD.companions)
                                       (doc:P.document) (i:TR.interp u sch)
  : Lemma (requires check_root_document_epsilon_route sch cs doc == RD.RootCertified /\ TR.root_model u sch i)
          (ensures TR.supported sch /\ root_covered_route sch cs doc /\ RD.typed_assertions doc.P.assertions /\
                   D.scoped_args [] (SP.epsilon_equations sch (SP.epsilon_context sch doc) doc.P.entries) /\
                   TR.supported_expressions (S.signature sch)
                     (SP.epsilon_equations sch (SP.epsilon_context sch doc) doc.P.entries) /\
                   D.scoped_args [] (RD.dependent_closures sch doc) /\
                   TR.supported_expressions (S.signature sch) (RD.dependent_closures sch doc) /\
                   not (RD.root_truths u sch i doc.P.assertions) /\
                   (exists (a:expr). L.mem a doc.P.assertions /\ D.scoped [] a /\ get_sort a == bool_sort /\
                                     not (RD.root_holds u sch i a))) =
  lemma_route_assertions_typed_epsilon sch cs doc;
  lemma_covered_route_supported (S.signature sch) cs 0 doc.P.entries;
  lemma_epsilon_equations_supported sch (SP.epsilon_context sch doc) doc.P.entries;
  RD.lemma_closures_scoped sch (SP.dependent_context sch doc (SP.epsilon_context sch doc));
  lemma_root_check_document_epsilon_route u sch i cs doc;
  RD.lemma_false_member u sch i doc.P.assertions

(* Unconditional standard corollary of the route gate (every u, uf). *)
let lemma_standard_certified_epsilon_route (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
                                           (cs:DD.companions) (doc:P.document)
  : Lemma (requires check_root_document_epsilon_route sch cs doc == RD.RootCertified)
          (ensures TR.root_model u sch (TR.standard u sch uf) /\
                   not (RD.root_truths u sch (TR.standard u sch uf) doc.P.assertions)) =
  TR.lemma_standard_root u sch uf;
  lemma_root_certified_epsilon_route u sch cs doc (TR.standard u sch uf)

(* The terms of a companion the route reads, in a certified document: every
   node of every entry formula of the prepared certificate recorded for a
   consumed quantifier introduction is supported and law-ready, and the
   route's guard passes on it. *)
let lemma_certified_companion_node (schema:S.schema) (cs:DD.companions) (doc:P.document) (n:nat)
                                   (c:U.binder_certificate) (p:DD.prepared) (used:(nat & nat))
                                   (b:U.binder_entry) (x:expr)
  : Lemma (requires check_root_document_epsilon_route schema cs doc == RD.RootCertified /\
                    n < L.length doc.P.entries /\
                    (L.index doc.P.entries n).P.rule == U.QuantifierIntroduction c /\ NR.consumed_root c /\
                    DD.preparation_of cs n == DD.Ready p used /\
                    L.mem b p.DD.pcert.U.binder_entries /\ TR.occurs x b.U.binder_formula)
          (ensures route_scoped p /\
                   TR.supported_expression (S.signature schema) x /\ TR.node_ready (S.signature schema) x) =
  lemma_covered_route_index (S.signature schema) cs 0 doc.P.entries n;
  RD.lemma_binder_entry_covered (S.signature schema) p.DD.pcert.U.binder_entries b;
  TR.lemma_document_node schema [b.U.binder_formula] b.U.binder_formula x

(* The binder sorts of the companion's entries are supported too. *)
let lemma_certified_companion_sorts (schema:S.schema) (cs:DD.companions) (doc:P.document) (n:nat)
                                    (c:U.binder_certificate) (p:DD.prepared) (used:(nat & nat))
                                    (b:U.binder_entry) (ss:list sort)
  : Lemma (requires check_root_document_epsilon_route schema cs doc == RD.RootCertified /\
                    n < L.length doc.P.entries /\
                    (L.index doc.P.entries n).P.rule == U.QuantifierIntroduction c /\ NR.consumed_root c /\
                    DD.preparation_of cs n == DD.Ready p used /\
                    L.mem b p.DD.pcert.U.binder_entries /\ b.U.binder_sorts == Some ss)
          (ensures TR.supported_sorts (S.signature schema) ss) =
  lemma_covered_route_index (S.signature schema) cs 0 doc.P.entries n;
  RD.lemma_binder_sorts_covered (S.signature schema) p.DD.pcert.U.binder_entries b ss

(* A consumed quantifier introduction without a prepared companion is not
   certified: the gate is `RootUncovered` (or the document is pending or
   rejected). *)
let lemma_unprepared_not_certified (schema:S.schema) (cs:DD.companions) (doc:P.document) (n:nat)
                                   (c:U.binder_certificate) (why:DD.unprepared_reason) (used:option (nat & nat))
  : Lemma (requires n < L.length doc.P.entries /\
                    (L.index doc.P.entries n).P.rule == U.QuantifierIntroduction c /\ NR.consumed_root c /\
                    DD.preparation_of cs n == DD.Unready why used)
          (ensures check_root_document_epsilon_route schema cs doc =!= RD.RootCertified) =
  if SRt.check_document_epsilon_route cs schema doc = Some 0 &&
     root_covered_route schema cs doc then
    lemma_covered_route_index (S.signature schema) cs 0 doc.P.entries n

(* ---------------------------------------------------------------------- *)
(* 4. The route reads only the read view                                    *)
(* ---------------------------------------------------------------------- *)

let lemma_node_shape_with (s:S.checked_schema) (assertions:list expr) (node:U.proof_node) (nnf:NR.verdict)
  : Lemma (SRt.check_node_with s assertions node nnf ==
           SRt.check_node_with s assertions ({ node with U.kind = RD.rule_shape node.U.kind }) nnf) =
  match node.U.kind with
  | U.Asserted | U.Hypothesis | U.LemmaRule | U.PullQuantifier | U.QuantifierInstantiation _
  | U.ArithmeticFarkas _ | U.Skolemization | U.QuantifierIntroduction _ -> ()
  | _ ->
    let node' = { node with U.kind = RD.rule_shape node.U.kind } in
    assert (not (SP.arithmetic_farkas node) /\ not (SP.arithmetic_farkas node'));
    assert (not (SP.lemma_step node) /\ not (SP.lemma_step node'));
    assert (not (SP.quantifier_instantiation node) /\ not (SP.quantifier_instantiation node'));
    assert (not (SP.quantifier_flattening node) /\ not (SP.quantifier_flattening node'))

let lemma_node_shape_route (s:S.checked_schema) (r:NRC.route) (assertions:list expr) (node:U.proof_node)
  : Lemma (SRt.check_node_route s r assertions node ==
           SRt.check_node_route s r assertions ({ node with U.kind = RD.rule_shape node.U.kind })) =
  let node' = { node with U.kind = RD.rule_shape node.U.kind } in
  assert ((SRt.nnf_result r assertions node).NRC.verdict == (SRt.nnf_result r assertions node').NRC.verdict);
  lemma_node_shape_with s assertions node (SRt.nnf_result r assertions node).NRC.verdict

let rec lemma_entries_read_view_route (cs:DD.companions) (s:S.checked_schema) (assertions:list expr)
                                      (cache:I.index_tree U.checked_fact) (next pending:nat)
                                      (entries:list P.entry)
  : Lemma (ensures SRt.check_entries_route cs s assertions cache next pending entries ==
                   SRt.check_entries_route cs s assertions cache next pending (L.map RD.shape_entry entries))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    (match SP.prepare_entry s cache e with
     | None -> ()
     | Some node ->
       assert (SP.prepare_entry s cache (RD.shape_entry e) ==
               Some ({ node with U.kind = RD.rule_shape node.U.kind }));
       lemma_node_shape_route s (SRt.entry_route cs next) assertions node;
       (match SRt.check_node_route s (SRt.entry_route cs next) assertions node with
        | None -> ()
        | Some (fact, local) ->
          lemma_entries_read_view_route cs s assertions (I.index_put cache next fact) (next + 1)
            (pending + local) rest))

let lemma_document_read_view_route (cs:DD.companions) (schema:S.schema) (doc:P.document)
  : Lemma (SRt.check_document_route cs schema doc == SRt.check_document_route cs schema (RD.read_view doc)) =
  if S.valid schema then lemma_entries_read_view_route cs schema doc.P.assertions I.Empty 0 0 doc.P.entries

(* The elaboration of the read view is the read view of the elaboration. *)
let lemma_elaborate_view (schema:S.schema) (doc:P.document)
  : Lemma (requires S.valid schema)
          (ensures SP.elaborate_full schema (RD.read_view doc) == RD.read_view (SP.elaborate_full schema doc)) =
  RD.lemma_collect_view schema [] doc.P.entries;
  RD.lemma_merged_view schema [] doc.P.entries;
  RD.lemma_dependents_view schema [] doc.P.entries;
  let ds = SP.epsilon_context schema doc in
  RD.lemma_certified_context_view schema doc (SP.collect_merged schema [] doc.P.entries);
  RD.lemma_certified_context_view schema doc (SP.collect_epsilon schema [] doc.P.entries);
  assert (SP.epsilon_context schema (RD.read_view doc) == ds);
  let dds = SP.dependent_context schema doc ds in
  assert (SP.dependent_context schema (RD.read_view doc) ds == dds);
  RD.lemma_equations_view schema ds doc.P.entries;
  RD.lemma_epsilon_entries_view schema ds doc.P.entries;
  assert (SP.elaborate_epsilon schema ds (RD.read_view doc) == RD.read_view (SP.elaborate_epsilon schema ds doc));
  assert (SP.elaborate_full schema (RD.read_view doc) == RD.read_view (SP.elaborate_full schema doc))

let lemma_document_read_view_epsilon_route (cs:DD.companions) (schema:S.schema) (doc:P.document)
  : Lemma (SRt.check_document_epsilon_route cs schema doc ==
           SRt.check_document_epsilon_route cs schema (RD.read_view doc)) =
  if S.valid schema then (
    lemma_elaborate_view schema doc;
    lemma_document_read_view_route cs schema (SP.elaborate_full schema doc))

let lemma_entry_covered_view (sigma:V.signature) (prep:DD.preparation) (e:P.entry)
  : Lemma (entry_covered_route sigma prep (RD.shape_entry e) == entry_covered_route sigma prep e) =
  match e.P.rule with
  | U.Asserted | U.Hypothesis | U.LemmaRule | U.PullQuantifier | U.QuantifierInstantiation _
  | U.ArithmeticFarkas _ | U.Skolemization | U.QuantifierIntroduction _ -> ()
  | _ -> ()

let rec lemma_entries_covered_route_view (sigma:V.signature) (cs:DD.companions) (i:nat) (es:list P.entry)
  : Lemma (ensures entries_covered_route sigma cs i (L.map RD.shape_entry es) == entries_covered_route sigma cs i es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    lemma_entry_covered_view sigma (DD.preparation_of cs i) e;
    lemma_entries_covered_route_view sigma cs (i + 1) rest

let lemma_root_read_view_epsilon_route (cs:DD.companions) (schema:S.schema) (doc:P.document)
  : Lemma (check_root_document_epsilon_route schema cs doc ==
           check_root_document_epsilon_route schema cs (RD.read_view doc)) =
  lemma_document_read_view_epsilon_route cs schema doc;
  RD.lemma_document_read_view_epsilon schema doc;
  lemma_entries_covered_route_view (S.signature schema) cs 0 doc.P.entries
