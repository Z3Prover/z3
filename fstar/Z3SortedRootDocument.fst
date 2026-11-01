module Z3SortedRootDocument

(* G2 document slice (PROTOTYPE, branch fstar-typed-root-prototype-20261030;
   not in the default route, no executable checker change, no route calls
   anything defined here).

   1. Derives the quantifier hypotheses of Z3SortedQuantifier (forall_model,
      forall_elimination_model) from R1 of ONE root model `i`
      (TR.root_model u sch i), never by assuming them.
   2./3./4. Restates the node and document theorems of the ACTUAL checker
      Z3SortedProof (check_node_cached, check_document and the existing
      induction lemma_check_document) for EVERY root model i, in i's own
      root truth: the Sorted interpretation over the root scalars on top of
      i agrees with i (Z3SortedRoot.lemma_truth_agreement).
   5. L2: a pure root-specific gate `check_root_document` that reuses the
      unchanged Sorted decision and only NARROWS certification to the
      covered fragment (supported schema; every original assertion, entry
      formula and instantiation argument typed by D.scoped AND covered by
      TR.supported_expression), plus the certified document theorem and its
      unconditional standard corollary (every u, every uf).

   Model class: every i with TR.root_model u sch i over a checked schema
   (non-empty for every u and schema, TR.lemma_root_inhabited). The Sorted
   layers interpret the Boolean core, Int numerals/+/*/-/comparisons and
   the datatype operations; on root models these ARE R2/R4/R5/R6
   (Z3SortedRoot). Every other operator (Real arithmetic, select/store/
   lambda, distinct, div/mod, BV/FF/Seq/FP, ...) is passed to i untouched,
   so the checker reasons about it only by congruence (it is a free symbol
   of the Sorted proof); no theory law is used for it.

   Dependency DAG: Z3SortedRootDocument -> {Z3SortedRoot, Z3SortedProof,
   Z3SortedQuantifier, Z3TypedRoot, ...}; nothing depends on it. *)

open Z3AstTheory
open Z3ValueTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module D = Z3Definitions
module L = FStar.List.Tot
module TR = Z3TypedRoot
module T = Z3SortedSemantics
module SR = Z3SortedRoot
module Q = Z3SortedQuantifier
module SP = Z3SortedProof
module P = Z3ProofDocument
module U = Z3UnifiedProof

(* ---------------------------------------------------------------------- *)
(* 1. Quantifier hypotheses of Z3SortedQuantifier, from R1                  *)
(* ---------------------------------------------------------------------- *)

(* R1 (forall_case) over the Sorted truth: the Sorted Boolean read-back of a
   root value IS the root truth (SR.lemma_truth_value). *)
let lemma_forall_case (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                      (bound:list sort) (body:TR.body_of u sch bound bool_sort)
  : Lemma (requires TR.root_model u sch i)
          (ensures T.truth_value sch (TR.booleans u) (i.V.quantification Forall_k bound bool_sort body) <==>
                   (forall (vs:TR.targuments u sch (L.rev bound)). T.truth_value sch (TR.booleans u) (body vs))) =
  assert (TR.forall_case u sch i bound body);
  SR.lemma_truth_value sch (i.V.quantification Forall_k bound bool_sort body);
  let pointwise (vs:TR.targuments u sch (L.rev bound))
    : Lemma (T.truth_value sch (TR.booleans u) (body vs) == TR.truth sch (body vs)) =
    SR.lemma_truth_value sch (body vs) in
  FStar.Classical.forall_intro pointwise

(* One case of Q.forall_model (Q's named forall_case, at Q's named body
   type), from R1 at the same binder list and body. *)
let lemma_q_forall_case (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                        (bound:list sort) (body:Q.ghost_body (TR.carrier u) sch bound)
  : Lemma (requires TR.root_model u sch i)
          (ensures Q.forall_case sch (TR.booleans u) i bound body) =
  lemma_forall_case u sch i bound body

(* The universal semantics needed by flattening (Q.lemma_check_flatten),
   for EVERY binder list and EVERY ghost body. *)
let lemma_forall_model (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
  : Lemma (requires TR.root_model u sch i)
          (ensures Q.forall_model sch (TR.booleans u) i) =
  introduce forall (bound:list sort) (body:Q.ghost_body (TR.carrier u) sch bound).
    Q.forall_case sch (TR.booleans u) i bound body
  with lemma_q_forall_case u sch i bound body

(* The elimination semantics needed by instantiation (Q.lemma_check): the
   same R1 fact read in one direction, for every typed argument list. *)
let lemma_q_elimination_case (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                             (bound:list sort) (body:Q.ghost_body (TR.carrier u) sch bound)
                             (vs:V.arguments (TR.carrier u) (S.signature sch) (L.rev bound))
  : Lemma (requires TR.root_model u sch i)
          (ensures Q.elimination_case sch (TR.booleans u) i bound body vs) =
  lemma_forall_case u sch i bound body

let lemma_forall_elimination_model (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
  : Lemma (requires TR.root_model u sch i)
          (ensures Q.forall_elimination_model sch (TR.booleans u) i) =
  introduce forall (bound:list sort) (body:Q.ghost_body (TR.carrier u) sch bound)
                   (vs:V.arguments (TR.carrier u) (S.signature sch) (L.rev bound)).
    Q.elimination_case sch (TR.booleans u) i bound body vs
  with lemma_q_elimination_case u sch i bound body vs

(* ---------------------------------------------------------------------- *)
(* 2. Root truth of the original assertions                                 *)
(* ---------------------------------------------------------------------- *)

let empty_root (u:TR.uninterpreted) (sch:S.checked_schema) : V.environment (TR.carrier u) (S.signature sch) [] =
  T.empty_environment #(TR.carrier u) (S.signature sch)

(* The ROOT truth of a closed Boolean expression in the root interpretation
   i itself (V.evaluate over i, no Sorted layer). *)
let root_holds (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (e:expr) : GTot bool =
  D.scoped [] e && get_sort e = bool_sort &&
  TR.truth sch (V.evaluate (S.signature sch) i [] (empty_root u sch) e)

let rec root_truths (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (es:list expr)
  : GTot bool (decreases es) =
  match es with [] -> true | e :: rest -> root_holds u sch i e && root_truths u sch i rest

(* The Sorted truth over the root scalars on top of i IS the root truth in i. *)
let lemma_holds_agreement (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (e:expr)
  : Lemma (requires TR.root_model u sch i)
          (ensures T.truth sch (TR.booleans u) (SR.root_scalars u) i e == root_holds u sch i e) =
  if D.scoped [] e && get_sort e = bool_sort then
    SR.lemma_truth_agreement u sch i [] (empty_root u sch) e

let rec lemma_truths_agreement (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (es:list expr)
  : Lemma (requires TR.root_model u sch i)
          (ensures T.truths sch (TR.booleans u) (SR.root_scalars u) i es == root_truths u sch i es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest -> lemma_holds_agreement u sch i e; lemma_truths_agreement u sch i rest

(* ---------------------------------------------------------------------- *)
(* 3. The node theorem: one checked rule application under ONE root model  *)
(* ---------------------------------------------------------------------- *)

(* Every rule path of Z3SortedProof.check_node_cached that reports no
   pending obligation (Asserted, Hypothesis, quantifier instantiation,
   flattening, lemma discharge, and the propositional, equality,
   congruence, Int-arithmetic and datatype consequence kernels) preserves
   the truth of the checked fact in the Sorted interpretation over i. Its
   quantifier hypotheses are DERIVED from R1 (section 1). This is the NODE
   theorem; the document theorem (section 4) is its induction over the
   actual DAG. *)
let lemma_root_check_node (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                          (assertions:list expr) (node:U.proof_node) (fact:U.checked_fact)
  : Lemma (requires TR.root_model u sch i /\
                    T.truths sch (TR.booleans u) (SR.root_scalars u) i assertions /\
                    SP.facts_hold sch (TR.booleans u) (SR.root_scalars u) i node.U.premises /\
                    SP.facts_valid sch node.U.premises /\
                    SP.check_node_cached sch assertions node == Some (fact, 0))
          (ensures SP.fact_holds sch (TR.booleans u) (SR.root_scalars u) i fact) =
  lemma_forall_model u sch i;
  lemma_forall_elimination_model u sch i;
  SP.lemma_check_node_cached sch (TR.booleans u) (SR.root_scalars u) i assertions node fact

(* ---------------------------------------------------------------------- *)
(* 4. The document theorem over the ACTUAL checker (Z3SortedProof)          *)
(* ---------------------------------------------------------------------- *)

(* For EVERY root model i (R1-R6) over a checked schema: if the actual
   Z3SortedProof.check_document (the real DAG walk: original assertions,
   entries in order, premises looked up among EARLIER entries only, the
   root fact `false` with no open hypothesis, total pending count 0)
   returns Some 0, then the original assertions are not all true in i.
   Proved by the existing induction SP.lemma_check_document; its only model
   hypotheses (forall semantics) are derived from R1; no cache or body
   truth is assumed. *)
let lemma_root_check_document (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
                              (doc:P.document)
  : Lemma (requires TR.root_model u sch i /\ SP.check_document sch doc == Some 0)
          (ensures not (root_truths u sch i doc.P.assertions)) =
  lemma_forall_model u sch i;
  lemma_forall_elimination_model u sch i;
  SP.lemma_check_document sch (TR.booleans u) (SR.root_scalars u) i doc;
  lemma_truths_agreement u sch i doc.P.assertions

(* ---------------------------------------------------------------------- *)
(* 5. L2: the root-specific document gate (pure, OFF the default route)     *)
(* ---------------------------------------------------------------------- *)

(* --- What Z3SortedProof actually READS of a document (proved, not
   assumed). Z3SortedProof.check_document reads the schema, the original
   assertions, the root index and, for each entry, its formula, its
   premise ids and its rule; there is no definition expansion and no
   normalization of entry terms before the kernels (SP.prepare_entry_from
   only checks D.scoped/in_context of e.formula and classifies it). Of the
   rule it distinguishes exactly six shapes (check_node_cached:
   Asserted, Hypothesis, LemmaRule, PullQuantifier, QuantifierInstantiation
   with its argument list, and ArithmeticFarkas WITH its coefficient list,
   which SP.arithmetic_farkas replays); the epsilon route
   (check_document_epsilon, section 6) also distinguishes Skolemization.
   Every other rule, with every other payload (Gomory, PAC, binder
   certificates, rule names), is judged identically. The read view KEEPS
   the Farkas coefficients and the Skolemization label (erasing them would
   change the decision); lemma_document_read_view proves that the decision
   equals the decision on the read view, which drops the
   declarations/expressions tables and every other payload. So the covered
   terms below (assertions, entry formulas, instantiation arguments) are
   all DOCUMENT terms the checker reads; the Farkas coefficients are
   numbers, not terms. The checker also builds internal terms of its own
   (the canonical false, equality and Boolean wrappers, field equalities and the
   instances of instantiation); those are not gated, and need not be: the
   falsity proof above (lemma_root_check_document) holds in every root
   model for every document with Some 0, covered or not. Coverage only
   restricts which certified documents are read as SMT queries; it is not
   used by the abstract root-class falsity proof. *)
let rule_shape (r:U.rule) : U.rule =
  match r with
  | U.Asserted | U.Hypothesis | U.LemmaRule | U.PullQuantifier | U.QuantifierInstantiation _
  | U.ArithmeticFarkas _ | U.Skolemization -> r
  | _ -> U.Unverified "payload-erased"

let shape_entry (e:P.entry) : P.entry = { e with P.rule = rule_shape e.P.rule }

let read_view (doc:P.document) : P.document = {
  P.declarations = []; P.expressions = []; P.assertions = doc.P.assertions;
  P.entries = L.map shape_entry doc.P.entries; P.root = doc.P.root;
}

let lemma_node_shape (s:S.checked_schema) (assertions:list expr) (node:U.proof_node)
  : Lemma (SP.check_node_cached s assertions node ==
           SP.check_node_cached s assertions ({ node with U.kind = rule_shape node.U.kind })) =
  match node.U.kind with
  | U.Asserted | U.Hypothesis | U.LemmaRule | U.PullQuantifier | U.QuantifierInstantiation _
  | U.ArithmeticFarkas _ | U.Skolemization -> ()
  | _ ->
    let node' = { node with U.kind = rule_shape node.U.kind } in
    assert (not (SP.arithmetic_farkas node) /\ not (SP.arithmetic_farkas node'));
    assert (not (SP.lemma_step node) /\ not (SP.lemma_step node'));
    assert (not (SP.quantifier_instantiation node) /\ not (SP.quantifier_instantiation node'));
    assert (not (SP.quantifier_flattening node) /\ not (SP.quantifier_flattening node'))

let rec lemma_entries_read_view (s:S.checked_schema) (assertions:list expr)
                                (cache:Z3ProofIndex.index_tree U.checked_fact) (next pending:nat)
                                (entries:list P.entry)
  : Lemma (ensures SP.check_entries s assertions cache next pending entries ==
                   SP.check_entries s assertions cache next pending (L.map shape_entry entries))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    (match SP.prepare_entry s cache e with
     | None -> ()
     | Some node ->
       assert (SP.prepare_entry s cache (shape_entry e) ==
               Some ({ node with U.kind = rule_shape node.U.kind }));
       lemma_node_shape s assertions node;
       (match SP.check_node_cached s assertions node with
        | None -> ()
        | Some (fact, local) ->
          lemma_entries_read_view s assertions (Z3ProofIndex.index_put cache next fact) (next + 1)
            (pending + local) rest))

let lemma_document_read_view (schema:S.schema) (doc:P.document)
  : Lemma (SP.check_document schema doc == SP.check_document schema (read_view doc)) =
  if S.valid schema then lemma_entries_read_view schema doc.P.assertions Z3ProofIndex.Empty 0 0 doc.P.entries

(* The terms carried by a rule shape: only the instantiation arguments. *)
let rule_terms (r:U.rule) : list expr =
  match r with U.QuantifierInstantiation args -> args | _ -> []

(* TYPING (D.scoped) and COVERAGE (TR.supported_expression: every sort of
   every node, at every depth, is supported and SMT-shaped, and an array
   sort is datatype-free with at least one index) are checked SEPARATELY on
   the actual entry data, never on the native `expressions` table. *)
let entry_covered (sigma:V.signature) (e:P.entry) : bool =
  D.scoped [] e.P.formula && TR.supported_expression sigma e.P.formula &&
  D.scoped_args [] (rule_terms e.P.rule) && TR.supported_expressions sigma (rule_terms e.P.rule)

let rec entries_covered (sigma:V.signature) (es:list P.entry) : Tot bool (decreases es) =
  match es with [] -> true | e :: rest -> entry_covered sigma e && entries_covered sigma rest

(* The covered fragment of a document: a supported schema (S.valid plus the
   root's own schema checks), and every original assertion, every entry
   formula and every instantiation argument typed and covered. Only the
   assertions are needed for the SMT reading of the conclusion; the entry
   and argument checks are deliberately conservative, so that a certified
   proof never reads a DOCUMENT term outside the covered fragment (terms the
   kernels build internally are not gated, see above). *)
let root_covered (schema:S.schema) (doc:P.document) : bool =
  TR.supported schema &&
  D.scoped_args [] doc.P.assertions &&
  TR.supported_expressions (S.signature schema) doc.P.assertions &&
  entries_covered (S.signature schema) doc.P.entries

type root_verdict =
  | RootCertified                            (* check_document = Some 0 and root_covered *)
  | RootUncovered                            (* check_document = Some 0, outside the covered fragment *)
  | RootPending : count:pos -> root_verdict  (* check_document = Some count, count > 0 *)
  | RootRejected                             (* check_document = None: the unchanged Sorted rejection *)

(* The gate. The decision of Z3SortedProof.check_document is reused
   unchanged; coverage only NARROWS certification (an uncovered document is
   reported RootUncovered, never as a rejected proof). No route calls it. *)
let check_root_document (schema:S.schema) (doc:P.document) : root_verdict =
  match SP.check_document schema doc with
  | None -> RootRejected
  | Some n ->
    if n > 0 then RootPending n
    else if root_covered schema doc then RootCertified
    else RootUncovered

let lemma_certified_schema (schema:S.schema) (doc:P.document)
  : Lemma (requires check_root_document schema doc == RootCertified)
          (ensures S.valid schema /\ TR.supported schema /\ SP.check_document schema doc == Some 0 /\
                   root_covered schema doc) = ()

(* The gate, too, reads only the read view: the native declarations and
   expressions tables and every rule payload other than instantiation
   arguments and Farkas coefficients never change its verdict. *)
let rec lemma_entries_covered_view (sigma:V.signature) (es:list P.entry)
  : Lemma (entries_covered sigma (L.map shape_entry es) == entries_covered sigma es) (decreases es) =
  match es with [] -> () | _ :: rest -> lemma_entries_covered_view sigma rest

let lemma_root_read_view (schema:S.schema) (doc:P.document)
  : Lemma (check_root_document schema doc == check_root_document schema (read_view doc)) =
  lemma_document_read_view schema doc;
  lemma_entries_covered_view (S.signature schema) doc.P.entries

(* Coverage consequences on the actual document data: every node occurring
   in an original assertion, an entry formula or an instantiation argument
   is supported and law-ready (TR.lemma_document_node), and the term is
   typed (D.scoped). *)
let rec lemma_scoped_mem (es:list expr) (e:expr)
  : Lemma (requires D.scoped_args [] es /\ L.mem e es) (ensures D.scoped [] e) (decreases es) =
  match es with [] -> () | d :: rest -> if d = e then () else lemma_scoped_mem rest e

let rec lemma_entries_covered_mem (sigma:V.signature) (es:list P.entry) (e:P.entry)
  : Lemma (requires entries_covered sigma es /\ L.mem e es) (ensures entry_covered sigma e) (decreases es) =
  match es with [] -> () | d :: rest -> if d = e then () else lemma_entries_covered_mem sigma rest e

let lemma_certified_assertion_node (schema:S.schema) (doc:P.document) (a x:expr)
  : Lemma (requires check_root_document schema doc == RootCertified /\ L.mem a doc.P.assertions /\ TR.occurs x a)
          (ensures TR.supported schema /\ D.scoped [] a /\
                   TR.supported_expression (S.signature schema) x /\ TR.node_ready (S.signature schema) x) =
  lemma_scoped_mem doc.P.assertions a;
  TR.lemma_document_node schema doc.P.assertions a x

let lemma_certified_entry_node (schema:S.schema) (doc:P.document) (e:P.entry) (t x:expr)
  : Lemma (requires check_root_document schema doc == RootCertified /\ L.mem e doc.P.entries /\
                    (t == e.P.formula \/ L.mem t (rule_terms e.P.rule)) /\ TR.occurs x t)
          (ensures D.scoped [] t /\
                   TR.supported_expression (S.signature schema) x /\ TR.node_ready (S.signature schema) x) =
  lemma_entries_covered_mem (S.signature schema) doc.P.entries e;
  if t = e.P.formula then TR.lemma_document_node schema [t] t x
  else begin
    lemma_scoped_mem (rule_terms e.P.rule) t;
    TR.lemma_document_node schema (rule_terms e.P.rule) t x
  end

(* The original assertions of an accepted document are closed Boolean
   terms: DERIVED from the checker's own result (SP.check_document tests
   SP.boolean_expressions on them), so the falsification below is never
   the vacuous falsity of an ill-scoped or non-Boolean assertion. *)
let rec typed_assertions (es:list expr) : Tot bool (decreases es) =
  match es with [] -> true | e :: rest -> D.scoped [] e && get_sort e = bool_sort && typed_assertions rest

let rec lemma_typed_assertions (s:S.checked_schema) (es:list expr)
  : Lemma (requires SP.boolean_expressions s es) (ensures typed_assertions es) (decreases es) =
  match es with [] -> () | _ :: rest -> lemma_typed_assertions s rest

let lemma_checked_assertions_typed (schema:S.schema) (doc:P.document)
  : Lemma (requires Some? (SP.check_document schema doc)) (ensures typed_assertions doc.P.assertions) =
  lemma_typed_assertions schema doc.P.assertions

(* Among typed assertions that are not all root-true, one is root-FALSE:
   its (well-typed) root evaluation has truth false. *)
let rec lemma_false_member (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (es:list expr)
  : Lemma (requires typed_assertions es /\ not (root_truths u sch i es))
          (ensures exists (a:expr). L.mem a es /\ D.scoped [] a /\ get_sort a == bool_sort /\
                                    not (root_holds u sch i a))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest -> if root_holds u sch i e then lemma_false_member u sch i rest

(* L2, the certified document theorem, for ANY checked schema: a
   RootCertified verdict implies the schema is supported and the original
   assertions are typed (both derived from the verdict), and in EVERY root
   model i, for every carrier choice u, some original assertion is false. *)
let lemma_root_certified (u:TR.uninterpreted) (sch:S.checked_schema) (doc:P.document) (i:TR.interp u sch)
  : Lemma (requires check_root_document sch doc == RootCertified /\ TR.root_model u sch i)
          (ensures TR.supported sch /\ root_covered sch doc /\ typed_assertions doc.P.assertions /\
                   not (root_truths u sch i doc.P.assertions) /\
                   (exists (a:expr). L.mem a doc.P.assertions /\ D.scoped [] a /\ get_sort a == bool_sort /\
                                     not (root_holds u sch i a))) =
  lemma_checked_assertions_typed sch doc;
  lemma_root_check_document u sch i doc;
  lemma_false_member u sch i doc.P.assertions

(* Unconditional standard corollary: for EVERY u and EVERY free choice uf,
   the standard root model (L1) falsifies a certified document. No legacy
   model_sound, no assumed hypothesis. *)
let lemma_standard_certified (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
                             (doc:P.document)
  : Lemma (requires check_root_document sch doc == RootCertified)
          (ensures TR.root_model u sch (TR.standard u sch uf) /\
                   not (root_truths u sch (TR.standard u sch uf) doc.P.assertions)) =
  TR.lemma_standard_root u sch uf;
  lemma_root_certified u sch doc (TR.standard u sch uf)
