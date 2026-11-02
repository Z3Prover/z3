module Z3NnfSkolemTests

(* Tests of the Skolem contexts of the Sorted epsilon route
   (Z3SortedProof.certified_context / epsilon_context).

   A. The behavioural contract of the context ordering (certified_context
      orders the REVERSED collection, so that the common case is one
      SK.ordered_context pass; the selection of SK.order_context still runs
      when the reversed list is not ordered):
        A1 the reversed collection is already ordered (fast path);
        A2 the reversed collection is NOT ordered: the selection finds the
           same context (same definitions, same order);
        A3 a duplicated Skolem step is collected once;
        A4 two different definitions of one witness conflict: no context;
        A5 a cycle (each body mentions the other's witness): no order, no
           context, and no fallback context either;
        A6 a witness occurring in an original assertion fails the freshness
           gate: no context;
        A7 the constant-only top-level route: when the merged collection
           (top-level plus inner steps of NNF certificates) fails a gate,
           the top-level context alone is used.

   B. Dependent Skolem functions (Z3SortedDependentSkolem): the two actual
      residual certificates of the b3c1 fstar-build replay, transcribed
      entry by entry (FStar.Nonempty query 2 node 92 and
      Pulse.C.Types.Scalar-1 query 1 node 85): red without the closure,
      green with it; the Nonempty node in a self-contained refutation,
      pending on the plain route and RootCertified on the epsilon route,
      falsified in every root model whose dependent extension is again a
      root model; a RELATIONAL two-witness definition (y1 <> y2, where a
      choice per coordinate may pick equal values) certified through the
      joint choice.
   C. Dependent mutants, each the checker's own verdict: swapped (and
      inconsistent), missing and repeated arguments (no definition), an
      extra typed argument (a Skolem function of more arguments: accepted),
      a captured index under an inner binder, both wrong polarities, a
      witness in an original assertion (no dependent context: pending), one
      function reused by two definitions (collection fails), a cycle (no
      order), the zero-dependency case kept on the closed route, the
      4096-position dependency-scope cap at its boundary, a referenced
      variable never reinterpreted at another sort, closed constants and
      dependent functions in one document (dependent body mentioning a closed
      constant: accepted; closed body mentioning a dependent function: no
      dependent context), and a satisfiable would-be refutation through a
      wrong-polarity dependent step: pending, with a proved standard-root
      counter-model (C15). Then (C16-C20): an ACCEPTED negative-polarity
      dependent step (pending without its closure, replayed with it); the
      runtime gate skolem_scopes_ok at an assigned scope (passes at the
      dependency sorts, refused when one assigned scope has another sort at
      a dependency's position); the same dependent step in two certificates
      (one definition); a non-cyclic chain in REVERSE document order (the
      selection orders it); and a sort-mismatched swap of the arguments (no
      definition).

   Every expected value is the checker's own result, computed by
   normalization. Most inputs are well-sorted; C12 and C20 are deliberately
   ill-sorted inputs, whose expected result is the rejection. *)

open Z3AstTheory
open Z3ValueTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3Definitions
module L = FStar.List.Tot
module TR = Z3TypedRoot
module SP = Z3SortedProof
module P = Z3ProofDocument
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module O = Z3ObservationalEquality
module E = Z3SortedSkolem
module SK = Z3Skolemization
module PT = Z3SortedProofTests
module NR = Z3NnfReplay
module RD = Z3SortedRootDocument
module DS = Z3SortedDependentSkolem
module BR = Z3BooleanRewrite
module RDT = Z3SortedRootDocumentTests

(* ---------------------------------------------------------------------- *)
(* Shapes                                                                   *)
(* ---------------------------------------------------------------------- *)

let integer : sort = TR.int_s

let symbol (name:string) (ds:list sort) (r:sort) : func_decl =
  { decl_name = name; domain = ds; range = r; interp = None; int_params = [] }

let oeq (a b:expr) : expr = O.mk_oeq_expr a b
let exists_ (bs:list sort) (b:expr) : expr = Quantifier Exists_k bs bool_sort b

let be (name:string) (f:expr) (ps:list int) : U.binder_entry =
  { U.binder_name = name; binder_formula = f; binder_premises = ps; binder_sorts = None }
let cert (es:list U.binder_entry) (root:int) : U.binder_certificate = { U.binder_entries = es; binder_root = root }

let entry (r:U.rule) (f:expr) (ids:list int) : P.entry = { P.rule = r; formula = f; premise_ids = ids }

let doc (assertions:list expr) (entries:list P.entry) (root:int) : P.document = {
  P.declarations = []; P.expressions = []; P.assertions = assertions; P.entries = entries; P.root = root;
}

let sch : S.checked_schema = PT.core_schema

(* The context the epsilon route certifies from the top-level Skolem steps. *)
let top_context (d:P.document) : list SK.definition =
  E.erase sch (SP.certified_context sch d (SP.collect_epsilon sch [] d.P.entries))

(* ---------------------------------------------------------------------- *)
(* Definitions                                                              *)
(* ---------------------------------------------------------------------- *)

(* da: exists x. P1(x)  ~  P1(sk!a)                        (witness sk!a)
   db: exists x. Q2(x, sk!a)  ~  Q2(sk!b, sk!a)            (witness sk!b)
   db's body mentions sk!a, so the only order is [db; da] (newest first). *)
let ca_decl : func_decl = symbol "sk!a" [] integer
let cb_decl : func_decl = symbol "sk!b" [] integer
let ca : expr = App ca_decl []
let cb : expr = App cb_decl []
let p1 : func_decl = symbol "P1" [integer] bool_sort
let q2 : func_decl = symbol "Q2" [integer; integer] bool_sort

let da_body : expr = App p1 [Var 0 integer]
let da_src : expr = exists_ [integer] da_body
let da_inst : expr = App p1 [ca]
let da_def : SK.definition =
  { SK.bound_sorts = [integer]; negative = false; body = da_body; dependencies = []; witnesses = [(0, ca_decl)] }

let db_body : expr = App q2 [Var 0 integer; ca]
let db_src : expr = exists_ [integer] db_body
let db_inst : expr = App q2 [cb; ca]
let db_def : SK.definition =
  { SK.bound_sorts = [integer]; negative = false; body = db_body; dependencies = []; witnesses = [(0, cb_decl)] }

let sk_entry (src inst:expr) : P.entry = entry U.Skolemization (oeq src inst) []

let a_definitions ()
  : Lemma (SK.definition_of da_src da_inst == Some da_def /\ E.eligible sch da_def /\
           SK.definition_of db_src db_inst == Some db_def /\ E.eligible sch db_def) =
  assert_norm (SK.definition_of da_src da_inst == Some da_def /\ E.eligible sch da_def);
  assert_norm (SK.definition_of db_src db_inst == Some db_def /\ E.eligible sch db_def)

(* ---------------------------------------------------------------------- *)
(* A. The ordering contract                                                 *)
(* ---------------------------------------------------------------------- *)

(* A1 document order da, db: the collection is [da; db] and its reversal
   [db; da] is already ordered (one SK.ordered_context pass). *)
let a1_doc : P.document = doc [] [sk_entry da_src da_inst; sk_entry db_src db_inst] 0

let a1_fast_path ()
  : Lemma (SP.collect_epsilon sch [] a1_doc.P.entries == Some [da_def; db_def] /\
           SK.ordered_context [db_def; da_def] /\
           top_context a1_doc == [db_def; da_def]) =
  assert_norm (SP.collect_epsilon sch [] a1_doc.P.entries == Some [da_def; db_def]);
  assert_norm (SK.ordered_context [db_def; da_def]);
  assert_norm (top_context a1_doc == [db_def; da_def])

(* A2 document order db, da: the reversal [da; db] is NOT ordered (da's
   witness occurs in db's body), so order_context selects; the result is the
   same context as A1. *)
let a2_doc : P.document = doc [] [sk_entry db_src db_inst; sk_entry da_src da_inst] 0

let a2_selection_path ()
  : Lemma (SP.collect_epsilon sch [] a2_doc.P.entries == Some [db_def; da_def] /\
           not (SK.ordered_context [da_def; db_def]) /\
           top_context a2_doc == [db_def; da_def]) =
  assert_norm (SP.collect_epsilon sch [] a2_doc.P.entries == Some [db_def; da_def]);
  assert_norm (not (SK.ordered_context [da_def; db_def]));
  assert_norm (top_context a2_doc == [db_def; da_def])

(* A3 the same Skolem step twice: one definition. *)
let a3_doc : P.document = doc [] [sk_entry da_src da_inst; sk_entry da_src da_inst] 0

let a3_duplicate ()
  : Lemma (SP.collect_epsilon sch [] a3_doc.P.entries == Some [da_def] /\ top_context a3_doc == [da_def]) =
  assert_norm (SP.collect_epsilon sch [] a3_doc.P.entries == Some [da_def]);
  assert_norm (top_context a3_doc == [da_def])

(* A4 a second, different definition of the witness sk!a conflicts. *)
let p2 : func_decl = symbol "P2" [integer] bool_sort
let a4_doc : P.document =
  doc [] [sk_entry da_src da_inst; sk_entry (exists_ [integer] (App p2 [Var 0 integer])) (App p2 [ca])] 0

let a4_conflict ()
  : Lemma (SP.collect_epsilon sch [] a4_doc.P.entries == None /\ top_context a4_doc == [] /\
           SP.epsilon_context sch a4_doc == []) =
  assert_norm (SP.collect_epsilon sch [] a4_doc.P.entries == None);
  assert_norm (top_context a4_doc == []);
  assert_norm (SP.epsilon_context sch a4_doc == [])

(* A5 a cycle: dc's body mentions dd's witness and dd's body mentions dc's. *)
let cc : expr = App (symbol "sk!c" [] integer) []
let cd : expr = App (symbol "sk!d" [] integer) []
let rr : func_decl = symbol "R" [integer; integer] bool_sort
let a5_doc : P.document =
  doc [] [sk_entry (exists_ [integer] (App rr [Var 0 integer; cd])) (App rr [cc; cd]);
          sk_entry (exists_ [integer] (App rr [cc; Var 0 integer])) (App rr [cc; cd])] 0

let a5_cycle ()
  : Lemma (Some? (SP.collect_epsilon sch [] a5_doc.P.entries) /\
           L.length (Some?.v (SP.collect_epsilon sch [] a5_doc.P.entries)) == 2 /\
           top_context a5_doc == [] /\ SP.epsilon_context sch a5_doc == []) =
  assert_norm (Some? (SP.collect_epsilon sch [] a5_doc.P.entries));
  assert_norm (L.length (Some?.v (SP.collect_epsilon sch [] a5_doc.P.entries)) == 2);
  assert_norm (top_context a5_doc == []);
  assert_norm (SP.epsilon_context sch a5_doc == [])

(* A6 the witness sk!a occurs in an original assertion. *)
let a6_doc : P.document = doc [da_inst] [sk_entry da_src da_inst] 0

let a6_not_fresh ()
  : Lemma (SP.collect_epsilon sch [] a6_doc.P.entries == Some [da_def] /\ top_context a6_doc == [] /\
           SP.epsilon_context sch a6_doc == []) =
  assert_norm (SP.collect_epsilon sch [] a6_doc.P.entries == Some [da_def]);
  assert_norm (top_context a6_doc == []);
  assert_norm (SP.epsilon_context sch a6_doc == [])

(* A7 the merged collection fails (an inner Skolem step of an NNF
   certificate redefines sk!a), so the epsilon context is the top-level
   context alone; the inner step is not in it. *)
let a7_inner_src : expr = exists_ [integer] (App p2 [Var 0 integer])
let a7_inner_inst : expr = App p2 [ca]
let a7_cert : U.binder_certificate =
  cert [be "sk" (oeq a7_inner_src a7_inner_inst) [];
        be "nnf-pos" (oeq a7_inner_src a7_inner_inst) [0]] 1
let a7_doc : P.document =
  doc [] [sk_entry da_src da_inst;
          entry (U.QuantifierIntroduction a7_cert) (oeq a7_inner_src a7_inner_inst) []] 0

let a7_top_level_fallback ()
  : Lemma (SP.collect_merged sch [] a7_doc.P.entries == None /\
           E.erase sch (SP.epsilon_context sch a7_doc) == [da_def]) =
  assert_norm (SP.collect_merged sch [] a7_doc.P.entries == None);
  assert_norm (E.erase sch (SP.epsilon_context sch a7_doc) == [da_def])

(* ---------------------------------------------------------------------- *)
(* B. Dependent Skolem functions (Z3SortedDependentSkolem)                  *)
(* ---------------------------------------------------------------------- *)

let term : sort = BaseSort "Term"
let universe : sort = BaseSort "Universe"
let fuel : sort = BaseSort "Fuel"

let const (name:string) (s:sort) : expr = App (symbol name [] s) []
let mk_and (args:list expr) : expr = App (BR.connective_decl BR.Conjunction args) args
let mk_or (args:list expr) : expr = App (BR.connective_decl BR.Disjunction args) args
let neg (a:expr) : expr = R.mk_not_expr a
let iff (a b:expr) : expr = App (R.eq_decl bool_sort) [a; b]
let forall_ (bs:list sort) (b:expr) : expr = Quantifier Forall_k bs bool_sort b
let bq (name:string) (bs:list sort) (f:expr) (ps:list int) : U.binder_entry =
  { U.binder_name = name; binder_formula = f; binder_premises = ps; binder_sorts = Some bs }
let refl (e:expr) : U.binder_entry = be "refl" (oeq e e) []

let valid (x:expr) : expr = App (symbol "Valid" [term] bool_sort) [x]
let htf : func_decl = symbol "HasTypeFuel" [fuel; term; term] bool_sort
let max_ifuel : expr = const "MaxIFuel" fuel
let ht (f x t:expr) : expr = App htf [f; x; t]

let node_of (c:U.binder_certificate) (a b:expr) : U.proof_node =
  { U.kind = U.QuantifierIntroduction c; conclusion = U.Observational a b; premises = [] }
let fact_of (a b:expr) : U.checked_fact = { U.conclusion = U.Observational a b; hypotheses = [] }

let falsified (u:TR.uninterpreted) (d:P.document) (i:TR.interp u sch) : prop =
  not (RD.root_truths u sch i d.P.assertions)

(* The closure the epsilon route generates for a dependent step a ~ b. *)
let closure_for (a b:expr) : option expr =
  match DS.definition_of sch a b with Some d -> Some (DS.closure d) | None -> None

(* B1 = FStar.Nonempty query 2 node 92 (b3c1 producer, phase B2 diagnostic
   certificate b2/certificates/queries-FStar.Nonempty.smt2.q2-n92.cert.txt),
   transcribed entry by entry: an nnf-pos root over forall [Universe; Term]
   of a Boolean equality whose right side is exists [Term]; the positive
   branch is the OPEN dependent step sk of @x2!1(#0:Term, #1:Universe). *)
let nonempty_d : func_decl = symbol "FStar.Nonempty.nonempty" [universe; term] term
let tag_d : func_decl = symbol "FStar.Nonempty.tag" [universe; term; term] term
let x2_1 : func_decl = symbol "@x2!1" [term; universe] term

let n_N : expr = valid (App nonempty_d [Var 1 universe; Var 0 term])
let n_body : expr = mk_and [ht max_ifuel (Var 0 term) (Var 1 term); valid (App tag_d [Var 2 universe; Var 1 term; Var 0 term])]
let n_B : expr = exists_ [term] n_body
let n_sk : expr = App x2_1 [Var 0 term; Var 1 universe]
let n_inst : expr = mk_and [ht max_ifuel n_sk (Var 0 term); valid (App tag_d [Var 1 universe; Var 0 term; n_sk])]
let n_fa : expr = forall_ [term] (neg n_body)
let n_tbody : expr = mk_and [mk_or [neg n_N; n_inst]; mk_or [n_N; n_fa]]
let n_src : expr = forall_ [universe; term] (iff n_N n_B)
let n_tgt : expr = forall_ [universe; term] n_tbody

let n92_cert : U.binder_certificate = cert [
  refl n_N;                                                 (* 0 *)
  refl (neg n_N);                                           (* 1 *)
  be "sk" (oeq n_B n_inst) [];                              (* 2, open at [Term; Universe] *)
  refl (neg n_body);                                        (* 3 *)
  bq "nnf-neg" [term] (oeq (neg n_B) n_fa) [3];             (* 4 *)
  be "nnf-pos" (oeq (iff n_N n_B) n_tbody) [0; 1; 2; 4];    (* 5 *)
  bq "nnf-pos" [universe; term] (oeq n_src n_tgt) [5]] 6    (* 6 *)

let n92_node : U.proof_node = node_of n92_cert n_src n_tgt

(* The closure: forall over the dependency scope [Term; Universe]
   (binders [Universe; Term]) of (= n_B n_inst). *)
let n92_closure : expr = forall_ [universe; term] (iff n_B n_inst)

let b1_definition ()
  : Lemma (closure_for n_B n_inst == Some n92_closure /\
           (match DS.definition_of sch n_B n_inst with
            | Some d -> d.SK.dependencies == [(0, term); (1, universe)] /\ d.SK.witnesses == [(0, x2_1)]
            | None -> False)) =
  assert_norm (closure_for n_B n_inst == Some n92_closure);
  assert_norm (match DS.definition_of sch n_B n_inst with
               | Some d -> d.SK.dependencies == [(0, term); (1, universe)] /\ d.SK.witnesses == [(0, x2_1)]
               | None -> False)

(* Red: without the closure the node stays pending (the old route, and the
   plain route); green: with it, the replay checks the node. *)
let b1_red_green ()
  : Lemma (SP.check_node sch [] n92_node == Some (fact_of n_src n_tgt, 1) /\
           SP.check_node sch [n92_closure] n92_node == Some (fact_of n_src n_tgt, 0)) =
  assert_norm (SP.check_node sch [] n92_node == Some (fact_of n_src n_tgt, 1));
  assert_norm (SP.check_node sch [n92_closure] n92_node == Some (fact_of n_src n_tgt, 0))

(* A self-contained refutation around the node: the axiom, nonempty(u0, t0)
   and "no y has type t0" are contradictory through the Skolem witness
   @x2!1(t0, u0). *)
let u0 : expr = const "u0" universe
let t0 : expr = const "t0" term
let n_N0 : expr = valid (App nonempty_d [u0; t0])
let n_sk0 : expr = App x2_1 [t0; u0]
let n_inst0 : expr = mk_and [ht max_ifuel n_sk0 t0; valid (App tag_d [u0; t0; n_sk0])]
let n_fa0 : expr = forall_ [term] (neg (mk_and [ht max_ifuel (Var 0 term) t0; valid (App tag_d [u0; t0; Var 0 term])]))
let n_tbody0 : expr = mk_and [mk_or [neg n_N0; n_inst0]; mk_or [n_N0; n_fa0]]
let n_h : expr = forall_ [term] (neg (ht max_ifuel (Var 0 term) t0))

let n92_document_with (assertions:list expr) : P.document =
  doc assertions
      [entry U.Asserted n_src [];
       entry (U.QuantifierIntroduction n92_cert) (oeq n_src n_tgt) [];
       entry U.ObservationalMP n_tgt [0; 1];
       entry (U.QuantifierInstantiation [u0; t0]) (mk_or [neg n_tgt; n_tbody0]) [];
       entry U.Asserted n_N0 [];
       entry U.Asserted n_h [];
       entry (U.QuantifierInstantiation [n_sk0]) (mk_or [neg n_h; neg (ht max_ifuel n_sk0 t0)]) [];
       entry U.UnitResolution R.false_expr [3; 2; 4; 6; 5]]
      7

let n92_document : P.document = n92_document_with [n_src; n_N0; n_h]

let b1_context ()
  : Lemma (SP.epsilon_context sch n92_document == [] /\
           L.length (SP.dependent_context sch n92_document []) == 1 /\
           L.mem n92_closure (SP.elaborate_full sch n92_document).P.assertions) =
  assert_norm (SP.epsilon_context sch n92_document == []);
  assert_norm (L.length (SP.dependent_context sch n92_document []) == 1);
  assert_norm (L.mem n92_closure (SP.elaborate_full sch n92_document).P.assertions)

let b1_plain_pending () : Lemma (SP.check_document sch n92_document == Some 1) =
  assert_norm (SP.check_document sch n92_document == Some 1)

let b1_certified () : Lemma (RD.check_root_document_epsilon sch n92_document == RD.RootCertified) =
  assert_norm (RD.check_root_document_epsilon sch n92_document == RD.RootCertified)

let b1_falsified (u:TR.uninterpreted) (i:TR.interp u sch)
  : Lemma (requires TR.root_model u sch i)
          (ensures falsified u n92_document i /\
                   TR.root_model u sch (RD.epsilon_extension u sch i n92_document)) =
  b1_certified ();
  RD.lemma_root_certified_epsilon u sch n92_document i;
  RD.lemma_root_epsilon_extension u sch i n92_document

(* The positive instance: for EVERY u and uf, the standard root model's
   dependent extension is a root model, and it falsifies the document. *)
let b1_standard (u:TR.uninterpreted) (uf:TR.symbols u sch)
  : Lemma (TR.root_model u sch (RD.epsilon_extension u sch (TR.standard u sch uf) n92_document) /\
           falsified u n92_document (TR.standard u sch uf)) =
  TR.lemma_standard_root u sch uf;
  b1_falsified u (TR.standard u sch uf)

(* B2 = Pulse.C.Types.Scalar-1 query 1 node 85 (b2/certificates/
   pulse__queries-Pulse.C.Types.Scalar-1.smt2.q1-n85.cert.txt), 11 entries:
   an nnf-pos root over forall [Fuel; Term; Universe; Term; Term]; the open
   step sk of @x5!1(#0:Term, #1:Term) under monotonicity; nnf-neg duality. *)
let refine_d : func_decl = symbol "Tm_refine_b46e74b04b958b2e2220a0876a9d032a" [universe; term; term] term
let apply_tt (x y:expr) : expr = App (symbol "ApplyTT" [term; term] term) [x; y]
let unit_t : expr = const "Prims.unit" term
let x5_1 : func_decl = symbol "@x5!1" [term; term] term

let s_HR : expr = ht (Var 4 fuel) (Var 3 term) (App refine_d [Var 2 universe; Var 1 term; Var 0 term])
let s_HU : expr = ht (Var 4 fuel) (Var 3 term) unit_t
let s_body : expr = mk_and [ht max_ifuel (Var 0 term) (Var 2 term); valid (apply_tt (Var 1 term) (Var 0 term))]
let s_B : expr = exists_ [term] s_body
let s_sk : expr = App x5_1 [Var 0 term; Var 1 term]
let s_inst : expr = mk_and [ht max_ifuel s_sk (Var 1 term); valid (apply_tt (Var 0 term) s_sk)]
let s_fa : expr = forall_ [term] (neg s_body)
let s_and : expr = mk_and [s_HU; s_B]
let s_tbody : expr = mk_and [mk_or [neg s_HR; mk_and [s_HU; s_inst]]; mk_or [s_HR; mk_or [neg s_HU; s_fa]]]
let s_binders : list sort = [fuel; term; universe; term; term]
let s_src : expr = forall_ s_binders (iff s_HR s_and)
let s_tgt : expr = forall_ s_binders s_tbody

let n85_cert_with (sk:U.binder_entry) (inst:expr) : U.binder_certificate = cert [
  refl s_HR;                                                          (* 0 *)
  refl (neg s_HR);                                                    (* 1 *)
  refl s_HU;                                                          (* 2 *)
  sk;                                                                 (* 3 *)
  be "monotonicity" (oeq s_and (mk_and [s_HU; inst])) [2; 3];         (* 4 *)
  refl (neg s_HU);                                                    (* 5 *)
  refl (neg s_body);                                                  (* 6 *)
  bq "nnf-neg" [term] (oeq (neg s_B) s_fa) [6];                       (* 7 *)
  be "nnf-neg" (oeq (neg s_and) (mk_or [neg s_HU; s_fa])) [5; 7];     (* 8 *)
  be "nnf-pos" (oeq (iff s_HR s_and) s_tbody) [0; 1; 4; 8];           (* 9 *)
  bq "nnf-pos" s_binders (oeq s_src s_tgt) [9]] 10                    (* 10 *)

let n85_cert : U.binder_certificate = n85_cert_with (be "sk" (oeq s_B s_inst) []) s_inst
let n85_node : U.proof_node = node_of n85_cert s_src s_tgt
let n85_closure : expr = forall_ [term; term] (iff s_B s_inst)

let b2_red_green ()
  : Lemma (closure_for s_B s_inst == Some n85_closure /\
           SP.check_node sch [] n85_node == Some (fact_of s_src s_tgt, 1) /\
           SP.check_node sch [n85_closure] n85_node == Some (fact_of s_src s_tgt, 0)) =
  assert_norm (closure_for s_B s_inst == Some n85_closure);
  assert_norm (SP.check_node sch [] n85_node == Some (fact_of s_src s_tgt, 1));
  assert_norm (SP.check_node sch [n85_closure] n85_node == Some (fact_of s_src s_tgt, 0))

(* B3 a RELATIONAL two-witness definition: exists y1 y2. P x /\ y1 <> y2.
   Each coordinate alone is satisfiable by any value, so independent
   per-coordinate choices may pick y1 = y2; the joint choice of ONE pair per
   argument (Z3SortedDependentSkolem.dselected) makes the closure true. The
   document is a refutation of "every x has two distinct values" and "all
   values are equal". *)
let pd : func_decl = symbol "P" [term] bool_sort
let f1 : func_decl = symbol "sk!f1" [term] term
let f2 : func_decl = symbol "sk!f2" [term] term
let eqt (a b:expr) : expr = App (R.eq_decl term) [a; b]
let r_body : expr = mk_and [App pd [Var 2 term]; neg (eqt (Var 1 term) (Var 0 term))]
let r_B : expr = exists_ [term; term] r_body
let r_inst : expr = mk_and [App pd [Var 0 term]; neg (eqt (App f1 [Var 0 term]) (App f2 [Var 0 term]))]
let r_src : expr = forall_ [term] r_B
let r_tgt : expr = forall_ [term] r_inst
let r_cert : U.binder_certificate =
  cert [be "sk" (oeq r_B r_inst) []; bq "nnf-pos" [term] (oeq r_src r_tgt) [0]] 1
let r_closure : expr = forall_ [term] (iff r_B r_inst)

let c0 : expr = const "c" term
let r_inst0 : expr = mk_and [App pd [c0]; neg (eqt (App f1 [c0]) (App f2 [c0]))]
let r_all_equal : expr = forall_ [term; term] (eqt (Var 1 term) (Var 0 term))
let r_document : P.document =
  doc [r_src; r_all_equal]
      [entry U.Asserted r_src [];
       entry (U.QuantifierIntroduction r_cert) (oeq r_src r_tgt) [];
       entry U.ObservationalMP r_tgt [0; 1];
       entry (U.QuantifierInstantiation [c0]) (mk_or [neg r_tgt; r_inst0]) [];
       entry U.Asserted r_all_equal [];
       entry (U.QuantifierInstantiation [App f1 [c0]; App f2 [c0]])
             (mk_or [neg r_all_equal; eqt (App f1 [c0]) (App f2 [c0])]) [];
       entry U.UnitResolution R.false_expr [3; 2; 5; 4]]
      6

let b3_relational ()
  : Lemma (closure_for r_B r_inst == Some r_closure /\
           (match DS.definition_of sch r_B r_inst with
            | Some d -> L.length d.SK.witnesses == 2
            | None -> False) /\
           SP.check_document sch r_document == Some 1 /\
           RD.check_root_document_epsilon sch r_document == RD.RootCertified) =
  assert_norm (closure_for r_B r_inst == Some r_closure);
  assert_norm (match DS.definition_of sch r_B r_inst with
               | Some d -> L.length d.SK.witnesses == 2
               | None -> False);
  assert_norm (SP.check_document sch r_document == Some 1);
  assert_norm (RD.check_root_document_epsilon sch r_document == RD.RootCertified)

let b3_falsified (u:TR.uninterpreted) (i:TR.interp u sch)
  : Lemma (requires TR.root_model u sch i) (ensures falsified u r_document i) =
  b3_relational ();
  RD.lemma_root_certified_epsilon u sch r_document i

(* ---------------------------------------------------------------------- *)
(* C. Dependent Skolem mutants: the actual verdicts                         *)
(* ---------------------------------------------------------------------- *)

(* C1 swapped arguments, inconsistently across the two occurrences of
   @x5!1 (same sorts): no definition (SK.collect_witnesses needs one
   dependency list), so the epsilon route generates no closure for the
   step and the replay leaves it pending. *)
let s_inst_swapped : expr =
  mk_and [ht max_ifuel s_sk (Var 1 term); valid (apply_tt (Var 0 term) (App x5_1 [Var 1 term; Var 0 term]))]
let c1_swapped () : Lemma (SK.definition_of s_B s_inst_swapped == None) =
  assert_norm (SK.definition_of s_B s_inst_swapped == None)

(* C2 a missing argument: @x5m(#0) while the body reads #0 and #1 outside
   the binder: not covered, no definition. *)
let x5m : func_decl = symbol "@x5m" [term] term
let s_inst_missing : expr =
  mk_and [ht max_ifuel (App x5m [Var 0 term]) (Var 1 term); valid (apply_tt (Var 0 term) (App x5m [Var 0 term]))]
let c2_missing () : Lemma (SK.definition_of s_B s_inst_missing == None) =
  assert_norm (SK.definition_of s_B s_inst_missing == None)

(* C3 a repeated argument: @x5r(#0, #1, #1): a repeated dependency index
   (SK.valid_dependencies), no definition. *)
let x5r : func_decl = symbol "@x5r" [term; term; term] term
let s_sk_r : expr = App x5r [Var 0 term; Var 1 term; Var 1 term]
let s_inst_repeated : expr = mk_and [ht max_ifuel s_sk_r (Var 1 term); valid (apply_tt (Var 0 term) s_sk_r)]
let c3_repeated () : Lemma (SK.definition_of s_B s_inst_repeated == None) =
  assert_norm (SK.definition_of s_B s_inst_repeated == None)

(* C4 an extra (unused, typed) argument @x5e(#0, #1, #2:Universe) is a
   Skolem function of more arguments: sound, and accepted with a closure
   over [Term; Term; Universe]. *)
let x5e : func_decl = symbol "@x5e" [term; term; universe] term
let s_sk_e : expr = App x5e [Var 0 term; Var 1 term; Var 2 universe]
let s_inst_extra : expr = mk_and [ht max_ifuel s_sk_e (Var 1 term); valid (apply_tt (Var 0 term) s_sk_e)]
let c4_extra ()
  : Lemma (closure_for s_B s_inst_extra == Some (forall_ [universe; term; term] (iff s_B s_inst_extra))) =
  assert_norm (closure_for s_B s_inst_extra == Some (forall_ [universe; term; term] (iff s_B s_inst_extra)))

(* C5 a captured index: under an inner binder the dependency #0 outside is
   Var 1; the mutant applies the witness to Var 0 (the inner variable). *)
let r3 : func_decl = symbol "R3" [term; term; term] bool_sort
let k_body : expr = forall_ [term] (App r3 [Var 1 term; Var 0 term; Var 2 term])
let k_B : expr = exists_ [term] k_body
let kf : func_decl = symbol "sk!k" [term] term
let k_inst : expr = forall_ [term] (App r3 [App kf [Var 1 term]; Var 0 term; Var 1 term])
let k_inst_captured : expr = forall_ [term] (App r3 [App kf [Var 0 term]; Var 0 term; Var 1 term])
let c5_captured ()
  : Lemma (Some? (closure_for k_B k_inst) /\ SK.definition_of k_B k_inst_captured == None) =
  assert_norm (Some? (closure_for k_B k_inst));
  assert_norm (SK.definition_of k_B k_inst_captured == None)

(* C6 wrong polarity: the negative source (not (forall y. body)) with a
   non-negated instance, and the positive source with a negated one. *)
let c6_wrong_polarity ()
  : Lemma (SK.definition_of (neg (forall_ [term] n_body)) n_inst == None /\
           SK.definition_of n_B (neg n_inst) == None) =
  assert_norm (SK.definition_of (neg (forall_ [term] n_body)) n_inst == None);
  assert_norm (SK.definition_of n_B (neg n_inst) == None)

(* C7 the witness of the step occurs in an ORIGINAL assertion: the
   dependent context fails the freshness gate, the node stays pending. *)
let c7_document : P.document = n92_document_with [n_src; n_N0; n_h; valid n_sk0]
let c7_not_fresh ()
  : Lemma (SP.dependent_context sch c7_document [] == [] /\
           SP.check_document_epsilon sch c7_document == Some 1) =
  assert_norm (SP.dependent_context sch c7_document [] == []);
  assert_norm (SP.check_document_epsilon sch c7_document == Some 1)

(* C8 one witness function reused by two different dependent definitions
   (two certificates): the collection fails (SK.add_definition), no
   dependent context. *)
let n_body2 : expr = mk_and [ht max_ifuel (Var 0 term) (Var 1 term); valid (App tag_d [Var 2 universe; Var 0 term; Var 1 term])]
let n_inst2 : expr = mk_and [ht max_ifuel n_sk (Var 0 term); valid (App tag_d [Var 1 universe; n_sk; Var 0 term])]
let c8_cert : U.binder_certificate =
  cert [be "sk" (oeq (exists_ [term] n_body2) n_inst2) [];
        bq "nnf-pos" [universe; term] (oeq (forall_ [universe; term] (exists_ [term] n_body2))
                                           (forall_ [universe; term] n_inst2)) [0]] 1
let c8_entries : list P.entry =
  [entry (U.QuantifierIntroduction n92_cert) (oeq n_src n_tgt) [];
   entry (U.QuantifierIntroduction c8_cert)
     (oeq (forall_ [universe; term] (exists_ [term] n_body2)) (forall_ [universe; term] n_inst2)) []]
let c8_reuse ()
  : Lemma (Some? (closure_for (exists_ [term] n_body2) n_inst2) /\
           SP.collect_dependents sch [] c8_entries == None) =
  assert_norm (Some? (closure_for (exists_ [term] n_body2) n_inst2));
  assert_norm (SP.collect_dependents sch [] c8_entries == None)

(* C9 a cycle: g's body mentions f and f's body mentions g; each step alone
   is eligible, no order exists, no dependent context. *)
let cf : func_decl = symbol "sk!cf" [term] term
let cg : func_decl = symbol "sk!cg" [term] term
let q3 : func_decl = symbol "Q3" [term; term; term] bool_sort
let cy_f_B : expr = exists_ [term] (App q3 [Var 1 term; Var 0 term; App cg [Var 1 term]])
let cy_f_inst : expr = App q3 [Var 0 term; App cf [Var 0 term]; App cg [Var 0 term]]
let cy_g_B : expr = exists_ [term] (App q3 [Var 1 term; App cf [Var 1 term]; Var 0 term])
let cy_g_inst : expr = App q3 [Var 0 term; App cf [Var 0 term]; App cg [Var 0 term]]
let cy_cert (b i:expr) : U.binder_certificate =
  cert [be "sk" (oeq b i) []; bq "nnf-pos" [term] (oeq (forall_ [term] b) (forall_ [term] i)) [0]] 1
let c9_document : P.document =
  doc [] [entry (U.QuantifierIntroduction (cy_cert cy_f_B cy_f_inst)) (oeq (forall_ [term] cy_f_B) (forall_ [term] cy_f_inst)) [];
          entry (U.QuantifierIntroduction (cy_cert cy_g_B cy_g_inst)) (oeq (forall_ [term] cy_g_B) (forall_ [term] cy_g_inst)) []] 0
let c9_cycle ()
  : Lemma (Some? (closure_for cy_f_B cy_f_inst) /\ Some? (closure_for cy_g_B cy_g_inst) /\
           Some? (SP.collect_dependents sch [] c9_document.P.entries) /\
           SP.dependent_context sch c9_document [] == []) =
  assert_norm (Some? (closure_for cy_f_B cy_f_inst));
  assert_norm (Some? (closure_for cy_g_B cy_g_inst));
  assert_norm (Some? (SP.collect_dependents sch [] c9_document.P.entries));
  assert_norm (SP.dependent_context sch c9_document [] == [])

(* C10 the zero-dependency case stays on the closed route: a closed step is
   not a dependent definition, and the closed context is unchanged. *)
let c10_closed_route ()
  : Lemma (SP.dependent_definition sch (be "sk" (oeq da_src da_inst) []) == None /\
           DS.definition_of sch da_src da_inst == None) =
  assert_norm (SP.dependent_definition sch (be "sk" (oeq da_src da_inst) []) == None);
  assert_norm (DS.definition_of sch da_src da_inst == None)

(* C11 the dependency-scope cap (DS.scope_limit = 4096 positions, an
   explicit resource limit): a dependency at index 4095 gives a 4096-position
   closure scope and an eligible definition; at index 4096 there is no
   closure scope and the definition is not eligible (the step stays
   pending). *)
let capf : func_decl = symbol "sk!cap" [term] term
let cap_def (n:nat) : SK.definition =
  { SK.bound_sorts = [term]; negative = false;
    body = App (symbol "P2t" [term; term] bool_sort) [Var 0 term; Var (n + 1) term];
    dependencies = [(n, term)]; witnesses = [(0, capf)] }
let c11_scope_cap ()
  : Lemma (L.length (DS.closure_binders (cap_def 4095)) == 4096 /\ DS.eligible sch (cap_def 4095) /\
           DS.closure_binders (cap_def 4096) == [] /\ not (DS.eligible sch (cap_def 4096))) =
  assert_norm (L.length (DS.closure_binders (cap_def 4095)) == 4096);
  assert_norm (DS.eligible sch (cap_def 4095));
  assert_norm (DS.closure_binders (cap_def 4096) == []);
  assert_norm (not (DS.eligible sch (cap_def 4096)))

(* C12 a referenced variable is never reinterpreted: the body reads the
   dependency #0 as Term and also (ill-typed) as Universe; the Skolem
   definition exists, but its closure is not typed (the dependency scope
   gives #0 the sort Term), so it is not eligible. *)
let r2 : func_decl = symbol "R2" [term; term; universe] bool_sort
let cr_f : func_decl = symbol "sk!cr" [term] term
let cr_B : expr = exists_ [term] (App r2 [Var 0 term; Var 1 term; Var 1 universe])
let cr_inst : expr = App r2 [App cr_f [Var 0 term]; Var 0 term; Var 0 universe]
let c12_no_reinterpretation ()
  : Lemma (Some? (SK.definition_of cr_B cr_inst) /\ DS.definition_of sch cr_B cr_inst == None) =
  assert_norm (Some? (SK.definition_of cr_B cr_inst));
  assert_norm (DS.definition_of sch cr_B cr_inst == None)

(* C13/C14 closed constants and dependent functions in one document. C13:
   the dependent body mentions the top-level Skolem CONSTANT sk!a (the
   dependent definition is newer): one dependent definition on top of the
   closed context. C14: a closed body mentions the dependent FUNCTION; the
   dependent definitions must precede every closed one, so there is no
   dependent context (fail closed: the dependent step stays pending). *)
let q3i : func_decl = symbol "Q3i" [integer; integer; integer] bool_sort
let gi : func_decl = symbol "sk!g" [integer] integer
let m_B : expr = exists_ [integer] (App q3i [Var 0 integer; Var 1 integer; ca])
let m_inst : expr = App q3i [App gi [Var 0 integer]; Var 0 integer; ca]
let m_cert : U.binder_certificate =
  cert [be "sk" (oeq m_B m_inst) [];
        bq "nnf-pos" [integer] (oeq (forall_ [integer] m_B) (forall_ [integer] m_inst)) [0]] 1
let m_entry : P.entry =
  entry (U.QuantifierIntroduction m_cert) (oeq (forall_ [integer] m_B) (forall_ [integer] m_inst)) []
let c13_doc : P.document = doc [] [sk_entry da_src da_inst; m_entry] 0
let p2i : func_decl = symbol "P2i" [integer; integer] bool_sort
let e_src : expr = exists_ [integer] (App p2i [Var 0 integer; App gi [const "k" integer]])
let e_inst : expr = App p2i [const "sk!e" integer; App gi [const "k" integer]]
let c14_doc : P.document = doc [] [sk_entry e_src e_inst; m_entry] 0
let c13_c14_mixed ()
  : Lemma (E.erase sch (SP.epsilon_context sch c13_doc) == [da_def] /\
           L.length (SP.dependent_context sch c13_doc (SP.epsilon_context sch c13_doc)) == 1 /\
           L.length (SP.epsilon_context sch c14_doc) == 1 /\
           SP.dependent_context sch c14_doc (SP.epsilon_context sch c14_doc) == []) =
  assert_norm (E.erase sch (SP.epsilon_context sch c13_doc) == [da_def]);
  assert_norm (L.length (SP.dependent_context sch c13_doc (SP.epsilon_context sch c13_doc)) == 1);
  assert_norm (L.length (SP.epsilon_context sch c14_doc) == 1);
  assert_norm (SP.dependent_context sch c14_doc (SP.epsilon_context sch c14_doc) == [])

(* C15 a SATISFIABLE would-be refutation through a wrong-polarity dependent
   step (exists y. Pw x y) ~ (not (Pw x (sk!w x))): no Skolem definition, no
   closure, the node stays pending, so the document is not certified; and
   both inputs hold in the standard root model that interprets every free
   Boolean symbol as true (for every u): a proved counter-model. *)
let pw : func_decl = symbol "Pw" [term; term] bool_sort
let fw : func_decl = symbol "sk!w" [term] term
let w_body : expr = App pw [Var 1 term; Var 0 term]
let w_B : expr = exists_ [term] w_body
let w_bad : expr = neg (App pw [Var 0 term; App fw [Var 0 term]])
let w_src : expr = forall_ [term] w_B
let w_tgt : expr = forall_ [term] w_bad
let w_cert : U.binder_certificate =
  cert [be "sk" (oeq w_B w_bad) []; bq "nnf-pos" [term] (oeq w_src w_tgt) [0]] 1
let w_all : expr = forall_ [term; term] w_body
let w_pc : expr = App pw [c0; App fw [c0]]
let w_document : P.document =
  doc [w_src; w_all]
      [entry U.Asserted w_src [];
       entry (U.QuantifierIntroduction w_cert) (oeq w_src w_tgt) [];
       entry U.ObservationalMP w_tgt [0; 1];
       entry (U.QuantifierInstantiation [c0]) (mk_or [neg w_tgt; neg w_pc]) [];
       entry U.Asserted w_all [];
       entry (U.QuantifierInstantiation [c0; App fw [c0]]) (mk_or [neg w_all; w_pc]) [];
       entry U.UnitResolution R.false_expr [3; 2; 5; 4]]
      6

let c15_mutant_pending ()
  : Lemma (SK.definition_of w_B w_bad == None /\
           RD.check_root_document_epsilon sch w_document == RD.RootPending 1) =
  assert_norm (SK.definition_of w_B w_bad == None);
  assert_norm (RD.check_root_document_epsilon sch w_document == RD.RootPending 1)

let lemma_pw_true (u:TR.uninterpreted) (scope:list sort)
                  (rho:V.environment (TR.carrier u) (S.signature sch) scope) (a b:expr)
  : Lemma (requires D.scoped scope (App pw [a; b]))
          (ensures TR.truth sch (V.evaluate (S.signature sch) (TR.standard u sch (RDT.uf_bool u true))
                                  scope rho (App pw [a; b])) == true) =
  assert_norm (TR.classify (S.signature sch) pw == TR.Other);
  TR.lemma_eval_free_choice u sch (RDT.uf_bool u true) scope rho pw [a; b]

let c15_counter_model (u:TR.uninterpreted)
  : Lemma (TR.root_model u sch (TR.standard u sch (RDT.uf_bool u true)) /\
           RD.root_truths u sch (TR.standard u sch (RDT.uf_bool u true)) w_document.P.assertions) =
  let i = TR.standard u sch (RDT.uf_bool u true) in
  let sigma = S.signature sch in
  let empty = RD.empty_root u sch in
  TR.lemma_standard_root u sch (RDT.uf_bool u true);
  (* forall x y. Pw x y *)
  let all2 (vs:TR.targuments u sch (L.rev [term; term]))
    : Lemma (TR.truth sch (V.evaluate sigma i (L.rev [term; term] `L.append` [])
               (V.extend sigma [] (L.rev [term; term]) vs empty) w_body) == true) =
    lemma_pw_true u (L.rev [term; term] `L.append` []) (V.extend sigma [] (L.rev [term; term]) vs empty) (Var 1 term) (Var 0 term) in
  FStar.Classical.forall_intro all2;
  TR.lemma_eval_forall i [] empty [term; term] w_body;
  (* forall x. exists y. Pw x y, with the witness y = any value of Term *)
  let outer (vs:TR.targuments u sch (L.rev [term]))
    : Lemma (TR.truth sch (V.evaluate sigma i (L.rev [term] `L.append` [])
               (V.extend sigma [] (L.rev [term]) vs empty) w_B) == true) =
    let sc = L.rev [term] `L.append` [] in
    let rho = V.extend sigma [] (L.rev [term]) vs empty in
    let w : TR.targuments u sch (L.rev [term]) = [S.value_inhabitant sch (TR.default_value u) term] in
    lemma_pw_true u (L.rev [term] `L.append` sc) (V.extend sigma sc (L.rev [term]) w rho) (Var 1 term) (Var 0 term);
    FStar.Classical.exists_intro (fun (ws:TR.targuments u sch (L.rev [term])) ->
      TR.truth sch (V.evaluate sigma i (L.rev [term] `L.append` sc) (V.extend sigma sc (L.rev [term]) ws rho) w_body) == true) w;
    TR.lemma_eval_exists i sc rho [term] w_body in
  FStar.Classical.forall_intro outer;
  TR.lemma_eval_forall i [] empty [term] w_B

(* C16 an ACCEPTED negative-polarity dependent step:
   (not (forall y. Pw x y)) ~ (not (Pw x (sk!n x))); the definition is
   negative, its closure exists, and an nnf-pos certificate over it is
   pending without the closure and replayed with it. *)
let fn_ : func_decl = symbol "sk!n" [term] term
let ng_src : expr = neg (forall_ [term] w_body)
let ng_inst : expr = neg (App pw [Var 0 term; App fn_ [Var 0 term]])
let ng_cert : U.binder_certificate =
  cert [be "sk" (oeq ng_src ng_inst) [];
        bq "nnf-pos" [term] (oeq (forall_ [term] ng_src) (forall_ [term] ng_inst)) [0]] 1
let ng_closure : expr = forall_ [term] (iff ng_src ng_inst)
let c16_negative_accepted ()
  : Lemma ((match DS.definition_of sch ng_src ng_inst with Some d -> d.SK.negative == true | None -> False) /\
           closure_for ng_src ng_inst == Some ng_closure /\
           SP.check_node sch [] (node_of ng_cert (forall_ [term] ng_src) (forall_ [term] ng_inst)) ==
             Some (fact_of (forall_ [term] ng_src) (forall_ [term] ng_inst), 1) /\
           SP.check_node sch [ng_closure] (node_of ng_cert (forall_ [term] ng_src) (forall_ [term] ng_inst)) ==
             Some (fact_of (forall_ [term] ng_src) (forall_ [term] ng_inst), 0)) =
  assert_norm (match DS.definition_of sch ng_src ng_inst with Some d -> d.SK.negative == true | None -> False);
  assert_norm (closure_for ng_src ng_inst == Some ng_closure);
  assert_norm (SP.check_node sch [] (node_of ng_cert (forall_ [term] ng_src) (forall_ [term] ng_inst)) ==
               Some (fact_of (forall_ [term] ng_src) (forall_ [term] ng_inst), 1));
  assert_norm (SP.check_node sch [ng_closure] (node_of ng_cert (forall_ [term] ng_src) (forall_ [term] ng_inst)) ==
               Some (fact_of (forall_ [term] ng_src) (forall_ [term] ng_inst), 0))

(* C17 the runtime contract skolem_scopes_ok: the n92 step's dependencies are
   [(0, Term); (1, Universe)]; it passes at [Term; Universe] and is refused at
   a scope with Int at position 1 (the guard would refuse such a scope too:
   the step reads #1 as Universe). *)
let c17_scope_gate ()
  : Lemma (NR.skolem_scopes_ok (be "sk" (oeq n_B n_inst) []) (U.Observational n_B n_inst) [[term; universe]] /\
           not (NR.skolem_scopes_ok (be "sk" (oeq n_B n_inst) []) (U.Observational n_B n_inst)
                  [[term; universe]; [term; integer]])) =
  assert_norm (NR.skolem_scopes_ok (be "sk" (oeq n_B n_inst) []) (U.Observational n_B n_inst) [[term; universe]]);
  assert_norm (not (NR.skolem_scopes_ok (be "sk" (oeq n_B n_inst) []) (U.Observational n_B n_inst)
                      [[term; universe]; [term; integer]]))

(* C18 the same dependent step in two certificates is collected once. *)
let c18_document : P.document =
  doc [] [entry (U.QuantifierIntroduction n92_cert) (oeq n_src n_tgt) [];
          entry (U.QuantifierIntroduction n92_cert) (oeq n_src n_tgt) []] 0
let c18_duplicate ()
  : Lemma (L.length (SP.dependent_context sch c18_document []) == 1) =
  assert_norm (L.length (SP.dependent_context sch c18_document []) == 1)

(* C19 a non-cyclic chain in REVERSE document order: g's body mentions f
   (g is newer); g's certificate comes first, so the reversed collection
   [f; g] is not ordered and the selection finds [g; f]. *)
let q2t : func_decl = symbol "Q2t" [term; term] bool_sort
let q3t : func_decl = symbol "Q3t" [term; term; term] bool_sort
let chf : func_decl = symbol "sk!chf" [term] term
let chg : func_decl = symbol "sk!chg" [term] term
let ch_f_B : expr = exists_ [term] (App q2t [Var 1 term; Var 0 term])
let ch_f_inst : expr = App q2t [Var 0 term; App chf [Var 0 term]]
let ch_g_B : expr = exists_ [term] (App q3t [Var 1 term; Var 0 term; App chf [Var 1 term]])
let ch_g_inst : expr = App q3t [Var 0 term; App chg [Var 0 term]; App chf [Var 0 term]]
let c19_document : P.document =
  doc [] [entry (U.QuantifierIntroduction (cy_cert ch_g_B ch_g_inst)) (oeq (forall_ [term] ch_g_B) (forall_ [term] ch_g_inst)) [];
          entry (U.QuantifierIntroduction (cy_cert ch_f_B ch_f_inst)) (oeq (forall_ [term] ch_f_B) (forall_ [term] ch_f_inst)) []] 0
let c19_reverse_chain ()
  : Lemma (Some? (SP.collect_dependents sch [] c19_document.P.entries) /\
           not (SK.ordered_context (L.rev (Some?.v (SP.collect_dependents sch [] c19_document.P.entries)))) /\
           L.length (SP.dependent_context sch c19_document []) == 2) =
  assert_norm (Some? (SP.collect_dependents sch [] c19_document.P.entries));
  assert_norm (not (SK.ordered_context (L.rev (Some?.v (SP.collect_dependents sch [] c19_document.P.entries)))));
  assert_norm (L.length (SP.dependent_context sch c19_document []) == 2)

(* C20 a sort-mismatched swap: @x2!1 (domain [Term; Universe]) applied as
   (#1:Universe, #0:Term): no definition. *)
let n_sk_bad : expr = App x2_1 [Var 1 universe; Var 0 term]
let n_inst_badswap : expr = mk_and [ht max_ifuel n_sk_bad (Var 0 term); valid (App tag_d [Var 1 universe; Var 0 term; n_sk_bad])]
let c20_sort_mismatched_swap () : Lemma (SK.definition_of n_B n_inst_badswap == None) =
  assert_norm (SK.definition_of n_B n_inst_badswap == None)
