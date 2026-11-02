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

   Every expected value is the checker's own result, computed by
   normalization on well-typed documents. *)

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
