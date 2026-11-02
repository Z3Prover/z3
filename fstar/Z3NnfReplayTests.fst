module Z3NnfReplayTests

(* Tests of the NNF certificate replay (Z3NnfReplay) on the Sorted route.

   A. The local rules, one replayed certificate per constructor family the
      producer (src/ast/normal_forms/nnf.cpp) emits: n-ary De Morgan, double
      negation, implication, Boolean equality, xor, Boolean ite, constants
      and opaque atoms, the positive steps, quantifier duality with
      heterogeneous, nested and repeated binders (reversed de Bruijn order)
      in both directions, and a shared (DAG) entry used at two scopes.
   B. Mutations, each the ACTUAL replay verdict (Unreplayed = the node stays
      pending, Malformed = a rejected proof entry): wrong sign, swapped,
      missing and reused children, wrong target connective, canonical-name
      lookalikes, wrong binder sorts and order, a capturing de Bruijn index,
      wrong polarity under a binder, a bad root, forward, self and negative
      premise ids, the hnf.cpp variant, a quant-intro root, and an inner
      Skolem step that is not a certified choice equation.
   C. Two ACTUAL previously pending corpus certificates (Phase A artifacts,
      dd-producer diagnosis proofs, transcribed entry by entry):
        I1 FStar.Nonempty query 2 node 11 (premise-free nnf-neg: or/3 ->
           and/3 with an exists -> forall duality over a Term binder);
        I2 FStar.Class.TotalOrder.Raw query 1 node 43 (14 entries: a closed
           inner Skolem step, trans, monotonicity, a positive quantifier
           step under a Term binder, double negation, or/2 -> and/2),
      each in a self-contained refutation: the old disjuncts of
      check_node_cached (the only ones master had for this node) fail on
      the node, the replay accepts it, the documents are certified by the
      root gates and falsified in EVERY root model.
   D. A false mutant whose inputs are satisfiable, with a positively proved
      counter-model (a standard root model): the mutant stays pending; a
      malformed certificate rejects its document; a reused Skolem witness
      falls back to the top-level epsilon context and leaves the inner
      Skolem step pending.

   E. The consumed certificate data: the inner choice equation in the
      elaborated assertions, the erased payload left pending, coverage of
      the internal terms and of the scope guard.
   F. Propositional mutants (wrong sign, ite, Boolean equality, xor, double
      negation, wrong n-ary connective): pending, and each claim false in a
      standard root model (proved counter-models).
   G. nnf-pos in the same calculus: positive Boolean equality and xor, an
      nnf-pos root over an nnf-neg duality under binders, and nnf-pos
      mutants (label-only claim with a counter-model, kind change, negative
      body, dual connective, extra child, swapped branches, out-of-scope and
      wrongly sorted indices, self reference).
   H. The duality mutant under HETEROGENEOUS binders [Int; Real] (a positive
      body fact for a negative duality): pending, in a would-be refutation
      of satisfiable inputs, with the positively proved counter-model.

   Every expected failure is the checker's own verdict on a well-typed
   certificate, computed by normalization; none is a parse, effect or
   refinement error. *)

open Z3AstTheory
open Z3ValueTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3Definitions
module L = FStar.List.Tot
module TR = Z3TypedRoot
module SP = Z3SortedProof
module DT = Z3SortedDatatype
module P = Z3ProofDocument
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module O = Z3ObservationalEquality
module NR = Z3NnfReplay
module RD = Z3SortedRootDocument
module PT = Z3SortedProofTests
module RDT = Z3SortedRootDocumentTests
module BR = Z3BooleanRewrite
module B = Z3BoundedBoolEquiv

(* ---------------------------------------------------------------------- *)
(* Shapes                                                                   *)
(* ---------------------------------------------------------------------- *)

let integer : sort = TR.int_s
let real : sort = TR.real_s
let term : sort = BaseSort "Term"

let const (name:string) (s:sort) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = [] } []

let symbol (name:string) (ds:list sort) (r:sort) : func_decl =
  { decl_name = name; domain = ds; range = r; interp = None; int_params = [] }

let rec bools (n:nat) : list sort = if n = 0 then [] else bool_sort :: bools (n - 1)

let conn (name:string) (op:int) (args:list expr) : expr =
  App { decl_name = name; domain = bools (L.length args); range = bool_sort; interp = Some op; int_params = [] } args

let mk_and (args:list expr) : expr = App (BR.connective_decl BR.Conjunction args) args
let mk_or (args:list expr) : expr = App (BR.connective_decl BR.Disjunction args) args
let mk_xor (a b:expr) : expr = conn "xor" op_xor [a; b]
let neg (a:expr) : expr = R.mk_not_expr a
let iff (a b:expr) : expr = App (R.eq_decl bool_sort) [a; b]
let implies (a b:expr) : expr = App SP.implies_decl [a; b]
let ite (c a b:expr) : expr = App (T.ite_decl bool_sort) [c; a; b]
let oeq (a b:expr) : expr = O.mk_oeq_expr a b
let forall_ (bs:list sort) (b:expr) : expr = Quantifier Forall_k bs bool_sort b
let exists_ (bs:list sort) (b:expr) : expr = Quantifier Exists_k bs bool_sort b

let be (name:string) (f:expr) (ps:list int) : U.binder_entry =
  { U.binder_name = name; binder_formula = f; binder_premises = ps; binder_sorts = None }
let bq (name:string) (bs:list sort) (f:expr) (ps:list int) : U.binder_entry =
  { U.binder_name = name; binder_formula = f; binder_premises = ps; binder_sorts = Some bs }
let refl (e:expr) : U.binder_entry = be "refl" (oeq e e) []
let cert (es:list U.binder_entry) (root:int) : U.binder_certificate = { U.binder_entries = es; binder_root = root }

let p : expr = const "p" bool_sort
let q : expr = const "q" bool_sort
let c : expr = const "c" bool_sort
let z : expr = const "z" bool_sort

let replays (c:U.binder_certificate) (lhs rhs:expr) : bool =
  NR.replay [] c (U.Observational lhs rhs) = NR.Replayed

let pending (c:U.binder_certificate) (lhs rhs:expr) : bool =
  NR.replay [] c (U.Observational lhs rhs) = NR.Unreplayed

let malformed (c:U.binder_certificate) (lhs rhs:expr) : bool =
  NR.replay [] c (U.Observational lhs rhs) = NR.Malformed

(* ---------------------------------------------------------------------- *)
(* A. Positive local rules                                                  *)
(* ---------------------------------------------------------------------- *)

(* A1 n-ary De Morgan, children in order, with the skip convention:
   the negative child (not z) is skipped to mk_not((not z)) = z. *)
let a1_src : expr = mk_and [p; neg z; q]
let a1_tgt : expr = mk_or [neg p; z; neg q]
let a1_entries : list U.binder_entry =
  [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 1; 2]]
let a1_demorgan () : Lemma (replays (cert a1_entries 3) (neg a1_src) a1_tgt) =
  assert_norm (replays (cert a1_entries 3) (neg a1_src) a1_tgt)

(* A2 double negation: a positive child under not. *)
let a2_double_negation () : Lemma (replays (cert [refl p; be "nnf-neg" (oeq (neg (neg p)) p) [0]] 1) (neg (neg p)) p) =
  assert_norm (replays (cert [refl p; be "nnf-neg" (oeq (neg (neg p)) p) [0]] 1) (neg (neg p)) p)

(* A3 implication: [positive antecedent, negative consequent]. *)
let a3_tgt : expr = mk_and [p; neg q]
let a3_implies () : Lemma (replays (cert [refl p; refl (neg q); be "nnf-neg" (oeq (neg (implies p q)) a3_tgt) [0; 1]] 2)
                                  (neg (implies p q)) a3_tgt) =
  assert_norm (replays (cert [refl p; refl (neg q); be "nnf-neg" (oeq (neg (implies p q)) a3_tgt) [0; 1]] 2)
                       (neg (implies p q)) a3_tgt)

(* A4/A5 Boolean equality and xor: [P(a), N(a), P(b), N(b)]. *)
let four : list U.binder_entry = [refl p; refl (neg p); refl q; refl (neg q)]
let a4_tgt : expr = mk_and [mk_or [p; q]; mk_or [neg p; neg q]]
let a4_iff () : Lemma (replays (cert (L.append four [be "nnf-neg" (oeq (neg (iff p q)) a4_tgt) [0; 1; 2; 3]]) 4)
                              (neg (iff p q)) a4_tgt) =
  assert_norm (replays (cert (L.append four [be "nnf-neg" (oeq (neg (iff p q)) a4_tgt) [0; 1; 2; 3]]) 4)
                       (neg (iff p q)) a4_tgt)

let a5_tgt : expr = mk_and [mk_or [neg p; q]; mk_or [p; neg q]]
let a5_xor () : Lemma (replays (cert (L.append four [be "nnf-neg" (oeq (neg (mk_xor p q)) a5_tgt) [0; 1; 2; 3]]) 4)
                              (neg (mk_xor p q)) a5_tgt) =
  assert_norm (replays (cert (L.append four [be "nnf-neg" (oeq (neg (mk_xor p q)) a5_tgt) [0; 1; 2; 3]]) 4)
                       (neg (mk_xor p q)) a5_tgt)

(* A6 Boolean ite: [P(c), N(c), N(then), N(else)]. *)
let a6_tgt : expr = mk_and [mk_or [neg c; neg p]; mk_or [c; neg q]]
let a6_entries : list U.binder_entry =
  [refl c; refl (neg c); refl (neg p); refl (neg q); be "nnf-neg" (oeq (neg (ite c p q)) a6_tgt) [0; 1; 2; 3]]
let a6_ite () : Lemma (replays (cert a6_entries 4) (neg (ite c p q)) a6_tgt) =
  assert_norm (replays (cert a6_entries 4) (neg (ite c p q)) a6_tgt)

(* A7 constants (skip: mk_not(true) = false) and an opaque Int predicate. *)
let pk : expr = App (symbol "P" [integer] bool_sort) [const "k" integer]
let a7_src : expr = mk_or [R.true_expr; pk]
let a7_tgt : expr = mk_and [R.false_expr; neg pk]
let a7_constants () : Lemma (replays (cert [refl R.false_expr; refl (neg pk); be "nnf-neg" (oeq (neg a7_src) a7_tgt) [0; 1]] 2)
                                   (neg a7_src) a7_tgt) =
  assert_norm (replays (cert [refl R.false_expr; refl (neg pk); be "nnf-neg" (oeq (neg a7_src) a7_tgt) [0; 1]] 2)
                       (neg a7_src) a7_tgt)

(* A8 positive steps: implication and ite at positive polarity. *)
let a8_implies () : Lemma (replays (cert [refl (neg p); refl q; be "nnf-pos" (oeq (implies p q) (mk_or [neg p; q])) [0; 1]] 2)
                                  (implies p q) (mk_or [neg p; q])) =
  assert_norm (replays (cert [refl (neg p); refl q; be "nnf-pos" (oeq (implies p q) (mk_or [neg p; q])) [0; 1]] 2)
                       (implies p q) (mk_or [neg p; q]))

let a8_ite_tgt : expr = mk_and [mk_or [neg c; p]; mk_or [c; q]]
let a8_ite () : Lemma (replays (cert [refl c; refl (neg c); refl p; refl q;
                                      be "nnf-pos" (oeq (ite c p q) a8_ite_tgt) [0; 1; 2; 3]] 4)
                              (ite c p q) a8_ite_tgt) =
  assert_norm (replays (cert [refl c; refl (neg c); refl p; refl q;
                              be "nnf-pos" (oeq (ite c p q) a8_ite_tgt) [0; 1; 2; 3]] 4)
                       (ite c p q) a8_ite_tgt)

(* A9 quantifier duality, heterogeneous and nested binders, a repeated
   (shadowing) Int binder, reversed de Bruijn order: under [Int; Real] the
   body scope is [Real; Int], so Var 0 is the Real binder and Var 1 the Int
   binder; the inner exists rebinds an Int at Var 0, one scope deeper. *)
let qd : func_decl = symbol "q" [integer; real] bool_sort
let pd : func_decl = symbol "P" [integer] bool_sort
let qxr : expr = App qd [Var 1 integer; Var 0 real]
let p0 : expr = App pd [Var 0 integer]
let a9_body : expr = mk_and [qxr; exists_ [integer] p0]
let a9_tbody : expr = mk_or [neg qxr; forall_ [integer] (neg p0)]
let a9_src : expr = exists_ [integer; real] a9_body
let a9_tgt : expr = forall_ [integer; real] a9_tbody
let a9_entries : list U.binder_entry = [
  refl (neg qxr);                                                            (* scope [Real; Int] *)
  refl (neg p0);                                                             (* scope [Int; Real; Int] *)
  bq "nnf-neg" [integer] (oeq (neg (exists_ [integer] p0)) (forall_ [integer] (neg p0))) [1];
  be "nnf-neg" (oeq (neg a9_body) a9_tbody) [0; 2];
  bq "nnf-neg" [integer; real] (oeq (neg a9_src) a9_tgt) [3]]
let a9_duality () : Lemma (replays (cert a9_entries 4) (neg a9_src) a9_tgt) =
  assert_norm (replays (cert a9_entries 4) (neg a9_src) a9_tgt)

(* A10 the dual direction, not forall -> exists (the rule is general; the
   producer Skolemizes a negative forall instead). *)
let a10_duality () : Lemma (replays (cert [refl (neg p0);
                                           bq "nnf-neg" [integer] (oeq (neg (forall_ [integer] p0)) (exists_ [integer] (neg p0))) [0]] 1)
                                   (neg (forall_ [integer] p0)) (exists_ [integer] (neg p0))) =
  assert_norm (replays (cert [refl (neg p0);
                              bq "nnf-neg" [integer] (oeq (neg (forall_ [integer] p0)) (exists_ [integer] (neg p0))) [0]] 1)
                       (neg (forall_ [integer] p0)) (exists_ [integer] (neg p0)))

(* A11 a shared (DAG) closed entry, refl (not p), used by the root at [] and
   by the body proof at [Int]: the guard checks it at both scopes. *)
let a11_ex : expr = exists_ [integer] (mk_and [p; p0])
let a11_fa : expr = forall_ [integer] (mk_or [neg p; neg p0])
let a11_src : expr = mk_or [p; a11_ex]
let a11_tgt : expr = mk_and [neg p; a11_fa]
let a11_entries : list U.binder_entry = [
  refl (neg p); refl (neg p0);
  be "nnf-neg" (oeq (neg (mk_and [p; p0])) (mk_or [neg p; neg p0])) [0; 1];
  bq "nnf-neg" [integer] (oeq (neg a11_ex) a11_fa) [2];
  be "nnf-neg" (oeq (neg a11_src) a11_tgt) [0; 3]]
let a11_shared () : Lemma (replays (cert a11_entries 4) (neg a11_src) a11_tgt) =
  assert_norm (replays (cert a11_entries 4) (neg a11_src) a11_tgt)

(* ---------------------------------------------------------------------- *)
(* B. Mutations: the actual replay verdicts                                 *)
(* ---------------------------------------------------------------------- *)

(* B1 wrong sign: positive children under nnf-neg, target (and p q). *)
let b1_wrong_sign () : Lemma (pending (cert [refl p; refl q; be "nnf-neg" (oeq (neg (mk_or [p; q])) (mk_and [p; q])) [0; 1]] 2)
                                      (neg (mk_or [p; q])) (mk_and [p; q])) =
  assert_norm (pending (cert [refl p; refl q; be "nnf-neg" (oeq (neg (mk_or [p; q])) (mk_and [p; q])) [0; 1]] 2)
                       (neg (mk_or [p; q])) (mk_and [p; q]))

(* B2 swapped, B3 missing and B4 reused children of A4/A1. *)
let b2_swapped () : Lemma (pending (cert (L.append four [be "nnf-neg" (oeq (neg (iff p q)) a4_tgt) [1; 0; 2; 3]]) 4)
                                   (neg (iff p q)) a4_tgt) =
  assert_norm (pending (cert (L.append four [be "nnf-neg" (oeq (neg (iff p q)) a4_tgt) [1; 0; 2; 3]]) 4)
                       (neg (iff p q)) a4_tgt)

let b3_missing () : Lemma (pending (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 1]] 3)
                                   (neg a1_src) a1_tgt) =
  assert_norm (pending (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 1]] 3)
                       (neg a1_src) a1_tgt)

let b4_reused () : Lemma (pending (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 0; 2]] 3)
                                  (neg a1_src) a1_tgt) =
  assert_norm (pending (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 0; 2]] 3)
                       (neg a1_src) a1_tgt)

(* B5 wrong target connective: and -> and (not the dual). *)
let b5_tgt : expr = mk_and [neg p; z; neg q]
let b5_wrong_connective () : Lemma (pending (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) b5_tgt) [0; 1; 2]] 3)
                                            (neg a1_src) b5_tgt) =
  assert_norm (pending (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) b5_tgt) [0; 1; 2]] 3)
                       (neg a1_src) b5_tgt)

(* B6 canonical-name lookalikes: an uninterpreted "not" and an "or" with an
   integer parameter classify as Other; the steps stay pending. *)
let fake_not (a:expr) : expr = App (symbol "not" [bool_sort] bool_sort) [a]
let fake_or (args:list expr) : expr =
  App { decl_name = "or"; domain = bools (L.length args); range = bool_sort; interp = Some op_or; int_params = [1] } args
let b6_fake_not () : Lemma (pending (cert [refl p; be "nnf-neg" (oeq (neg (fake_not p)) p) [0]] 1) (neg (fake_not p)) p /\
                            pending (cert [refl p; be "nnf-neg" (oeq (fake_not (neg p)) p) [0]] 1) (fake_not (neg p)) p) =
  assert_norm (pending (cert [refl p; be "nnf-neg" (oeq (neg (fake_not p)) p) [0]] 1) (neg (fake_not p)) p);
  assert_norm (pending (cert [refl p; be "nnf-neg" (oeq (fake_not (neg p)) p) [0]] 1) (fake_not (neg p)) p)

let b6_fake_or () : Lemma (pending (cert [refl (neg p); refl (neg q); be "nnf-neg" (oeq (neg (fake_or [p; q])) (mk_and [neg p; neg q])) [0; 1]] 2)
                                   (neg (fake_or [p; q])) (mk_and [neg p; neg q])) =
  assert_norm (pending (cert [refl (neg p); refl (neg q); be "nnf-neg" (oeq (neg (fake_or [p; q])) (mk_and [neg p; neg q])) [0; 1]] 2)
                       (neg (fake_or [p; q])) (mk_and [neg p; neg q]))

(* B7 wrong binders: the target's binder list reversed, and a certificate
   whose binder sorts disagree with the quantifiers. *)
let b7_tgt : expr = forall_ [real; integer] a9_tbody
let b7_wrong_binders ()
  : Lemma (pending (cert (L.append (L.init a9_entries) [bq "nnf-neg" [integer; real] (oeq (neg a9_src) b7_tgt) [3]]) 4)
                   (neg a9_src) b7_tgt /\
           pending (cert (L.append (L.init a9_entries) [bq "nnf-neg" [real; integer] (oeq (neg a9_src) a9_tgt) [3]]) 4)
                   (neg a9_src) a9_tgt) =
  assert_norm (pending (cert (L.append (L.init a9_entries) [bq "nnf-neg" [integer; real] (oeq (neg a9_src) b7_tgt) [3]]) 4)
                       (neg a9_src) b7_tgt);
  assert_norm (pending (cert (L.append (L.init a9_entries) [bq "nnf-neg" [real; integer] (oeq (neg a9_src) a9_tgt) [3]]) 4)
                       (neg a9_src) a9_tgt)

(* B8 a capturing index: q(Var 0, Var 1) with Var 0 annotated Int, which at
   the body scope [Real; Int] is the Real binder. The scope guard rejects
   the certificate. *)
let qbad : expr = App qd [Var 0 integer; Var 1 real]
let b8_body : expr = mk_and [qbad; exists_ [integer] p0]
let b8_tbody : expr = mk_or [neg qbad; forall_ [integer] (neg p0)]
let b8_entries : list U.binder_entry = [
  refl (neg qbad); refl (neg p0);
  bq "nnf-neg" [integer] (oeq (neg (exists_ [integer] p0)) (forall_ [integer] (neg p0))) [1];
  be "nnf-neg" (oeq (neg b8_body) b8_tbody) [0; 2];
  bq "nnf-neg" [integer; real] (oeq (neg (exists_ [integer; real] b8_body)) (forall_ [integer; real] b8_tbody)) [3]]
let b8_capture () : Lemma (pending (cert b8_entries 4) (neg (exists_ [integer; real] b8_body)) (forall_ [integer; real] b8_tbody)) =
  assert_norm (pending (cert b8_entries 4) (neg (exists_ [integer; real] b8_body)) (forall_ [integer; real] b8_tbody))

(* B9 wrong polarity under a binder: a positive body fact for a negative
   duality (the false claim (not (exists x. P x)) ~ (forall x. P x)). *)
let b9_entries : list U.binder_entry =
  [refl p0; bq "nnf-neg" [integer] (oeq (neg (exists_ [integer] p0)) (forall_ [integer] p0)) [0]]
let b9_wrong_polarity () : Lemma (pending (cert b9_entries 1) (neg (exists_ [integer] p0)) (forall_ [integer] p0)) =
  assert_norm (pending (cert b9_entries 1) (neg (exists_ [integer] p0)) (forall_ [integer] p0))

(* B10 bad root (out of range, or not an nnf step): pending. Forward, self,
   negative and missing (past the last entry) premise ids: malformed. The
   boundary is structural only: an unsupported rule with valid ids (B11) and
   a valid id shared by two children (b10_shared) are not malformed. *)
let b10_bad_root ()
  : Lemma (pending (cert a1_entries 7) (neg a1_src) a1_tgt /\
           pending (cert a1_entries 0) (neg a1_src) a1_tgt /\
           pending (cert a1_entries (-1)) (neg a1_src) a1_tgt) =
  assert_norm (pending (cert a1_entries 7) (neg a1_src) a1_tgt);
  assert_norm (pending (cert a1_entries 0) (neg a1_src) a1_tgt);
  assert_norm (pending (cert a1_entries (-1)) (neg a1_src) a1_tgt)

let b10_malformed ()
  : Lemma (malformed (cert [be "refl" (oeq (neg p) (neg p)) [1]; refl z; refl (neg q);
                            be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 1; 2]] 3) (neg a1_src) a1_tgt /\
           malformed (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 1; 3]] 3)
                     (neg a1_src) a1_tgt /\
           malformed (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 1; (-2)]] 3)
                     (neg a1_src) a1_tgt /\
           malformed (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 1; 9]] 3)
                     (neg a1_src) a1_tgt) =
  assert_norm (malformed (cert [be "refl" (oeq (neg p) (neg p)) [1]; refl z; refl (neg q);
                                be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 1; 2]] 3) (neg a1_src) a1_tgt);
  assert_norm (malformed (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 1; 3]] 3)
                         (neg a1_src) a1_tgt);
  assert_norm (malformed (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 1; (-2)]] 3)
                         (neg a1_src) a1_tgt);
  assert_norm (malformed (cert [refl (neg p); refl z; refl (neg q); be "nnf-neg" (oeq (neg a1_src) a1_tgt) [0; 1; 9]] 3)
                         (neg a1_src) a1_tgt)

(* A valid earlier entry used by two children of one step: replayed. *)
let b10_shared ()
  : Lemma (replays (cert [refl (neg p); be "nnf-neg" (oeq (neg (mk_or [p; p])) (mk_and [neg p; neg p])) [0; 0]] 1)
                   (neg (mk_or [p; p])) (mk_and [neg p; neg p])) =
  assert_norm (replays (cert [refl (neg p); be "nnf-neg" (oeq (neg (mk_or [p; p])) (mk_and [neg p; neg p])) [0; 0]] 1)
                       (neg (mk_or [p; p])) (mk_and [neg p; neg p]))

(* B11 the hnf.cpp variant: nnf-neg(q, body, [apply-def]) whose target is
   not the negation of its source; and B12 a quant-intro root (not an NNF
   certificate): both pending. *)
let b11_hnf () : Lemma (pending (cert [be "apply-def" (oeq p0 p0) []; be "nnf-neg" (oeq (neg (exists_ [integer] p0)) p0) [0]] 1)
                                (neg (exists_ [integer] p0)) p0) =
  assert_norm (pending (cert [be "apply-def" (oeq p0 p0) []; be "nnf-neg" (oeq (neg (exists_ [integer] p0)) p0) [0]] 1)
                       (neg (exists_ [integer] p0)) p0)

let b12_quant_intro () : Lemma (pending (cert [refl p0; bq "quant-intro" [integer] (oeq (forall_ [integer] p0) (forall_ [integer] p0)) [0]] 1)
                                        (forall_ [integer] p0) (forall_ [integer] p0)) =
  assert_norm (pending (cert [refl p0; bq "quant-intro" [integer] (oeq (forall_ [integer] p0) (forall_ [integer] p0)) [0]] 1)
                       (forall_ [integer] p0) (forall_ [integer] p0))

(* B13 an inner Skolem step is accepted only as an assertion (on the epsilon
   route: a certified choice equation, see C2); without it the step stays
   pending. An OPEN (dependent) Skolem step is never collected. *)
let sk_c : expr = const "sk!c" integer
let ex_p : expr = exists_ [integer] p0
let pc : expr = App pd [sk_c]
let b13_tgt : expr = mk_or [neg p; pc]
let b13_entries : list U.binder_entry =
  [refl (neg p); be "sk" (oeq ex_p pc) []; be "nnf-pos" (oeq (implies p ex_p) b13_tgt) [0; 1]]
let b13_sk_only_as_assertion ()
  : Lemma (NR.replay [] (cert b13_entries 2) (U.Observational (implies p ex_p) b13_tgt) == NR.Unreplayed /\
           NR.replay [R.mk_eq_expr ex_p pc] (cert b13_entries 2) (U.Observational (implies p ex_p) b13_tgt) ==
             NR.Replayed) =
  assert_norm (NR.replay [] (cert b13_entries 2) (U.Observational (implies p ex_p) b13_tgt) == NR.Unreplayed);
  assert_norm (NR.replay [R.mk_eq_expr ex_p pc] (cert b13_entries 2) (U.Observational (implies p ex_p) b13_tgt) ==
               NR.Replayed)

let skf : func_decl = symbol "sk!f" [integer] integer
let b13_dependent () : Lemma (SP.inner_definition PT.core_schema
                                (be "sk" (oeq (exists_ [integer] (App qd [Var 0 integer; Var 1 real]))
                                              (App qd [App skf [Var 1 integer]; Var 1 real])) []) == None) =
  assert_norm (SP.inner_definition PT.core_schema
                 (be "sk" (oeq (exists_ [integer] (App qd [Var 0 integer; Var 1 real]))
                               (App qd [App skf [Var 1 integer]; Var 1 real])) []) == None)

(* ---------------------------------------------------------------------- *)
(* C. Actual previously pending corpus certificates                         *)
(* ---------------------------------------------------------------------- *)

let entry (r:U.rule) (f:expr) (ids:list int) : P.entry = { P.rule = r; formula = f; premise_ids = ids }

let doc (assertions:list expr) (entries:list P.entry) (root:int) : P.document = {
  P.declarations = []; P.expressions = []; P.assertions = assertions; P.entries = entries; P.root = root;
}

let falsified (u:TR.uninterpreted) (sch:S.checked_schema) (d:P.document) (i:TR.interp u sch) : prop =
  not (RD.root_truths u sch i d.P.assertions)

(* The old disjuncts of check_node_cached for a premise-free node (the only
   ones master had for QuantifierIntroduction): the bounded propositional,
   equality and datatype consequence of no premises. *)
let old_paths (node:U.proof_node) : bool =
  SP.consequence PT.core_schema [] (SP.proposition node.U.conclusion) ||
  DT.consequence PT.core_schema [] (SP.scoped_proposition ({ U.conclusion = node.U.conclusion; hypotheses = [] }))

let fuel : sort = BaseSort "Fuel"
let htf : func_decl = symbol "HasTypeFuel" [fuel; term; term] bool_sort
let max_ifuel : expr = const "MaxIFuel" fuel
let label_1 : expr = const "label_1" bool_sort

(* C1 = I1, FStar.Nonempty (sha256 19da3614...) query 2 node 11. The
   certificate as printed by the labelled diagnostic rerun (@x2716 of
   artifacts/diag/queries-FStar.Nonempty.smt2.proof.txt, patterns dropped as
   the marshal drops them), entries in the marshal's post order:
     (nnf-neg (refl (~ HT HT)) (refl (~ (not label_1) (not label_1)))
              (nnf-neg (proof-bind (lambda ((@x1 Term)) (refl (~ (not B) (not B)))))
                       (~ (not (exists ((@x1 Term)) B)) (forall ((@x1 Term)) (not B))))
              (~ (not (or (not HT) label_1 (exists ((@x1 Term)) B))) (and HT (not label_1) (forall ...))))
   with HT = (HasTypeFuel MaxIFuel @x0!6 (Tm_refine_c30d... uu___13)) and
   B = (HasTypeFuel MaxIFuel @x1 @x0!6). *)
let x0_6 : expr = const "@x0!6" term
let i1_ht : expr =
  App htf [max_ifuel; x0_6; App (symbol "Tm_refine_c30d2f9420b3c7338e3f495ba85ace23" [term] term) [const "uu___13" term]]
let i1_b : expr = App htf [max_ifuel; Var 0 term; x0_6]
let i1_ex : expr = exists_ [term] i1_b
let i1_fa : expr = forall_ [term] (neg i1_b)
let i1_src : expr = mk_or [neg i1_ht; label_1; i1_ex]
let i1_tgt : expr = mk_and [i1_ht; neg label_1; i1_fa]
let i1_cert : U.binder_certificate = cert [
  refl i1_ht; refl (neg label_1); refl (neg i1_b);
  bq "nnf-neg" [term] (oeq (neg i1_ex) i1_fa) [2];
  be "nnf-neg" (oeq (neg i1_src) i1_tgt) [0; 1; 3]] 4
let i1_node : U.proof_node =
  { U.kind = U.QuantifierIntroduction i1_cert; conclusion = U.Observational (neg i1_src) i1_tgt; premises = [] }

let c1_red_then_green ()
  : Lemma (not (old_paths i1_node) /\
           SP.check_node PT.core_schema [] i1_node ==
             Some ({ U.conclusion = U.Observational (neg i1_src) i1_tgt; hypotheses = [] }, 0)) =
  assert_norm (not (old_paths i1_node));
  assert_norm (SP.check_node PT.core_schema [] i1_node ==
               Some ({ U.conclusion = U.Observational (neg i1_src) i1_tgt; hypotheses = [] }, 0))

(* A self-contained refutation around the corpus node: the negated query
   (not (or (not HT) label_1 (exists x. B x))) and B(c) are contradictory. *)
let c_term : expr = const "c" term
let i1_bc : expr = App htf [max_ifuel; c_term; x0_6]
let i1_document : P.document =
  doc [neg i1_src; i1_bc]
      [entry U.Asserted (neg i1_src) [];
       entry (U.QuantifierIntroduction i1_cert) (oeq (neg i1_src) i1_tgt) [];
       entry U.ObservationalMP i1_tgt [0; 1];
       entry (U.QuantifierInstantiation [c_term]) (mk_or [neg i1_fa; neg i1_bc]) [];
       entry U.Asserted i1_bc [];
       entry U.UnitResolution R.false_expr [3; 2; 4]]
      5

let c1_document_certified () : Lemma (RD.check_root_document PT.core_schema i1_document == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema i1_document == RD.RootCertified)

let c1_falsified (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i) (ensures falsified u PT.core_schema i1_document i) =
  c1_document_certified ();
  RD.lemma_root_certified u PT.core_schema i1_document i

(* C2 = I2, FStar.Class.TotalOrder.Raw (sha256 6c884059...) query 1 node 43:
   the 14-entry certificate (diagnostic rerun @x2802's nnf-neg child) with a
   CLOSED inner Skolem step for @x1!2 whose source mentions the top-level
   Skolem constant @x0!1. Q(x0, x1) is the body of `forall @x1`:
     (or (not (and (HasTypeFuel MaxIFuel x1 (Prims.pure_post U_zero order))
                   (forall ((@x2 Term)) (Valid (ApplyTT x1 @x2)))
                   (not (BoxBool_proj_0 (uu___is_Lt x0))) (not (... Eq x0)) (not (... Gt x0))))
         label_1) *)
let universe : sort = BaseSort "Universe"
let order : expr = const "FStar.Order.order" term
let pure_post : expr = App (symbol "Prims.pure_post" [universe; term] term) [const "U_zero" universe; order]
let box (x:expr) : expr = App (symbol "BoxBool_proj_0" [term] bool_sort) [x]
let is_ (name:string) (x:expr) : expr = App (symbol name [term] term) [x]
let valid (x:expr) : expr = App (symbol "Valid" [term] bool_sort) [x]
let apply_tt (x y:expr) : expr = App (symbol "ApplyTT" [term; term] term) [x; y]
let ht (x t:expr) : expr = App htf [max_ifuel; x; t]

(* x1_in is x1 one binder deeper (inside `forall @x2`). *)
let and5 (x0 x1 x1_in:expr) : expr =
  mk_and [ht x1 pure_post; forall_ [term] (valid (apply_tt x1_in (Var 0 term)));
          neg (box (is_ "FStar.Order.uu___is_Lt" x0)); neg (box (is_ "FStar.Order.uu___is_Eq" x0));
          neg (box (is_ "FStar.Order.uu___is_Gt" x0))]
let q_of (x0 x1 x1_in:expr) : expr = mk_or [neg (and5 x0 x1 x1_in); label_1]

let x0_1 : expr = const "@x0!1" term
let x1_2 : expr = const "@x1!2" term
let i2_fa : expr = forall_ [term] (q_of x0_1 (Var 0 term) (Var 1 term))
let i2_s : expr = mk_or [neg (ht x0_1 order); i2_fa]
let i2_q1 : expr = q_of x0_1 x1_2 x1_2
let i2_and5 : expr = and5 x0_1 x1_2 x1_2
let i2_v : expr = forall_ [term] (valid (apply_tt x1_2 (Var 0 term)))
let i2_t1 : expr = mk_and [i2_and5; neg label_1]
let i2_t : expr = mk_and [ht x0_1 order; i2_t1]
let i2_inner_sk : expr = oeq (neg i2_fa) (neg i2_q1)
let i2_cert : U.binder_certificate = cert [
  refl (ht x0_1 order);                                              (* 0 *)
  be "sk" i2_inner_sk [];                                            (* 1 *)
  refl (ht x1_2 pure_post);                                          (* 2 *)
  refl (valid (apply_tt x1_2 (Var 0 term)));                         (* 3, scope [Term] *)
  bq "nnf-pos" [term] (oeq i2_v i2_v) [3];                           (* 4 *)
  refl (neg (box (is_ "FStar.Order.uu___is_Lt" x0_1)));              (* 5 *)
  refl (neg (box (is_ "FStar.Order.uu___is_Eq" x0_1)));              (* 6 *)
  refl (neg (box (is_ "FStar.Order.uu___is_Gt" x0_1)));              (* 7 *)
  be "monotonicity" (oeq i2_and5 i2_and5) [2; 4; 5; 6; 7];           (* 8 *)
  be "nnf-neg" (oeq (neg (neg i2_and5)) i2_and5) [8];                (* 9 *)
  refl (neg label_1);                                                (* 10 *)
  be "nnf-neg" (oeq (neg i2_q1) i2_t1) [9; 10];                      (* 11 *)
  be "trans" (oeq (neg i2_fa) i2_t1) [1; 11];                        (* 12 *)
  be "nnf-neg" (oeq (neg i2_s) i2_t) [0; 12]] 13                     (* 13 *)

(* The negated query, its top-level Skolem step to @x0!1, and a
   contradicting input forall x. not HT(x, order). *)
let i2_a0 : expr =
  neg (forall_ [term] (mk_or [neg (ht (Var 0 term) order); forall_ [term] (q_of (Var 1 term) (Var 0 term) (Var 1 term))]))
let i2_f : expr = forall_ [term] (neg (ht (Var 0 term) order))

let i2_document_with (assertions:list expr) : P.document =
  doc assertions
      [entry U.Asserted i2_a0 [];
       entry U.Skolemization (oeq i2_a0 (neg i2_s)) [];
       entry (U.QuantifierIntroduction i2_cert) (oeq (neg i2_s) i2_t) [];
       entry U.Transitivity (oeq i2_a0 i2_t) [1; 2];
       entry U.ObservationalMP i2_t [0; 3];
       entry U.Asserted i2_f [];
       entry (U.QuantifierInstantiation [x0_1]) (mk_or [neg i2_f; neg (ht x0_1 order)]) [];
       entry U.UnitResolution R.false_expr [6; 5; 4]]
      7

let i2_document : P.document = i2_document_with [i2_a0; i2_f]

let i2_node : U.proof_node =
  { U.kind = U.QuantifierIntroduction i2_cert; conclusion = U.Observational (neg i2_s) i2_t; premises = [] }

(* Red: the old paths fail on the node; without the choice equation of the
   inner Skolem step the replay leaves it pending too. Green: with the
   equation (as the epsilon route supplies it) the node is checked. *)
let c2_node ()
  : Lemma (not (old_paths i2_node) /\
           SP.check_node PT.core_schema [] i2_node ==
             Some ({ U.conclusion = U.Observational (neg i2_s) i2_t; hypotheses = [] }, 1) /\
           SP.check_node PT.core_schema [R.mk_eq_expr (neg i2_fa) (neg i2_q1)] i2_node ==
             Some ({ U.conclusion = U.Observational (neg i2_s) i2_t; hypotheses = [] }, 0)) =
  assert_norm (not (old_paths i2_node));
  assert_norm (SP.check_node PT.core_schema [] i2_node ==
               Some ({ U.conclusion = U.Observational (neg i2_s) i2_t; hypotheses = [] }, 1));
  assert_norm (SP.check_node PT.core_schema [R.mk_eq_expr (neg i2_fa) (neg i2_q1)] i2_node ==
               Some ({ U.conclusion = U.Observational (neg i2_s) i2_t; hypotheses = [] }, 0))

(* The plain route leaves the top-level Skolem step and the certificate
   open; the epsilon route collects BOTH definitions (the inner one from the
   certificate, ordered after the top-level one whose witness its source
   mentions) and certifies the document. *)
let c2_plain_pending () : Lemma (SP.check_document PT.core_schema i2_document == Some 2) =
  assert_norm (SP.check_document PT.core_schema i2_document == Some 2)

let c2_context () : Lemma (L.length (SP.epsilon_context PT.core_schema i2_document) == 2) =
  assert_norm (L.length (SP.epsilon_context PT.core_schema i2_document) == 2)

let c2_epsilon_certified ()
  : Lemma (RD.check_root_document_epsilon PT.core_schema i2_document == RD.RootCertified) =
  assert_norm (RD.check_root_document_epsilon PT.core_schema i2_document == RD.RootCertified)

let c2_falsified (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema i2_document i /\
                   TR.root_model u PT.core_schema (RD.epsilon_extension u PT.core_schema i i2_document)) =
  c2_epsilon_certified ();
  RD.lemma_root_certified_epsilon u PT.core_schema i2_document i;
  RD.lemma_root_epsilon_extension u PT.core_schema i i2_document

(* ---------------------------------------------------------------------- *)
(* D. False mutant, malformed certificate, witness reuse                    *)
(* ---------------------------------------------------------------------- *)

(* D1 the wrong-polarity mutant of B9, (not (exists x. P x)) ~ (forall x. P x),
   in a would-be refutation of the SATISFIABLE inputs (not (exists x. P x))
   and (not (P k)): the node stays pending, so the document is not
   certified. *)
let kc : expr = const "k" integer
let d1_a : expr = neg (exists_ [integer] p0)
let d1_b : expr = neg (App pd [kc])
let d1_document : P.document =
  doc [d1_a; d1_b]
      [entry U.Asserted d1_a [];
       entry (U.QuantifierIntroduction (cert b9_entries 1)) (oeq d1_a (forall_ [integer] p0)) [];
       entry U.ObservationalMP (forall_ [integer] p0) [0; 1];
       entry (U.QuantifierInstantiation [kc]) (mk_or [neg (forall_ [integer] p0); App pd [kc]]) [];
       entry U.Asserted d1_b [];
       entry U.UnitResolution R.false_expr [3; 2; 4]]
      5

let d1_mutant_pending ()
  : Lemma (RD.check_root_document_epsilon PT.core_schema d1_document == RD.RootPending 1) =
  assert_norm (RD.check_root_document_epsilon PT.core_schema d1_document == RD.RootPending 1)

(* The positive counter-model: in the standard root model that interprets
   every free Boolean symbol as false (for every u), both inputs hold. *)
let lemma_p_false (u:TR.uninterpreted) (scope:list sort)
                  (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope) (arg:expr)
  : Lemma (requires D.scoped scope (App pd [arg]))
          (ensures TR.truth PT.core_schema
                     (V.evaluate (S.signature PT.core_schema)
                        (TR.standard u PT.core_schema (RDT.uf_bool u false)) scope rho (App pd [arg])) == false) =
  assert_norm (TR.classify (S.signature PT.core_schema) pd == TR.Other);
  TR.lemma_eval_free_choice u PT.core_schema (RDT.uf_bool u false) scope rho pd [arg]

let lemma_not_value (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
                    (scope:list sort) (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope) (x:expr)
  : Lemma (requires TR.root_model u PT.core_schema i /\ D.scoped scope (neg x))
          (ensures TR.truth PT.core_schema (V.evaluate (S.signature PT.core_schema) i scope rho (neg x)) ==
                   not (TR.truth PT.core_schema (V.evaluate (S.signature PT.core_schema) i scope rho x))) =
  TR.lemma_classify_booleans (S.signature PT.core_schema) bool_sort;
  assert (TR.classify (S.signature PT.core_schema) R.not_decl == TR.Negation);
  TR.lemma_not_registered PT.core_schema R.not_decl;
  TR.lemma_eval_application i scope rho R.not_decl [x];
  let v = V.evaluate (S.signature PT.core_schema) i scope rho x in
  assert (V.evaluate_args (S.signature PT.core_schema) i scope rho [x] R.not_decl.domain == [v]);
  TR.law_not i R.not_decl v

let d1_counter_model (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (TR.standard u PT.core_schema (RDT.uf_bool u false)) /\
           RD.root_truths u PT.core_schema (TR.standard u PT.core_schema (RDT.uf_bool u false)) d1_document.P.assertions) =
  let sch = PT.core_schema in
  let i = TR.standard u sch (RDT.uf_bool u false) in
  let sigma = S.signature sch in
  let empty = RD.empty_root u sch in
  TR.lemma_standard_root u sch (RDT.uf_bool u false);
  (* (not (P k)) *)
  lemma_p_false u [] empty kc;
  lemma_not_value u i [] empty (App pd [kc]);
  (* (not (exists x. P x)): no witness *)
  let none (vs:TR.targuments u sch (L.rev [integer]))
    : Lemma (TR.truth sch (V.evaluate sigma i (L.append (L.rev [integer]) [])
               (V.extend sigma [] (L.rev [integer]) vs empty) p0) == false) =
    lemma_p_false u (L.append (L.rev [integer]) []) (V.extend sigma [] (L.rev [integer]) vs empty) (Var 0 integer) in
  FStar.Classical.forall_intro none;
  TR.lemma_eval_exists i [] empty [integer] p0;
  lemma_not_value u i [] empty (exists_ [integer] p0)

(* D2 a malformed certificate (a forward premise id) rejects its document:
   a semantic rejection of the proof entry, not a pending obligation. *)
let i1_forward : U.binder_certificate = cert [
  refl i1_ht; refl (neg label_1); refl (neg i1_b);
  bq "nnf-neg" [term] (oeq (neg i1_ex) i1_fa) [4];
  be "nnf-neg" (oeq (neg i1_src) i1_tgt) [0; 1; 3]] 4
let d2_document : P.document =
  doc [neg i1_src; i1_bc]
      [entry U.Asserted (neg i1_src) [];
       entry (U.QuantifierIntroduction i1_forward) (oeq (neg i1_src) i1_tgt) [];
       entry U.ObservationalMP i1_tgt [0; 1];
       entry (U.QuantifierInstantiation [c_term]) (mk_or [neg i1_fa; neg i1_bc]) [];
       entry U.Asserted i1_bc [];
       entry U.UnitResolution R.false_expr [3; 2; 4]]
      5
let d2_malformed_rejected () : Lemma (RD.check_root_document_epsilon PT.core_schema d2_document == RD.RootRejected) =
  assert_norm (RD.check_root_document_epsilon PT.core_schema d2_document == RD.RootRejected)

(* D3 the inner witness @x1!2 occurs in an original input: the merged epsilon
   context fails the freshness gate, the top-level context (one definition)
   is used, and the certificate, replayed against the elaborated assertions
   of exactly this document, stays pending (its inner Skolem step has no
   choice equation). Decomposed into the context and the replay of the
   elaborated node instead of one normalized run of the whole document. *)
let d3_document : P.document = i2_document_with [i2_a0; i2_f; R.mk_eq_expr x1_2 x1_2]

let d3_merged_context_rejected ()
  : Lemma (SP.certified_context PT.core_schema d3_document (SP.collect_merged PT.core_schema [] d3_document.P.entries) == [] /\
           L.length (SP.epsilon_context PT.core_schema d3_document) == 1) =
  assert_norm (SP.certified_context PT.core_schema d3_document (SP.collect_merged PT.core_schema [] d3_document.P.entries) == []);
  assert_norm (L.length (SP.epsilon_context PT.core_schema d3_document) == 1)

let d3_reused_witness_pending ()
  : Lemma (NR.replay (SP.elaborate_epsilon PT.core_schema (SP.epsilon_context PT.core_schema d3_document) d3_document).P.assertions
             i2_cert (U.Observational (neg i2_s) i2_t) == NR.Unreplayed) =
  assert_norm (NR.replay (SP.elaborate_epsilon PT.core_schema (SP.epsilon_context PT.core_schema d3_document) d3_document).P.assertions
                 i2_cert (U.Observational (neg i2_s) i2_t) == NR.Unreplayed)

(* ---------------------------------------------------------------------- *)
(* E. The consumed certificate data                                         *)
(* ---------------------------------------------------------------------- *)

(* E1 the epsilon route collects the inner definition from the ACTUAL
   certificate: its choice equation is an assertion of the elaborated I2
   document, next to the top-level one. *)
let e1_inner_equation_elaborated ()
  : Lemma (L.mem (R.mk_eq_expr (neg i2_fa) (neg i2_q1))
                 (SP.elaborate_epsilon PT.core_schema (SP.epsilon_context PT.core_schema i2_document) i2_document).P.assertions /\
           L.mem (R.mk_eq_expr i2_a0 (neg i2_s))
                 (SP.elaborate_epsilon PT.core_schema (SP.epsilon_context PT.core_schema i2_document) i2_document).P.assertions) =
  assert_norm (L.mem (R.mk_eq_expr (neg i2_fa) (neg i2_q1))
                 (SP.elaborate_epsilon PT.core_schema (SP.epsilon_context PT.core_schema i2_document) i2_document).P.assertions);
  assert_norm (L.mem (R.mk_eq_expr i2_a0 (neg i2_s))
                 (SP.elaborate_epsilon PT.core_schema (SP.epsilon_context PT.core_schema i2_document) i2_document).P.assertions)

(* E2 the payload is consumed: the I1 node with its certificate erased (the
   previous read view's `payload-erased`) stays pending; the read view now
   keeps the certificate. *)
let e2_payload_consumed ()
  : Lemma (RD.rule_shape (U.QuantifierIntroduction i1_cert) == U.QuantifierIntroduction i1_cert /\
           SP.check_node PT.core_schema [] ({ i1_node with U.kind = U.Unverified "payload-erased" }) ==
             Some ({ U.conclusion = U.Observational (neg i1_src) i1_tgt; hypotheses = [] }, 1)) =
  assert_norm (RD.rule_shape (U.QuantifierIntroduction i1_cert) == U.QuantifierIntroduction i1_cert);
  assert_norm (SP.check_node PT.core_schema [] ({ i1_node with U.kind = U.Unverified "payload-erased" }) ==
               Some ({ U.conclusion = U.Observational (neg i1_src) i1_tgt; hypotheses = [] }, 1))

(* E3 coverage reads the consumed certificate: the I1/I2 certificates are
   covered; an unsupported internal term (a zero-index array constant in an
   entry the root does not even use) or a certificate failing the scope
   guard (B8) is not; a certificate the replay does not consume (B12) is not
   gated. *)
let zero_index : expr = const "zero-index" (ArraySort [] integer)
let e3_coverage ()
  : Lemma (RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction i1_cert) /\
           RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction i2_cert) /\
           not (RD.certificate_covered (S.signature PT.core_schema)
                  (U.QuantifierIntroduction (cert (L.append a1_entries [refl (R.mk_eq_expr zero_index zero_index)]) 3))) /\
           not (RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction (cert b8_entries 4))) /\
           RD.certificate_covered (S.signature PT.core_schema)
             (U.QuantifierIntroduction (cert [refl p0; bq "quant-intro" [integer] (oeq (forall_ [integer] p0) (forall_ [integer] p0)) [0]] 1))) =
  assert_norm (RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction i1_cert));
  assert_norm (RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction i2_cert));
  assert_norm (not (RD.certificate_covered (S.signature PT.core_schema)
                      (U.QuantifierIntroduction (cert (L.append a1_entries [refl (R.mk_eq_expr zero_index zero_index)]) 3))));
  assert_norm (not (RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction (cert b8_entries 4))));
  assert_norm (RD.certificate_covered (S.signature PT.core_schema)
                 (U.QuantifierIntroduction (cert [refl p0; bq "quant-intro" [integer] (oeq (forall_ [integer] p0) (forall_ [integer] p0)) [0]] 1)))

(* ---------------------------------------------------------------------- *)
(* F. Propositional mutants: pending, and FALSE in a standard root model    *)
(* ---------------------------------------------------------------------- *)

(* Each mutant certificate claims a false equation: in the standard root
   model that interprets every free Boolean constant as b (for every u), the
   claimed `lhs = rhs` is false (computed through T.cut and the root truth),
   so a replay that accepted it would be unsound. *)
let model (u:TR.uninterpreted) (b:bool) : TR.interp u PT.core_schema =
  TR.standard u PT.core_schema (RDT.uf_bool u b)

let lemma_atom (u:TR.uninterpreted) (b:bool) (f:func_decl)
  : Lemma (requires TR.classify (S.signature PT.core_schema) f == TR.Other /\ f.interp == None /\
                    f.domain == [] /\ f.range == bool_sort /\ f.int_params == [])
          (ensures T.truth PT.core_schema (TR.booleans u) (Z3SortedRoot.root_scalars u) (model u b) (App f []) == b) =
  TR.lemma_standard_root u PT.core_schema (RDT.uf_bool u b);
  RD.lemma_holds_agreement u PT.core_schema (model u b) (App f []);
  TR.lemma_eval_free_choice u PT.core_schema (RDT.uf_bool u b) [] (RD.empty_root u PT.core_schema) f []

let lemma_false_claim (u:TR.uninterpreted) (b:bool) (lhs rhs:expr) (skel:B.skeleton)
  : Lemma (requires D.scoped [] (R.mk_eq_expr lhs rhs) /\ get_sort (R.mk_eq_expr lhs rhs) == bool_sort /\
                    T.cut 64 (R.mk_eq_expr lhs rhs) == skel /\
                    B.geval (T.truth PT.core_schema (TR.booleans u) (Z3SortedRoot.root_scalars u) (model u b)) skel == false)
          (ensures TR.root_model u PT.core_schema (model u b) /\
                   not (RD.root_holds u PT.core_schema (model u b) (R.mk_eq_expr lhs rhs))) =
  TR.lemma_standard_root u PT.core_schema (RDT.uf_bool u b);
  T.lemma_cut PT.core_schema (TR.booleans u) (Z3SortedRoot.root_scalars u) (model u b) 64 (R.mk_eq_expr lhs rhs);
  RD.lemma_holds_agreement u PT.core_schema (model u b) (R.mk_eq_expr lhs rhs)

let decl_of (e:expr) : func_decl = match e with App f _ -> f | _ -> R.not_decl

let lemma_atoms (u:TR.uninterpreted) (b:bool)
  : Lemma (T.truth PT.core_schema (TR.booleans u) (Z3SortedRoot.root_scalars u) (model u b) p == b /\
           T.truth PT.core_schema (TR.booleans u) (Z3SortedRoot.root_scalars u) (model u b) q == b /\
           T.truth PT.core_schema (TR.booleans u) (Z3SortedRoot.root_scalars u) (model u b) c == b) =
  assert_norm (TR.classify (S.signature PT.core_schema) (decl_of p) == TR.Other);
  assert_norm (TR.classify (S.signature PT.core_schema) (decl_of q) == TR.Other);
  assert_norm (TR.classify (S.signature PT.core_schema) (decl_of c) == TR.Other);
  lemma_atom u b (decl_of p); lemma_atom u b (decl_of q); lemma_atom u b (decl_of c)

(* F1 De Morgan with the wrong sign (B1): not (or p q) ~ (and p q), false
   when p and q hold. *)
let f1_wrong_sign_false (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u true) /\
           not (RD.root_holds u PT.core_schema (model u true) (R.mk_eq_expr (neg (mk_or [p; q])) (mk_and [p; q])))) =
  lemma_atoms u true;
  assert_norm (D.scoped [] (R.mk_eq_expr (neg (mk_or [p; q])) (mk_and [p; q])));
  assert_norm (T.cut 64 (R.mk_eq_expr (neg (mk_or [p; q])) (mk_and [p; q])) ==
               B.Eq (B.Not (B.Nary B.Or [B.Atom p; B.Atom q])) (B.Nary B.And [B.Atom p; B.Atom q]));
  lemma_false_claim u true (neg (mk_or [p; q])) (mk_and [p; q])
    (B.Eq (B.Not (B.Nary B.Or [B.Atom p; B.Atom q])) (B.Nary B.And [B.Atom p; B.Atom q]))

(* F2 ite with positive branches under nnf-neg: pending, and the claim
   (not (ite c p q)) ~ (ite-shape c p q) is false in every valuation. *)
let f2_entries : list U.binder_entry =
  [refl c; refl (neg c); refl p; refl q; be "nnf-neg" (oeq (neg (ite c p q)) a8_ite_tgt) [0; 1; 2; 3]]
let f2_ite_mutant ()
  : Lemma (pending (cert f2_entries 4) (neg (ite c p q)) a8_ite_tgt) =
  assert_norm (pending (cert f2_entries 4) (neg (ite c p q)) a8_ite_tgt)

let f2_ite_false (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u true) /\
           not (RD.root_holds u PT.core_schema (model u true) (R.mk_eq_expr (neg (ite c p q)) a8_ite_tgt))) =
  let skel = B.Eq (B.Not (B.Nary B.Or [B.Nary B.And [B.Atom c; B.Atom p]; B.Nary B.And [B.Not (B.Atom c); B.Atom q]]))
                  (B.Nary B.And [B.Nary B.Or [B.Not (B.Atom c); B.Atom p]; B.Nary B.Or [B.Atom c; B.Atom q]]) in
  lemma_atoms u true;
  assert_norm (D.scoped [] (R.mk_eq_expr (neg (ite c p q)) a8_ite_tgt));
  assert_norm (T.cut 64 (R.mk_eq_expr (neg (ite c p q)) a8_ite_tgt) == skel);
  lemma_false_claim u true (neg (ite c p q)) a8_ite_tgt skel

(* F3 Boolean equality with the xor shape and F4 xor with the equality shape
   (swapped target shapes): pending, and each false when p and q hold. *)
let f3_iff_mutant ()
  : Lemma (pending (cert (L.append four [be "nnf-neg" (oeq (neg (iff p q)) a5_tgt) [0; 1; 2; 3]]) 4) (neg (iff p q)) a5_tgt /\
           pending (cert (L.append four [be "nnf-neg" (oeq (neg (mk_xor p q)) a4_tgt) [0; 1; 2; 3]]) 4) (neg (mk_xor p q)) a4_tgt) =
  assert_norm (pending (cert (L.append four [be "nnf-neg" (oeq (neg (iff p q)) a5_tgt) [0; 1; 2; 3]]) 4) (neg (iff p q)) a5_tgt);
  assert_norm (pending (cert (L.append four [be "nnf-neg" (oeq (neg (mk_xor p q)) a4_tgt) [0; 1; 2; 3]]) 4) (neg (mk_xor p q)) a4_tgt)

let f3_iff_false (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u true) /\
           not (RD.root_holds u PT.core_schema (model u true) (R.mk_eq_expr (neg (iff p q)) a5_tgt))) =
  let s1 = B.Eq (B.Not (B.Eq (B.Atom p) (B.Atom q)))
                (B.Nary B.And [B.Nary B.Or [B.Not (B.Atom p); B.Atom q]; B.Nary B.Or [B.Atom p; B.Not (B.Atom q)]]) in
  lemma_atoms u true;
  assert_norm (D.scoped [] (R.mk_eq_expr (neg (iff p q)) a5_tgt));
  assert_norm (T.cut 64 (R.mk_eq_expr (neg (iff p q)) a5_tgt) == s1);
  lemma_false_claim u true (neg (iff p q)) a5_tgt s1

let f4_xor_false (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u true) /\
           not (RD.root_holds u PT.core_schema (model u true) (R.mk_eq_expr (neg (mk_xor p q)) a4_tgt))) =
  let tp = T.truth PT.core_schema (TR.booleans u) (Z3SortedRoot.root_scalars u) (model u true) in
  let s2 = B.Eq (B.Not (B.Nary B.Xor [B.Atom p; B.Atom q]))
                (B.Nary B.And [B.Nary B.Or [B.Atom p; B.Atom q]; B.Nary B.Or [B.Not (B.Atom p); B.Not (B.Atom q)]]) in
  lemma_atoms u true;
  assert (B.geval tp (B.Nary B.Xor [B.Atom p; B.Atom q]) == false);
  assert (B.geval tp (B.Nary B.Or [B.Not (B.Atom p); B.Not (B.Atom q)]) == false);
  assert (B.geval tp s2 == false);
  assert_norm (D.scoped [] (R.mk_eq_expr (neg (mk_xor p q)) a4_tgt));
  assert_norm (T.cut 64 (R.mk_eq_expr (neg (mk_xor p q)) a4_tgt) == s2);
  lemma_false_claim u true (neg (mk_xor p q)) a4_tgt s2

(* F5 double negation read as a negative child: (not (not p)) ~ (not p). *)
let f5_double_negation_mutant ()
  : Lemma (pending (cert [refl (neg p); be "nnf-neg" (oeq (neg (neg p)) (neg p)) [0]] 1) (neg (neg p)) (neg p)) =
  assert_norm (pending (cert [refl (neg p); be "nnf-neg" (oeq (neg (neg p)) (neg p)) [0]] 1) (neg (neg p)) (neg p))

let f5_double_negation_false (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u true) /\
           not (RD.root_holds u PT.core_schema (model u true) (R.mk_eq_expr (neg (neg p)) (neg p)))) =
  let skel = B.Eq (B.Not (B.Not (B.Atom p))) (B.Not (B.Atom p)) in
  lemma_atoms u true;
  assert_norm (D.scoped [] (R.mk_eq_expr (neg (neg p)) (neg p)));
  assert_norm (T.cut 64 (R.mk_eq_expr (neg (neg p)) (neg p)) == skel);
  lemma_false_claim u true (neg (neg p)) (neg p) skel

(* F6 the n-ary mutant B5 (and -> and), false when p, z, q are all false. *)
let f6_wrong_connective_false (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u false) /\
           not (RD.root_holds u PT.core_schema (model u false) (R.mk_eq_expr (neg a1_src) b5_tgt))) =
  let skel = B.Eq (B.Not (B.Nary B.And [B.Atom p; B.Not (B.Atom z); B.Atom q]))
                  (B.Nary B.And [B.Not (B.Atom p); B.Atom z; B.Not (B.Atom q)]) in
  lemma_atoms u false;
  assert_norm (TR.classify (S.signature PT.core_schema) (decl_of z) == TR.Other);
  lemma_atom u false (decl_of z);
  assert_norm (D.scoped [] (R.mk_eq_expr (neg a1_src) b5_tgt));
  assert_norm (T.cut 64 (R.mk_eq_expr (neg a1_src) b5_tgt) == skel);
  lemma_false_claim u false (neg a1_src) b5_tgt skel

(* ---------------------------------------------------------------------- *)
(* G. nnf-pos: the positive steps in the same calculus                      *)
(* ---------------------------------------------------------------------- *)

(* G1/G2 positive Boolean equality and xor (nnf.cpp process_iff_xor at
   positive polarity), children [P(a), N(a), P(b), N(b)]. *)
let g1_tgt : expr = mk_and [mk_or [neg p; q]; mk_or [p; neg q]]
let g2_tgt : expr = mk_and [mk_or [p; q]; mk_or [neg p; neg q]]
let g1_g2_positive ()
  : Lemma (replays (cert (L.append four [be "nnf-pos" (oeq (iff p q) g1_tgt) [0; 1; 2; 3]]) 4) (iff p q) g1_tgt /\
           replays (cert (L.append four [be "nnf-pos" (oeq (mk_xor p q) g2_tgt) [0; 1; 2; 3]]) 4) (mk_xor p q) g2_tgt) =
  assert_norm (replays (cert (L.append four [be "nnf-pos" (oeq (iff p q) g1_tgt) [0; 1; 2; 3]]) 4) (iff p q) g1_tgt);
  assert_norm (replays (cert (L.append four [be "nnf-pos" (oeq (mk_xor p q) g2_tgt) [0; 1; 2; 3]]) 4) (mk_xor p q) g2_tgt)

(* G3 an nnf-pos ROOT over an nnf-neg duality under a binder (the shape of
   `forall w. not (exists x r. q(x, r) and P(w))`): the root reads its body at
   [Int], the duality reads its body at [Real; Int; Int], where Var 2 is w. *)
let pw : expr = App pd [Var 2 integer]
let g3_body : expr = mk_and [qxr; pw]
let g3_tbody : expr = mk_or [neg qxr; neg pw]
let g3_src : expr = forall_ [integer] (neg (exists_ [integer; real] g3_body))
let g3_tgt : expr = forall_ [integer] (forall_ [integer; real] g3_tbody)
let g3_entries : list U.binder_entry = [
  refl (neg qxr); refl (neg pw);
  be "nnf-neg" (oeq (neg g3_body) g3_tbody) [0; 1];
  bq "nnf-neg" [integer; real] (oeq (neg (exists_ [integer; real] g3_body)) (forall_ [integer; real] g3_tbody)) [2];
  bq "nnf-pos" [integer] (oeq g3_src g3_tgt) [3]]
let g3_positive_root () : Lemma (replays (cert g3_entries 4) g3_src g3_tgt) =
  assert_norm (replays (cert g3_entries 4) g3_src g3_tgt)

(* G4 nnf-pos mutants: a label-only claim (implication read as disjunction),
   a quantifier kind change, a negative body fact under nnf-pos, a dual
   connective, an extra child, swapped ite branches, an out-of-scope index
   and a wrongly sorted index under the binders, a self reference. *)
let g4_label_only ()
  : Lemma (pending (cert [refl p; refl q; be "nnf-pos" (oeq (implies p q) (mk_or [p; q])) [0; 1]] 2)
                   (implies p q) (mk_or [p; q])) =
  assert_norm (pending (cert [refl p; refl q; be "nnf-pos" (oeq (implies p q) (mk_or [p; q])) [0; 1]] 2)
                       (implies p q) (mk_or [p; q]))

let g4_label_only_false (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (model u false) /\
           not (RD.root_holds u PT.core_schema (model u false) (R.mk_eq_expr (implies p q) (mk_or [p; q])))) =
  let skel = B.Eq (B.Implies (B.Atom p) (B.Atom q)) (B.Nary B.Or [B.Atom p; B.Atom q]) in
  lemma_atoms u false;
  assert_norm (D.scoped [] (R.mk_eq_expr (implies p q) (mk_or [p; q])));
  assert_norm (T.cut 64 (R.mk_eq_expr (implies p q) (mk_or [p; q])) == skel);
  lemma_false_claim u false (implies p q) (mk_or [p; q]) skel

let g4_quantifier_mutants ()
  : Lemma (pending (cert [refl p0; bq "nnf-pos" [integer] (oeq (forall_ [integer] p0) (exists_ [integer] p0)) [0]] 1)
                   (forall_ [integer] p0) (exists_ [integer] p0) /\
           pending (cert [refl (neg p0); bq "nnf-pos" [integer] (oeq (forall_ [integer] p0) (forall_ [integer] (neg p0))) [0]] 1)
                   (forall_ [integer] p0) (forall_ [integer] (neg p0)) /\
           pending (cert [refl p0; bq "nnf-pos" [real] (oeq (forall_ [integer] p0) (forall_ [integer] p0)) [0]] 1)
                   (forall_ [integer] p0) (forall_ [integer] p0)) =
  assert_norm (pending (cert [refl p0; bq "nnf-pos" [integer] (oeq (forall_ [integer] p0) (exists_ [integer] p0)) [0]] 1)
                       (forall_ [integer] p0) (exists_ [integer] p0));
  assert_norm (pending (cert [refl (neg p0); bq "nnf-pos" [integer] (oeq (forall_ [integer] p0) (forall_ [integer] (neg p0))) [0]] 1)
                       (forall_ [integer] p0) (forall_ [integer] (neg p0)));
  assert_norm (pending (cert [refl p0; bq "nnf-pos" [real] (oeq (forall_ [integer] p0) (forall_ [integer] p0)) [0]] 1)
                       (forall_ [integer] p0) (forall_ [integer] p0))

let g4_boolean_mutants ()
  : Lemma (pending (cert [refl p; refl q; be "nnf-pos" (oeq (mk_and [p; q]) (mk_or [p; q])) [0; 1]] 2)
                   (mk_and [p; q]) (mk_or [p; q]) /\
           pending (cert (L.append four [refl q; be "nnf-pos" (oeq (iff p q) g1_tgt) [0; 1; 2; 3; 4]]) 5) (iff p q) g1_tgt /\
           pending (cert [refl c; refl (neg c); refl p; refl q;
                          be "nnf-pos" (oeq (ite c p q) (mk_and [mk_or [neg c; q]; mk_or [c; p]])) [0; 1; 2; 3]] 4)
                   (ite c p q) (mk_and [mk_or [neg c; q]; mk_or [c; p]])) =
  assert_norm (pending (cert [refl p; refl q; be "nnf-pos" (oeq (mk_and [p; q]) (mk_or [p; q])) [0; 1]] 2)
                       (mk_and [p; q]) (mk_or [p; q]));
  assert_norm (pending (cert (L.append four [refl q; be "nnf-pos" (oeq (iff p q) g1_tgt) [0; 1; 2; 3; 4]]) 5) (iff p q) g1_tgt);
  assert_norm (pending (cert [refl c; refl (neg c); refl p; refl q;
                              be "nnf-pos" (oeq (ite c p q) (mk_and [mk_or [neg c; q]; mk_or [c; p]])) [0; 1; 2; 3]] 4)
                       (ite c p q) (mk_and [mk_or [neg c; q]; mk_or [c; p]]))

(* Under the G3 binders: Var 3 is out of scope, and Var 2 annotated Real
   disagrees with the Int binder w; a self reference is malformed. *)
let g3_parts (w:expr) : expr & expr =
  let pw' = App (symbol "P" [get_sort w] bool_sort) [w] in
  mk_and [qxr; pw'], mk_or [neg qxr; neg pw']

let g3_with (w:expr) (self:bool) : list U.binder_entry =
  let body, tbody = g3_parts w in
  let pw' = App (symbol "P" [get_sort w] bool_sort) [w] in
  [refl (neg qxr); refl (neg pw');
   be "nnf-neg" (oeq (neg body) tbody) (if self then [0; 2] else [0; 1]);
   bq "nnf-neg" [integer; real] (oeq (neg (exists_ [integer; real] body)) (forall_ [integer; real] tbody)) [2];
   bq "nnf-pos" [integer] (oeq (forall_ [integer] (neg (exists_ [integer; real] body)))
                               (forall_ [integer] (forall_ [integer; real] tbody))) [3]]

let g3_lhs (w:expr) : expr = forall_ [integer] (neg (exists_ [integer; real] (fst (g3_parts w))))
let g3_rhs (w:expr) : expr = forall_ [integer] (forall_ [integer; real] (snd (g3_parts w)))

let g4_scope_mutants ()
  : Lemma (replays (cert (g3_with (Var 2 integer) false) 4) (g3_lhs (Var 2 integer)) (g3_rhs (Var 2 integer)) /\
           pending (cert (g3_with (Var 3 integer) false) 4) (g3_lhs (Var 3 integer)) (g3_rhs (Var 3 integer)) /\
           pending (cert (g3_with (Var 2 real) false) 4) (g3_lhs (Var 2 real)) (g3_rhs (Var 2 real)) /\
           malformed (cert (g3_with (Var 2 integer) true) 4) (g3_lhs (Var 2 integer)) (g3_rhs (Var 2 integer))) =
  assert_norm (replays (cert (g3_with (Var 2 integer) false) 4) (g3_lhs (Var 2 integer)) (g3_rhs (Var 2 integer)));
  assert_norm (pending (cert (g3_with (Var 3 integer) false) 4) (g3_lhs (Var 3 integer)) (g3_rhs (Var 3 integer)));
  assert_norm (pending (cert (g3_with (Var 2 real) false) 4) (g3_lhs (Var 2 real)) (g3_rhs (Var 2 real)));
  assert_norm (malformed (cert (g3_with (Var 2 integer) true) 4) (g3_lhs (Var 2 integer)) (g3_rhs (Var 2 integer)))

(* ---------------------------------------------------------------------- *)
(* H. Mixed-binder duality mutant with a counter-model                      *)
(* ---------------------------------------------------------------------- *)

(* H1 the wrong-polarity duality under the heterogeneous binders [Int; Real]:
   (not (exists x:Int r:Real. q x r)) ~ (forall x:Int r:Real. q x r), in a
   would-be refutation of the SATISFIABLE inputs (not (exists x r. q x r))
   and (not (q k r0)): the node stays pending, so the document is not
   certified. *)
let rc : expr = const "r0" real
let h1_ex : expr = exists_ [integer; real] qxr
let h1_fa : expr = forall_ [integer; real] qxr
let h1_a : expr = neg h1_ex
let h1_b : expr = neg (App qd [kc; rc])
let h1_entries : list U.binder_entry = [refl qxr; bq "nnf-neg" [integer; real] (oeq h1_a h1_fa) [0]]
let h1_document : P.document =
  doc [h1_a; h1_b]
      [entry U.Asserted h1_a [];
       entry (U.QuantifierIntroduction (cert h1_entries 1)) (oeq h1_a h1_fa) [];
       entry U.ObservationalMP h1_fa [0; 1];
       entry (U.QuantifierInstantiation [kc; rc]) (mk_or [neg h1_fa; App qd [kc; rc]]) [];
       entry U.Asserted h1_b [];
       entry U.UnitResolution R.false_expr [3; 2; 4]]
      5

let h1_mutant_pending ()
  : Lemma (pending (cert h1_entries 1) h1_a h1_fa /\
           RD.check_root_document_epsilon PT.core_schema h1_document == RD.RootPending 1) =
  assert_norm (pending (cert h1_entries 1) h1_a h1_fa);
  assert_norm (RD.check_root_document_epsilon PT.core_schema h1_document == RD.RootPending 1)

let lemma_q_false (u:TR.uninterpreted) (scope:list sort)
                  (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope) (a b:expr)
  : Lemma (requires D.scoped scope (App qd [a; b]))
          (ensures TR.truth PT.core_schema
                     (V.evaluate (S.signature PT.core_schema)
                        (TR.standard u PT.core_schema (RDT.uf_bool u false)) scope rho (App qd [a; b])) == false) =
  assert_norm (TR.classify (S.signature PT.core_schema) qd == TR.Other);
  TR.lemma_eval_free_choice u PT.core_schema (RDT.uf_bool u false) scope rho qd [a; b]

(* The positive counter-model: the standard root model that interprets every
   free Boolean symbol as false (for every u) satisfies both inputs, so a
   replay that accepted the mutant would certify a satisfiable document. *)
let h1_counter_model (u:TR.uninterpreted)
  : Lemma (TR.root_model u PT.core_schema (TR.standard u PT.core_schema (RDT.uf_bool u false)) /\
           RD.root_truths u PT.core_schema (TR.standard u PT.core_schema (RDT.uf_bool u false)) h1_document.P.assertions) =
  let sch = PT.core_schema in
  let i = TR.standard u sch (RDT.uf_bool u false) in
  let sigma = S.signature sch in
  let empty = RD.empty_root u sch in
  TR.lemma_standard_root u sch (RDT.uf_bool u false);
  (* (not (q k r0)) *)
  lemma_q_false u [] empty kc rc;
  lemma_not_value u i [] empty (App qd [kc; rc]);
  (* (not (exists x r. q x r)): no witness at the reversed binder scope [Real; Int] *)
  let none (vs:TR.targuments u sch (L.rev [integer; real]))
    : Lemma (TR.truth sch (V.evaluate sigma i (L.append (L.rev [integer; real]) [])
               (V.extend sigma [] (L.rev [integer; real]) vs empty) qxr) == false) =
    lemma_q_false u (L.append (L.rev [integer; real]) []) (V.extend sigma [] (L.rev [integer; real]) vs empty)
      (Var 1 integer) (Var 0 real) in
  FStar.Classical.forall_intro none;
  TR.lemma_eval_exists i [] empty [integer; real] qxr;
  lemma_not_value u i [] empty h1_ex
