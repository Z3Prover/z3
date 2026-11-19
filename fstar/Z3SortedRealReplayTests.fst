module Z3SortedRealReplayTests

(* Real rewrite leaves in the scoped quant-intro replay (Z3NnfReplay with the
   schema-derived Real gate that Z3SortedProof passes: real_primitive of its
   checked schema), by normalization of the checker itself.

   C1. The captured Pulse.Class.PtsTo q1 certificates (9af capture full-9af,
       /root/fstar-quant-intro-investigation-20261104/exemplars/real,
       certdump.jsonl sha256 be96fb23... for node 114 and 69952588... for
       node 176), entry by entry with the marshalled declaration names, the
       Term binder sort of the capture and the canonical Real operators of
       the leaf heads: node 114 (`>` to `not <=`, `<=` to the renormalized
       `>=` of the difference y + (-1)x, a propositional leaf and an identity leaf) and
       node 176 (binary Real `*` commutation under BoxReal). Each replays
       with the gate and stays pending without it (the previous verdict).
   C2. The leaf shapes of the captured Real cohort at scope [Term; Term]:
       `+` permutation, `(to_real 0)` folded to the Real numeral 0, `<` to
       `not <=`, `>=` and `<=` reorientations.
   C3. Mutants, each refused with the gate (the node stays pending): the
       strict comparison to `not <`, the Int-style strict rounding
       `x < y` to `x <= y - 1`, a wrong renormalization direction, a dropped
       summand, the square x x for the product x y, a counterfeit `>`, a same-spelled
       distinct projection, `(to_real 1)` folded to 0, a nonlinear product
       regrouped by associativity, and to_int / is_int / Real division
       by zero, which have no law here.
   C4. The theorem: a gated replay holds in every Sorted model with the Real
       laws, hence in every root model (Real laws derived from R2 of the same
       model); the flag alone is not a hypothesis. *)

open Z3AstTheory
open Z3ValueTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module L = FStar.List.Tot
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module NR = Z3NnfReplay
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module RL = Z3SortedReal
module RR = Z3SortedRealRoot
module RD = Z3SortedRootDocument
module LIN = Z3SortedRealLinear

let term : sort = BaseSort "sort!2147483829:Term"
let real : sort = TR.real_s
let integer : sort = TR.int_s

let symbol (name:string) (ds:list sort) (r:sort) : func_decl =
  { decl_name = name; domain = ds; range = r; interp = None; int_params = [] }

let eq (a b:expr) : expr = R.mk_eq_expr a b
let neg (a:expr) : expr = R.mk_not_expr a
let forall_ (bs:list sort) (b:expr) : expr = Quantifier Forall_k bs bool_sort b

let be (name:string) (f:expr) (ps:list int) : U.binder_entry =
  { U.binder_name = name; binder_formula = f; binder_premises = ps; binder_sorts = None }
let bq (name:string) (bs:list sort) (f:expr) (ps:list int) : U.binder_entry =
  { U.binder_name = name; binder_formula = f; binder_premises = ps; binder_sorts = Some bs }
let cert (es:list U.binder_entry) (root:int) : U.binder_certificate = { U.binder_entries = es; binder_root = root }

(* Captured declarations (marshalled names). *)
let proj : func_decl = symbol "decl!2147483973:BoxReal_proj_0" [term] real
let box : func_decl = symbol "decl!2147483966:BoxReal" [real] term
let valid : func_decl = symbol "decl!2147483842:Valid" [term] bool_sort
let gt_dot : func_decl = symbol "decl!2147484004:FStar.Real.op_Greater_Dot" [term; term] term
let star_dot : func_decl = symbol "decl!2147484005:FStar.Real.op_Star_Dot" [term; term] term

let t0 : expr = Var 0 term
let t1 : expr = Var 1 term
let p0 : expr = App proj [t0]
let p1 : expr = App proj [t1]
let rnum (n:int) : expr = App (TR.real_numeral n 1) []
let rgt (a b:expr) : expr = App (TR.gt_decl real) [a; b]
let rlt (a b:expr) : expr = App (TR.lt_decl real) [a; b]
let rle (a b:expr) : expr = App (TR.le_decl real) [a; b]
let rge (a b:expr) : expr = App (TR.ge_decl real) [a; b]
let rplus (a b:expr) : expr = App (TR.plus_decl real) [a; b]
let rminus (a b:expr) : expr = App (TR.minus_decl real) [a; b]
let rtimes (a b:expr) : expr = App (TR.times_decl real) [a; b]
let to_real (a:expr) : expr = App TR.to_real_decl [a]

(* The two replay verdicts on one certificate: with the Real gate (what the
   Sorted kernel passes for a Real-primitive schema) and without it. *)
let gated (c:U.binder_certificate) (lhs rhs:expr) : bool =
  NR.replay_with true [] c (U.Equal lhs rhs) = NR.Replayed

let ungated_pending (c:U.binder_certificate) (lhs rhs:expr) : bool =
  NR.replay [] c (U.Equal lhs rhs) = NR.Unreplayed

let gated_pending (c:U.binder_certificate) (lhs rhs:expr) : bool =
  NR.replay_with true [] c (U.Equal lhs rhs) = NR.Unreplayed

(* ---------------------------------------------------------------------- *)
(* C1. Captured certificates                                                *)
(* ---------------------------------------------------------------------- *)

(* Node 114. *)
let n114_gt : expr = rgt p1 p0
let n114_le : expr = rle p1 p0
let n114_ge : expr = rge (rplus p0 (rtimes (rnum (-1)) p1)) (rnum 0)
let n114_valid : expr = App valid [App gt_dot [t1; t0]]
let n114_body_l : expr = eq n114_valid n114_gt
let n114_body_m : expr = eq n114_valid (neg n114_ge)
let n114_body_r : expr = neg (eq n114_ge n114_valid)
let n114_lhs : expr = forall_ [term; term] n114_body_l
let n114_rhs : expr = forall_ [term; term] n114_body_r

let n114_entries (leaf0_rhs leaf1_rhs:expr) : list U.binder_entry = [
  be "rewrite" (eq n114_gt (neg n114_le)) [];               (* 0 *)
  be "rewrite" (eq n114_le leaf1_rhs) [];                    (* 1 *)
  be "monotonicity" (eq (neg n114_le) (neg n114_ge)) [1];    (* 2 *)
  be "trans" (eq n114_gt (neg n114_ge)) [0; 2];              (* 3 *)
  be "monotonicity" (eq n114_body_l n114_body_m) [3];        (* 4 *)
  be "rewrite" (eq n114_body_m n114_body_r) [];              (* 5 *)
  be "trans" (eq n114_body_l n114_body_r) [4; 5];            (* 6 *)
  be "rewrite" (eq n114_body_r n114_body_r) [];              (* 7 *)
  be "trans" (eq n114_body_l n114_body_r) [6; 7];            (* 8 *)
  bq "quant-intro" [term; term] (eq n114_lhs n114_rhs) [8]]  (* 9, the root *)

let n114_cert : U.binder_certificate = cert (n114_entries (neg n114_le) n114_ge) 9

let c1_n114 ()
  : Lemma (gated n114_cert n114_lhs n114_rhs /\ ungated_pending n114_cert n114_lhs n114_rhs) =
  assert_norm (gated n114_cert n114_lhs n114_rhs);
  assert_norm (ungated_pending n114_cert n114_lhs n114_rhs)

(* Node 176. *)
let n176_l : expr = rtimes p1 p0
let n176_r : expr = rtimes p0 p1
let n176_body_l : expr = eq (App star_dot [t1; t0]) (App box [n176_l])
let n176_body_r : expr = eq (App star_dot [t1; t0]) (App box [n176_r])
let n176_lhs : expr = forall_ [term; term] n176_body_l
let n176_rhs : expr = forall_ [term; term] n176_body_r

let n176_cert_of (leaf_rhs:expr) : U.binder_certificate =
  cert [be "rewrite" (eq n176_l leaf_rhs) [];                                  (* 0 *)
        be "monotonicity" (eq (App box [n176_l]) (App box [leaf_rhs])) [0];    (* 1 *)
        be "monotonicity" (eq n176_body_l (eq (App star_dot [t1; t0]) (App box [leaf_rhs]))) [1]; (* 2 *)
        bq "quant-intro" [term; term]
          (eq n176_lhs (forall_ [term; term] (eq (App star_dot [t1; t0]) (App box [leaf_rhs])))) [2]] (* 3 *)
    3

let c1_n176 ()
  : Lemma (gated (n176_cert_of n176_r) n176_lhs n176_rhs /\ ungated_pending (n176_cert_of n176_r) n176_lhs n176_rhs) =
  assert_norm (gated (n176_cert_of n176_r) n176_lhs n176_rhs);
  assert_norm (ungated_pending (n176_cert_of n176_r) n176_lhs n176_rhs)

(* ---------------------------------------------------------------------- *)
(* C2. Leaf shapes of the captured cohort, C3. mutants                      *)
(* ---------------------------------------------------------------------- *)

let gate (l r:expr) : bool = NR.real_rewrite_ok true l r
let old (l r:expr) : bool = NR.rewrite_ok l r

let c2_shapes ()
  : Lemma (gate (rplus p1 p0) (rplus p0 p1) /\ not (old (rplus p1 p0) (rplus p0 p1)) /\
           gate (to_real (App (TR.int_numeral 0) [])) (rnum 0) /\
           gate (rlt p1 p0) (neg (rle p0 p1)) /\
           gate (rge p1 p0) (rle (rplus p0 (rtimes (rnum (-1)) p1)) (rnum 0)) /\
           gate (rle p1 p0) (rge (rplus p0 (rtimes (rnum (-1)) p1)) (rnum 0)) /\
           gate (rgt p1 p0) (neg (rle p1 p0)) /\
           gate (rtimes p1 p0) (rtimes p0 p1) /\
           not (NR.real_rewrite_ok false (rtimes p1 p0) (rtimes p0 p1))) =
  assert_norm (gate (rplus p1 p0) (rplus p0 p1));
  assert_norm (not (old (rplus p1 p0) (rplus p0 p1)));
  assert_norm (gate (to_real (App (TR.int_numeral 0) [])) (rnum 0));
  assert_norm (gate (rlt p1 p0) (neg (rle p0 p1)));
  assert_norm (gate (rge p1 p0) (rle (rplus p0 (rtimes (rnum (-1)) p1)) (rnum 0)));
  assert_norm (gate (rle p1 p0) (rge (rplus p0 (rtimes (rnum (-1)) p1)) (rnum 0)));
  assert_norm (gate (rgt p1 p0) (neg (rle p1 p0)));
  assert_norm (gate (rtimes p1 p0) (rtimes p0 p1));
  assert_norm (not (NR.real_rewrite_ok false (rtimes p1 p0) (rtimes p0 p1)))

let twin_proj : func_decl = { proj with int_params = [7] }
let fake_gt : func_decl = { TR.gt_decl real with interp = None }

let c3_mutants ()
  : Lemma (not (gate (rgt p1 p0) (neg (rlt p1 p0))) /\
           not (gate (rlt p1 p0) (rle p1 (rminus p0 (rnum 1)))) /\
           not (gate (rle p1 p0) (rge (rplus p1 (rtimes (rnum (-1)) p0)) (rnum 0))) /\
           not (gate (rplus p1 p0) p0) /\
           not (gate (rtimes p1 p0) (rtimes p1 p1)) /\
           not (gate (App fake_gt [p1; p0]) (neg (rle p1 p0))) /\
           not (gate (rgt p1 p0) (neg (rle p1 (App twin_proj [t0])))) /\
           not (gate (to_real (App (TR.int_numeral 1) [])) (rnum 0)) /\
           not (gate (rtimes (rtimes p1 p0) p1) (rtimes (rtimes p1 p1) p0))) =
  assert_norm (not (gate (rgt p1 p0) (neg (rlt p1 p0))));
  assert_norm (not (gate (rlt p1 p0) (rle p1 (rminus p0 (rnum 1)))));
  assert_norm (not (gate (rle p1 p0) (rge (rplus p1 (rtimes (rnum (-1)) p0)) (rnum 0))));
  assert_norm (not (gate (rplus p1 p0) p0));
  assert_norm (not (gate (rtimes p1 p0) (rtimes p1 p1)));
  assert_norm (not (gate (App fake_gt [p1; p0]) (neg (rle p1 p0))));
  assert_norm (not (gate (rgt p1 p0) (neg (rle p1 (App twin_proj [t0])))));
  assert_norm (not (gate (to_real (App (TR.int_numeral 1) [])) (rnum 0)));
  assert_norm (not (gate (rtimes (rtimes p1 p0) p1) (rtimes (rtimes p1 p1) p0)))

(* Unsupported operators: to_int and is_int have no interpretation tag in the
   checker's operator vocabulary (Z3ValueTheory), so they are opaque symbols
   with no law, and Real division by zero has none either; leaves that need
   such a law stay pending even under the gate. *)
let to_int_decl : func_decl = symbol "to_int" [real] integer
let is_int_decl : func_decl = symbol "is_int" [real] bool_sort

let c3_unsupported ()
  : Lemma (not (gate (to_real (App to_int_decl [p1])) p1) /\
           not (gate (App is_int_decl [rnum 0]) R.true_expr) /\
           not (gate (App TR.divide_decl [p1; rnum 0]) (rnum 0))) =
  assert_norm (not (gate (to_real (App to_int_decl [p1])) p1));
  assert_norm (not (gate (App is_int_decl [rnum 0]) R.true_expr));
  assert_norm (not (gate (App TR.divide_decl [p1; rnum 0]) (rnum 0)))

(* The captured certificates with a mutated leaf stay pending under the gate. *)
let c3_certificate_mutants ()
  : Lemma (gated_pending (cert (n114_entries (neg n114_le)
                                  (rge (rplus p1 (rtimes (rnum (-1)) p0)) (rnum 0))) 9) n114_lhs n114_rhs /\
           gated_pending (n176_cert_of (rtimes p1 p1)) n176_lhs
             (forall_ [term; term] (eq (App star_dot [t1; t0]) (App box [rtimes p1 p1])))) =
  assert_norm (gated_pending (cert (n114_entries (neg n114_le)
                                      (rge (rplus p1 (rtimes (rnum (-1)) p0)) (rnum 0))) 9) n114_lhs n114_rhs);
  assert_norm (gated_pending (n176_cert_of (rtimes p1 p1)) n176_lhs
                 (forall_ [term; term] (eq (App star_dot [t1; t0]) (App box [rtimes p1 p1]))))

(* ---------------------------------------------------------------------- *)
(* C4. The theorem in every Sorted model with the Real laws, every root     *)
(* ---------------------------------------------------------------------- *)

let c4_valid (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
             (eq_model:T.scalar_model base) (other:V.interpretation base (S.signature s))
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\ RL.real_model s bc eq_model other)
          (ensures NR.holds_at s bc eq_model other [] (T.empty_environment (S.signature s)) (U.Equal n114_lhs n114_rhs) /\
                   NR.holds_at s bc eq_model other [] (T.empty_environment (S.signature s)) (U.Equal n176_lhs n176_rhs)) =
  c1_n114 ();
  c1_n176 ();
  NR.lemma_replay_with s bc eq_model other true [] n114_cert (U.Equal n114_lhs n114_rhs);
  NR.lemma_replay_with s bc eq_model other true [] (n176_cert_of n176_r) (U.Equal n176_lhs n176_rhs)

let c4_root (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
  : Lemma (requires TR.root_model u sch i /\ RL.real_primitive sch)
          (ensures NR.holds_at sch (TR.booleans u) (SR.root_scalars u) i [] (T.empty_environment (S.signature sch))
                     (U.Equal n114_lhs n114_rhs) /\
                   NR.holds_at sch (TR.booleans u) (SR.root_scalars u) i [] (T.empty_environment (S.signature sch))
                     (U.Equal n176_lhs n176_rhs)) =
  RD.lemma_forall_model u sch i;
  RD.lemma_exists_model u sch i;
  RR.lemma_root_real_model u sch i;
  c4_valid sch (TR.booleans u) (SR.root_scalars u) i
