module Z3QuantIntroReplayTests

(* Tests of the scoped quant-intro certificate replay (Z3NnfReplay with a
   quant-intro root) on the Sorted route.

   A. Positive certificates, each the ACTUAL replay verdict (normalized):
      A1 the Tactics.BreakVC shape: implication-to-or under two nested Term
         binders (rewrite / quant-intro / monotonicity / trans / quant-intro);
      A2 the Int normalization shape (PulseCore.IndirectionTheorySep-2,
         Pulse.Lib.Swap.Spec-7, FStar.Math.Fermat-2): `>` to `not <=`, the
         difference form `x + (-1)*y <= 0`, implication-to-or, under two
         nested Int binders;
      A3 an exists root, a shared (DAG) closed leaf read at two scopes, and a
         two-sorted binder list in de Bruijn order.
   B. Mutants (Unreplayed = the node stays pending, Malformed = a rejected
      proof entry): wrong leaf sign, wrong Int target, a de Bruijn shift /
      capture, swapped binder sorts, a leaf reused at an incompatible scope,
      a missing and a swapped congruence premise, a wrong quantifier kind, a
      wrong body parent, a wrong root target, a forward / self / cyclic
      premise id, a rewrite leaf with a premise or binder sorts, rewrite
      and quant-intro steps under an NNF root (unchanged NNF calculus), and
      a VALID closed root over corrupted used internal entries (Bool and
      Int).
   C. The node and the document: the old disjuncts of check_node_cached
      fail on the A2 node and the replay checks it (the small A1 node is
      within both); refutations using them are RootCertified (the Root gate
      reads and covers the consumed quant-intro certificate) and falsified
      in EVERY root model; hence the A1/A2 equations hold in every standard
      root model (populated positive instances of NR.lemma_replay through
      the document theorem). Mutant documents stay pending or are rejected
      (malformed), and the coverage gate reads the consumed certificate.
   Counter-models for the false mutants (the claimed root equation, or the
   corrupted open leaf at a concrete environment of its assigned scope, is
   FALSE in an explicitly constructed standard root model) are in
   Z3QuantIntroCounterModelTests.

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
module SR = Z3SortedRoot
module SP = Z3SortedProof
module DT = Z3SortedDatatype
module P = Z3ProofDocument
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module NR = Z3NnfReplay
module RD = Z3SortedRootDocument
module PT = Z3SortedProofTests
module BR = Z3BooleanRewrite
module B = Z3BoundedBoolEquiv
module Q = Z3SortedQuantifier

(* ---------------------------------------------------------------------- *)
(* Shapes                                                                   *)
(* ---------------------------------------------------------------------- *)

let integer : sort = TR.int_s
let term : sort = BaseSort "Term"

let symbol (name:string) (ds:list sort) (r:sort) : func_decl =
  { decl_name = name; domain = ds; range = r; interp = None; int_params = [] }

let mk_and (args:list expr) : expr = App (BR.connective_decl BR.Conjunction args) args
let mk_or (args:list expr) : expr = App (BR.connective_decl BR.Disjunction args) args
let neg (a:expr) : expr = R.mk_not_expr a
let implies (a b:expr) : expr = App SP.implies_decl [a; b]
let eq (a b:expr) : expr = R.mk_eq_expr a b
let forall_ (bs:list sort) (b:expr) : expr = Quantifier Forall_k bs bool_sort b
let exists_ (bs:list sort) (b:expr) : expr = Quantifier Exists_k bs bool_sort b

let num (n:int) : expr = App (TR.int_numeral n) []
let plus (a b:expr) : expr = App (TR.plus_decl integer) [a; b]
let times (a b:expr) : expr = App (TR.times_decl integer) [a; b]
let le (a b:expr) : expr = App (TR.le_decl integer) [a; b]
let gt (a b:expr) : expr = App (TR.gt_decl integer) [a; b]

let be (name:string) (f:expr) (ps:list int) : U.binder_entry =
  { U.binder_name = name; binder_formula = f; binder_premises = ps; binder_sorts = None }
let bq (name:string) (bs:list sort) (f:expr) (ps:list int) : U.binder_entry =
  { U.binder_name = name; binder_formula = f; binder_premises = ps; binder_sorts = Some bs }
let cert (es:list U.binder_entry) (root:int) : U.binder_certificate = { U.binder_entries = es; binder_root = root }

let replays (c:U.binder_certificate) (lhs rhs:expr) : bool =
  NR.replay [] c (U.Equal lhs rhs) = NR.Replayed

let pending (c:U.binder_certificate) (lhs rhs:expr) : bool =
  NR.replay [] c (U.Equal lhs rhs) = NR.Unreplayed

let malformed (c:U.binder_certificate) (lhs rhs:expr) : bool =
  NR.replay [] c (U.Equal lhs rhs) = NR.Malformed

(* ---------------------------------------------------------------------- *)
(* A. Positive certificates                                                 *)
(* ---------------------------------------------------------------------- *)

(* A1, the BreakVC shape. Outer binder x, inner binder y: at the inner body
   scope [Term; Term] Var 1 is x and Var 0 is y; at the outer body scope
   [Term] Var 0 is x.
     forall x. (P x => forall y. (Q x y => R y))
   = forall x. (or (not (P x)) (forall y. (or (not (Q x y)) (R y)))) *)
let pd : func_decl = symbol "P" [term] bool_sort
let qd : func_decl = symbol "Q" [term; term] bool_sort
let rd : func_decl = symbol "R" [term] bool_sort
let p_ (x:expr) : expr = App pd [x]
let q_ (x y:expr) : expr = App qd [x; y]
let r_ (x:expr) : expr = App rd [x]
let t0 : expr = Var 0 term
let t1 : expr = Var 1 term

let in_l : expr = implies (q_ t1 t0) (r_ t0)
let in_r : expr = mk_or [neg (q_ t1 t0); r_ t0]
let all_l : expr = forall_ [term] in_l
let all_r : expr = forall_ [term] in_r
let out_l : expr = implies (p_ t0) all_l
let out_m : expr = implies (p_ t0) all_r
let out_r : expr = mk_or [neg (p_ t0); all_r]
let a1_lhs : expr = forall_ [term] out_l
let a1_rhs : expr = forall_ [term] out_r

let a1_entries : list U.binder_entry = [
  be "rewrite" (eq in_l in_r) [];                 (* 0, scope [Term; Term] *)
  bq "quant-intro" [term] (eq all_l all_r) [0];   (* 1, scope [Term] *)
  be "monotonicity" (eq out_l out_m) [1];         (* 2, scope [Term] *)
  be "rewrite" (eq out_m out_r) [];               (* 3, scope [Term] *)
  be "trans" (eq out_l out_r) [2; 3];             (* 4, scope [Term] *)
  bq "quant-intro" [term] (eq a1_lhs a1_rhs) [4]] (* 5, the root, scope [] *)
let a1_cert : U.binder_certificate = cert a1_entries 5

let a1_breakvc_shape () : Lemma (replays a1_cert a1_lhs a1_rhs) =
  assert_norm (replays a1_cert a1_lhs a1_rhs)

(* A2, the Int shape. Outer binder x, inner binder y (both Int): at the
   inner body scope Var 1 is x and Var 0 is y.
     forall x. forall y. ((x > y) => pi x)
   = forall x. forall y. (or (x + (-1)*y <= 0) (pi x)) *)
let pid : func_decl = symbol "pi" [integer] bool_sort
let i0 : expr = Var 0 integer
let i1 : expr = Var 1 integer
let pix : expr = App pid [i1]
let gxy : expr = gt i1 i0
let lxy : expr = le i1 i0
let dxy : expr = le (plus i1 (times (num (-1)) i0)) (num 0)
let b2_l : expr = implies gxy pix
let b2_m : expr = implies (neg dxy) pix
let b2_r : expr = mk_or [dxy; pix]
let a2_inner_l : expr = forall_ [integer] b2_l
let a2_inner_r : expr = forall_ [integer] b2_r
let a2_lhs : expr = forall_ [integer] a2_inner_l
let a2_rhs : expr = forall_ [integer] a2_inner_r

let a2_entries : list U.binder_entry = [
  be "rewrite" (eq gxy (neg lxy)) [];                     (* 0, Int: > to not <= *)
  be "rewrite" (eq lxy dxy) [];                           (* 1, Int: difference form *)
  be "monotonicity" (eq (neg lxy) (neg dxy)) [1];         (* 2 *)
  be "trans" (eq gxy (neg dxy)) [0; 2];                   (* 3 *)
  be "monotonicity" (eq b2_l b2_m) [3];                   (* 4 *)
  be "rewrite" (eq b2_m b2_r) [];                         (* 5, propositional *)
  be "trans" (eq b2_l b2_r) [4; 5];                       (* 6, scope [Int; Int] *)
  bq "quant-intro" [integer] (eq a2_inner_l a2_inner_r) [6]; (* 7, scope [Int] *)
  bq "quant-intro" [integer] (eq a2_lhs a2_rhs) [7]]     (* 8, the root *)
let a2_cert : U.binder_certificate = cert a2_entries 8

let a2_int_shape () : Lemma (replays a2_cert a2_lhs a2_rhs) =
  assert_norm (replays a2_cert a2_lhs a2_rhs)

(* The two Int leaves are accepted by the existing typed Int equivalence,
   the implication leaf by the propositional check only. *)
let a2_leaf_classes ()
  : Lemma (Z3SortedArithmetic.equivalent gxy (neg lxy) /\ Z3SortedArithmetic.equivalent lxy dxy /\
           not (Z3SortedArithmetic.equivalent b2_m b2_r) /\ NR.rewrite_ok b2_m b2_r) =
  assert_norm (Z3SortedArithmetic.equivalent gxy (neg lxy));
  assert_norm (Z3SortedArithmetic.equivalent lxy dxy);
  assert_norm (not (Z3SortedArithmetic.equivalent b2_m b2_r));
  assert_norm (NR.rewrite_ok b2_m b2_r)

(* A3 an exists root over a two-sorted binder list [Int; Term] (body scope
   [Term; Int]: Var 0 is the Term, Var 1 the Int), with a closed leaf that
   is used both at [Term; Int] and, through a second quant-intro, at [Int]:
   exists x:Int t:Term. (c => (pi x and P t)) = exists x t. (or (not c) (and (pi x) (P t))) *)
let cc : expr = App (symbol "c" [] bool_sort) []
let a3_shared_l : expr = implies cc cc
let a3_shared_r : expr = mk_or [neg cc; cc]
let a3_body_l : expr = mk_and [a3_shared_l; App pid [i1]; p_ t0]
let a3_body_r : expr = mk_and [a3_shared_r; App pid [i1]; p_ t0]
let a3_lhs : expr = exists_ [integer; term] a3_body_l
let a3_rhs : expr = exists_ [integer; term] a3_body_r
let a3_side_l : expr = forall_ [integer] (mk_and [a3_shared_l; App pid [i0]])
let a3_side_r : expr = forall_ [integer] (mk_and [a3_shared_r; App pid [i0]])
let a3_entries : list U.binder_entry = [
  be "rewrite" (eq a3_shared_l a3_shared_r) [];                      (* 0, at [Term; Int] and [Int] *)
  be "monotonicity" (eq a3_body_l a3_body_r) [0];                    (* 1 *)
  bq "quant-intro" [integer; term] (eq a3_lhs a3_rhs) [1];           (* 2 *)
  be "monotonicity" (eq (mk_and [a3_shared_l; App pid [i0]]) (mk_and [a3_shared_r; App pid [i0]])) [0]; (* 3 *)
  bq "quant-intro" [integer] (eq a3_side_l a3_side_r) [3];          (* 4 *)
  be "monotonicity" (eq (mk_and [a3_lhs; a3_side_l]) (mk_and [a3_rhs; a3_side_r])) [2; 4]; (* 5 *)
  bq "quant-intro" [term] (eq (forall_ [term] (mk_and [a3_lhs; a3_side_l]))
                              (forall_ [term] (mk_and [a3_rhs; a3_side_r]))) [5]]           (* 6 *)

let a3_exists_root () : Lemma (replays (cert a3_entries 2) a3_lhs a3_rhs) =
  assert_norm (replays (cert a3_entries 2) a3_lhs a3_rhs)

let a3_shared_leaf ()
  : Lemma (replays (cert a3_entries 6) (forall_ [term] (mk_and [a3_lhs; a3_side_l]))
                                       (forall_ [term] (mk_and [a3_rhs; a3_side_r]))) =
  assert_norm (replays (cert a3_entries 6) (forall_ [term] (mk_and [a3_lhs; a3_side_l]))
                                           (forall_ [term] (mk_and [a3_rhs; a3_side_r])))

(* ---------------------------------------------------------------------- *)
(* B. Mutants: the actual replay verdicts                                   *)
(* ---------------------------------------------------------------------- *)

(* B1 wrong leaf sign: the inner leaf (Q x y => R y) = (or (Q x y) (R y)),
   carried consistently up to the root (claim false: counter-model D1 of
   Z3QuantIntroCounterModelTests). *)
let w_in_r : expr = mk_or [q_ t1 t0; r_ t0]
let w_all_r : expr = forall_ [term] w_in_r
let w_out_m : expr = implies (p_ t0) w_all_r
let w_out_r : expr = mk_or [neg (p_ t0); w_all_r]
let b1_rhs : expr = forall_ [term] w_out_r
let b1_entries : list U.binder_entry = [
  be "rewrite" (eq in_l w_in_r) [];
  bq "quant-intro" [term] (eq all_l w_all_r) [0];
  be "monotonicity" (eq out_l w_out_m) [1];
  be "rewrite" (eq w_out_m w_out_r) [];
  be "trans" (eq out_l w_out_r) [2; 3];
  bq "quant-intro" [term] (eq a1_lhs b1_rhs) [4]]
let b1_wrong_leaf_sign () : Lemma (pending (cert b1_entries 5) a1_lhs b1_rhs) =
  assert_norm (pending (cert b1_entries 5) a1_lhs b1_rhs)

(* B2 wrong Int target: (x > y) = (not (y <= x)) (operands of <= swapped),
   carried up. The leaf is false at x = 1, y = 0 (counter-model D6); the
   root claim itself happens to be valid over the unbounded Int carrier. *)
let lyx : expr = le i0 i1
let dyx : expr = le (plus i0 (times (num (-1)) i1)) (num 0)
let b2w_m : expr = implies (neg dyx) pix
let b2w_r : expr = mk_or [dyx; pix]
let b2_rhs : expr = forall_ [integer] (forall_ [integer] b2w_r)
let b2_entries : list U.binder_entry = [
  be "rewrite" (eq gxy (neg lyx)) [];
  be "rewrite" (eq lyx dyx) [];
  be "monotonicity" (eq (neg lyx) (neg dyx)) [1];
  be "trans" (eq gxy (neg dyx)) [0; 2];
  be "monotonicity" (eq b2_l b2w_m) [3];
  be "rewrite" (eq b2w_m b2w_r) [];
  be "trans" (eq b2_l b2w_r) [4; 5];
  bq "quant-intro" [integer] (eq a2_inner_l (forall_ [integer] b2w_r)) [6];
  bq "quant-intro" [integer] (eq a2_lhs b2_rhs) [7]]
let b2_wrong_int_target () : Lemma (pending (cert b2_entries 8) a2_lhs b2_rhs) =
  assert_norm (pending (cert b2_entries 8) a2_lhs b2_rhs)

(* B3 a de Bruijn shift: the difference leaf reads Var 0 for x (the inner
   binder twice), so the claimed rhs is about y - y (the leaf is false at
   x = 1, y = 0: counter-model D7); and a capture: the inner leaf of A1 with
   Q's arguments read one binder off (Q y x). *)
let dyy : expr = le (plus i0 (times (num (-1)) i0)) (num 0)
let b3_rhs : expr = forall_ [integer] (forall_ [integer] (mk_or [dyy; pix]))
let b3_entries : list U.binder_entry = [
  be "rewrite" (eq gxy (neg lxy)) [];
  be "rewrite" (eq lxy dyy) [];
  be "monotonicity" (eq (neg lxy) (neg dyy)) [1];
  be "trans" (eq gxy (neg dyy)) [0; 2];
  be "monotonicity" (eq b2_l (implies (neg dyy) pix)) [3];
  be "rewrite" (eq (implies (neg dyy) pix) (mk_or [dyy; pix])) [];
  be "trans" (eq b2_l (mk_or [dyy; pix])) [4; 5];
  bq "quant-intro" [integer] (eq a2_inner_l (forall_ [integer] (mk_or [dyy; pix]))) [6];
  bq "quant-intro" [integer] (eq a2_lhs b3_rhs) [7]]
let b3_shift () : Lemma (pending (cert b3_entries 8) a2_lhs b3_rhs) =
  assert_norm (pending (cert b3_entries 8) a2_lhs b3_rhs)

let c_in_r : expr = mk_or [neg (q_ t0 t1); r_ t0]
let c_all_r : expr = forall_ [term] c_in_r
let b3c_rhs : expr = forall_ [term] (mk_or [neg (p_ t0); c_all_r])
let b3_capture ()
  : Lemma (pending (cert [be "rewrite" (eq in_l c_in_r) [];
                          bq "quant-intro" [term] (eq all_l c_all_r) [0];
                          be "monotonicity" (eq out_l (implies (p_ t0) c_all_r)) [1];
                          be "rewrite" (eq (implies (p_ t0) c_all_r) (mk_or [neg (p_ t0); c_all_r])) [];
                          be "trans" (eq out_l (mk_or [neg (p_ t0); c_all_r])) [2; 3];
                          bq "quant-intro" [term] (eq a1_lhs b3c_rhs) [4]] 5) a1_lhs b3c_rhs) =
  assert_norm (pending (cert [be "rewrite" (eq in_l c_in_r) [];
                              bq "quant-intro" [term] (eq all_l c_all_r) [0];
                              be "monotonicity" (eq out_l (implies (p_ t0) c_all_r)) [1];
                              be "rewrite" (eq (implies (p_ t0) c_all_r) (mk_or [neg (p_ t0); c_all_r])) [];
                              be "trans" (eq out_l (mk_or [neg (p_ t0); c_all_r])) [2; 3];
                              bq "quant-intro" [term] (eq a1_lhs b3c_rhs) [4]] 5) a1_lhs b3c_rhs)

(* B4 swapped binder sorts: the A3 root declares [Term; Int] for quantifiers
   over [Int; Term]; and both quantifiers over [Term; Int] with the body
   still typed for [Int; Term] (its indices then capture the wrong binder). *)
let b4_swapped_sorts ()
  : Lemma (pending (cert [L.index a3_entries 0; L.index a3_entries 1;
                          bq "quant-intro" [term; integer] (eq a3_lhs a3_rhs) [1]] 2) a3_lhs a3_rhs /\
           pending (cert [L.index a3_entries 0; L.index a3_entries 1;
                          bq "quant-intro" [term; integer]
                            (eq (exists_ [term; integer] a3_body_l) (exists_ [term; integer] a3_body_r)) [1]] 2)
                   (exists_ [term; integer] a3_body_l) (exists_ [term; integer] a3_body_r)) =
  assert_norm (pending (cert [L.index a3_entries 0; L.index a3_entries 1;
                              bq "quant-intro" [term; integer] (eq a3_lhs a3_rhs) [1]] 2) a3_lhs a3_rhs);
  assert_norm (pending (cert [L.index a3_entries 0; L.index a3_entries 1;
                              bq "quant-intro" [term; integer]
                                (eq (exists_ [term; integer] a3_body_l) (exists_ [term; integer] a3_body_r)) [1]] 2)
                       (exists_ [term; integer] a3_body_l) (exists_ [term; integer] a3_body_r))

(* B6 a missing congruence premise: monotonicity changes the inner
   quantifier to a NON-equivalent one with no premise (claim false,
   counter-model D3). *)
let m_all_r : expr = forall_ [term] (mk_and [q_ t1 t0; r_ t0])
let b6_rhs : expr = forall_ [term] (implies (p_ t0) m_all_r)
let b6_missing_premise ()
  : Lemma (pending (cert [be "monotonicity" (eq out_l (implies (p_ t0) m_all_r)) [];
                          bq "quant-intro" [term] (eq a1_lhs b6_rhs) [0]] 1) a1_lhs b6_rhs /\
           pending (cert [be "rewrite" (eq in_l in_r) [];
                          bq "quant-intro" [term] (eq all_l all_r) [0];
                          be "monotonicity" (eq out_l out_m) [];
                          be "rewrite" (eq out_m out_r) [];
                          be "trans" (eq out_l out_r) [2; 3];
                          bq "quant-intro" [term] (eq a1_lhs a1_rhs) [4]] 5) a1_lhs a1_rhs) =
  assert_norm (pending (cert [be "monotonicity" (eq out_l (implies (p_ t0) m_all_r)) [];
                              bq "quant-intro" [term] (eq a1_lhs b6_rhs) [0]] 1) a1_lhs b6_rhs);
  assert_norm (pending (cert [be "rewrite" (eq in_l in_r) [];
                              bq "quant-intro" [term] (eq all_l all_r) [0];
                              be "monotonicity" (eq out_l out_m) [];
                              be "rewrite" (eq out_m out_r) [];
                              be "trans" (eq out_l out_r) [2; 3];
                              bq "quant-intro" [term] (eq a1_lhs a1_rhs) [4]] 5) a1_lhs a1_rhs)

(* B5 a leaf reused at an incompatible scope: under an outer Term binder,
   the A1 inner leaf (typed at [Term; Term] and, one binder deeper, at
   [Term; Term; Term]) is also given as the body premise of a quant-intro
   over ONE Int binder, where Var 0 is the Int. The claim is true and well
   scoped (the control with its own leaf replays); the reuse is refused by
   the scope guard and by the quantifier step. *)
let zp : expr = App pid [i0]
let zl : expr = forall_ [integer] (implies zp zp)
let zr : expr = forall_ [integer] (mk_or [neg zp; zp])
let b5_lhs : expr = forall_ [term] (mk_and [a1_lhs; zl])
let b5_rhs : expr = forall_ [term] (mk_and [a1_rhs; zr])
let b5_reuse : list U.binder_entry =
  L.append a1_entries
    [bq "quant-intro" [integer] (eq zl zr) [0];
     be "monotonicity" (eq (mk_and [a1_lhs; zl]) (mk_and [a1_rhs; zr])) [5; 6];
     bq "quant-intro" [term] (eq b5_lhs b5_rhs) [7]]
let b5_control : list U.binder_entry =
  L.append a1_entries
    [be "rewrite" (eq (implies zp zp) (mk_or [neg zp; zp])) [];
     bq "quant-intro" [integer] (eq zl zr) [6];
     be "monotonicity" (eq (mk_and [a1_lhs; zl]) (mk_and [a1_rhs; zr])) [5; 7];
     bq "quant-intro" [term] (eq b5_lhs b5_rhs) [8]]
let b5_incompatible_reuse ()
  : Lemma (pending (cert b5_reuse 8) b5_lhs b5_rhs /\ replays (cert b5_control 9) b5_lhs b5_rhs) =
  assert_norm (pending (cert b5_reuse 8) b5_lhs b5_rhs);
  assert_norm (replays (cert b5_control 9) b5_lhs b5_rhs)

(* B7 swapped congruence premises: (a => b) = (b' => a') from premises
   [a = a', b = b'] (claim false, counter-model D4), and the correctly targeted
   congruence with its premises in the wrong order. *)
let pc : expr = App (symbol "p" [] bool_sort) []
let qc : expr = App (symbol "q" [] bool_sort) []
let b7_lhs : expr = forall_ [term] (implies (neg (neg pc)) (mk_or [qc; qc]))
let b7_rhs : expr = forall_ [term] (implies qc pc)
let b7_swapped_premises ()
  : Lemma (pending (cert [be "rewrite" (eq (neg (neg pc)) pc) [];
                          be "rewrite" (eq (mk_or [qc; qc]) qc) [];
                          be "monotonicity" (eq (implies (neg (neg pc)) (mk_or [qc; qc])) (implies qc pc)) [0; 1];
                          bq "quant-intro" [term] (eq b7_lhs b7_rhs) [2]] 3) b7_lhs b7_rhs /\
           pending (cert [be "rewrite" (eq (neg (neg pc)) pc) [];
                          be "rewrite" (eq (mk_or [qc; qc]) qc) [];
                          be "monotonicity" (eq (implies (neg (neg pc)) (mk_or [qc; qc])) (implies pc qc)) [1; 0];
                          bq "quant-intro" [term] (eq b7_lhs (forall_ [term] (implies pc qc))) [2]] 3)
                   b7_lhs (forall_ [term] (implies pc qc))) =
  assert_norm (pending (cert [be "rewrite" (eq (neg (neg pc)) pc) [];
                              be "rewrite" (eq (mk_or [qc; qc]) qc) [];
                              be "monotonicity" (eq (implies (neg (neg pc)) (mk_or [qc; qc])) (implies qc pc)) [0; 1];
                              bq "quant-intro" [term] (eq b7_lhs b7_rhs) [2]] 3) b7_lhs b7_rhs);
  assert_norm (pending (cert [be "rewrite" (eq (neg (neg pc)) pc) [];
                              be "rewrite" (eq (mk_or [qc; qc]) qc) [];
                              be "monotonicity" (eq (implies (neg (neg pc)) (mk_or [qc; qc])) (implies pc qc)) [1; 0];
                              bq "quant-intro" [term] (eq b7_lhs (forall_ [term] (implies pc qc))) [2]] 3)
                       b7_lhs (forall_ [term] (implies pc qc)))

(* The correctly ordered certificate of the same root replays. *)
let b7_control ()
  : Lemma (replays (cert [be "rewrite" (eq (neg (neg pc)) pc) [];
                          be "rewrite" (eq (mk_or [qc; qc]) qc) [];
                          be "monotonicity" (eq (implies (neg (neg pc)) (mk_or [qc; qc])) (implies pc qc)) [0; 1];
                          bq "quant-intro" [term] (eq b7_lhs (forall_ [term] (implies pc qc))) [2]] 3)
                   b7_lhs (forall_ [term] (implies pc qc))) =
  assert_norm (replays (cert [be "rewrite" (eq (neg (neg pc)) pc) [];
                              be "rewrite" (eq (mk_or [qc; qc]) qc) [];
                              be "monotonicity" (eq (implies (neg (neg pc)) (mk_or [qc; qc])) (implies pc qc)) [0; 1];
                              bq "quant-intro" [term] (eq b7_lhs (forall_ [term] (implies pc qc))) [2]] 3)
                       b7_lhs (forall_ [term] (implies pc qc)))

(* B8 a quantifier kind change (forall x. x > 0) = (exists x. x > 0) over a
   reflexive body (claim false over Int: x = 0 and x = 1), a wrong body parent (the quant-intro's
   premise is the A1 outer step, not its body equation), and a wrong root
   target (the node conclusion differs from the root entry). *)
let gx0 : expr = gt i0 (num 0)
let b8_kind ()
  : Lemma (pending (cert [be "refl" (eq gx0 gx0) [];
                          bq "quant-intro" [integer] (eq (forall_ [integer] gx0) (exists_ [integer] gx0)) [0]] 1)
                   (forall_ [integer] gx0) (exists_ [integer] gx0)) =
  assert_norm (pending (cert [be "refl" (eq gx0 gx0) [];
                              bq "quant-intro" [integer] (eq (forall_ [integer] gx0) (exists_ [integer] gx0)) [0]] 1)
                       (forall_ [integer] gx0) (exists_ [integer] gx0))

let b8_wrong_parent_and_target ()
  : Lemma (pending (cert (L.append (L.init a1_entries) [bq "quant-intro" [term] (eq a1_lhs a1_rhs) [2]]) 5) a1_lhs a1_rhs /\
           pending a1_cert a1_lhs a1_lhs /\
           NR.replay [] a1_cert (U.Equal a1_rhs a1_lhs) == NR.Unreplayed) =
  assert_norm (pending (cert (L.append (L.init a1_entries) [bq "quant-intro" [term] (eq a1_lhs a1_rhs) [2]]) 5) a1_lhs a1_rhs);
  assert_norm (pending a1_cert a1_lhs a1_lhs);
  assert_norm (NR.replay [] a1_cert (U.Equal a1_rhs a1_lhs) == NR.Unreplayed)

(* B9 non-earlier premise ids: forward, self and a two-entry cycle make the
   certificate malformed (a rejected proof entry, C2). *)
let b9_malformed ()
  : Lemma (malformed (cert [be "rewrite" (eq in_l in_r) [1]; bq "quant-intro" [term] (eq all_l all_r) [0]] 1) all_l all_r /\
           malformed (cert [be "rewrite" (eq in_l in_r) []; bq "quant-intro" [term] (eq all_l all_r) [1]] 1) all_l all_r /\
           malformed (cert [be "trans" (eq in_l in_r) [1; 1]; be "trans" (eq in_l in_r) [0; 0];
                            bq "quant-intro" [term] (eq all_l all_r) [1]] 2) all_l all_r) =
  assert_norm (malformed (cert [be "rewrite" (eq in_l in_r) [1]; bq "quant-intro" [term] (eq all_l all_r) [0]] 1) all_l all_r);
  assert_norm (malformed (cert [be "rewrite" (eq in_l in_r) []; bq "quant-intro" [term] (eq all_l all_r) [1]] 1) all_l all_r);
  assert_norm (malformed (cert [be "trans" (eq in_l in_r) [1; 1]; be "trans" (eq in_l in_r) [0; 0];
                                bq "quant-intro" [term] (eq all_l all_r) [1]] 2) all_l all_r)

(* B10 the NNF calculus is unchanged: the A1 body proof under an nnf-pos
   root (the root step renamed), or under an nnf-pos step above the A1
   quant-intro root, stays pending (only a quant-intro root replays rewrite
   leaves and quant-intro steps), while A1 itself replays. *)
let b10_nnf_root : U.binder_certificate =
  cert (L.append (L.init a1_entries) [bq "nnf-pos" [term] (eq a1_lhs a1_rhs) [4]]) 5
let b10_nnf_above : U.binder_certificate =
  cert (L.append a1_entries [be "nnf-pos" (eq (mk_and [a1_lhs]) (mk_and [a1_rhs])) [5]]) 6
let b10_nnf_unchanged ()
  : Lemma (pending b10_nnf_root a1_lhs a1_rhs /\
           pending b10_nnf_above (mk_and [a1_lhs]) (mk_and [a1_rhs]) /\
           replays a1_cert a1_lhs a1_rhs) =
  assert_norm (pending b10_nnf_root a1_lhs a1_rhs);
  assert_norm (pending b10_nnf_above (mk_and [a1_lhs]) (mk_and [a1_rhs]));
  assert_norm (replays a1_cert a1_lhs a1_rhs)

(* B11 a rewrite leaf with a premise or with binder sorts is outside the
   calculus (the A1 certificate with its first leaf changed). *)
let b11_with_premise : U.binder_certificate =
  cert [be "refl" (eq in_r in_r) []; be "rewrite" (eq in_l in_r) [0];
        bq "quant-intro" [term] (eq all_l all_r) [1];
        be "monotonicity" (eq out_l out_m) [2];
        be "rewrite" (eq out_m out_r) [];
        be "trans" (eq out_l out_r) [3; 4];
        bq "quant-intro" [term] (eq a1_lhs a1_rhs) [5]] 6
let b11_with_sorts : U.binder_certificate =
  cert (bq "rewrite" [term] (eq in_l in_r) [] :: L.tl a1_entries) 5
let b11_rewrite_payload ()
  : Lemma (pending b11_with_premise a1_lhs a1_rhs /\ pending b11_with_sorts a1_lhs a1_rhs) =
  assert_norm (pending b11_with_premise a1_lhs a1_rhs);
  assert_norm (pending b11_with_sorts a1_lhs a1_rhs)

(* B12 a VALID closed root (the A1 equation, which A1 certifies) over a
   CORRUPTED used internal entry: two false open leaves whose errors cancel
   in the trans step,
     (P x => A) = (and (P x) A)         (false at P x = false, D5)
     (and (P x) A) = (or (not (P x)) A) (false at P x = false)
   so the closed root equation is true but its proof reads false open
   facts. The scope-demanded invariant refuses it. *)
let k_m : expr = mk_and [p_ t0; all_r]
let b12_entries : list U.binder_entry = [
  be "rewrite" (eq in_l in_r) [];
  bq "quant-intro" [term] (eq all_l all_r) [0];
  be "monotonicity" (eq out_l out_m) [1];
  be "rewrite" (eq out_m k_m) [];
  be "rewrite" (eq k_m out_r) [];
  be "trans" (eq out_m out_r) [3; 4];
  be "trans" (eq out_l out_r) [2; 5];
  bq "quant-intro" [term] (eq a1_lhs a1_rhs) [6]]
let b12_corrupted_internal ()
  : Lemma (pending (cert b12_entries 7) a1_lhs a1_rhs /\ replays a1_cert a1_lhs a1_rhs) =
  assert_norm (pending (cert b12_entries 7) a1_lhs a1_rhs);
  assert_norm (replays a1_cert a1_lhs a1_rhs)

(* ---------------------------------------------------------------------- *)
(* C. The node and the document                                             *)
(* ---------------------------------------------------------------------- *)

let entry (r:U.rule) (f:expr) (ids:list int) : P.entry = { P.rule = r; formula = f; premise_ids = ids }

let doc (assertions:list expr) (entries:list P.entry) (root:int) : P.document = {
  P.declarations = []; P.expressions = []; P.assertions = assertions; P.entries = entries; P.root = root;
}

let qi_node (c:U.binder_certificate) (lhs rhs:expr) : U.proof_node =
  { U.kind = U.QuantifierIntroduction c; conclusion = U.Equal lhs rhs; premises = [] }

(* The disjuncts of check_node_cached other than the certificate replay for
   a premise-free node: the bounded propositional, equality, quantifier
   equality and datatype consequence of no premises. *)
let old_paths (node:U.proof_node) : bool =
  SP.consequence PT.core_schema [] (SP.proposition node.U.conclusion) ||
  DT.consequence PT.core_schema [] (SP.scoped_proposition ({ U.conclusion = node.U.conclusion; hypotheses = [] }))

let checked (lhs rhs:expr) : option (U.checked_fact & nat) =
  Some ({ U.conclusion = U.Equal lhs rhs; hypotheses = [] }, 0)

(* C1 the A2 node is outside every other disjunct (red) and the replay checks
   it (green); the A1 node is checked too (the small A1 equation is ALSO
   within the old bounded propositional congruence, which the actual
   Tactics.BreakVC node of the same shape exceeds). *)
let c1_nodes ()
  : Lemma (not (old_paths (qi_node a2_cert a2_lhs a2_rhs)) /\
           SP.check_node PT.core_schema [] (qi_node a2_cert a2_lhs a2_rhs) == checked a2_lhs a2_rhs /\
           SP.check_node PT.core_schema [] (qi_node a1_cert a1_lhs a1_rhs) == checked a1_lhs a1_rhs /\
           old_paths (qi_node a1_cert a1_lhs a1_rhs)) =
  assert_norm (not (old_paths (qi_node a2_cert a2_lhs a2_rhs)));
  assert_norm (SP.check_node PT.core_schema [] (qi_node a2_cert a2_lhs a2_rhs) == checked a2_lhs a2_rhs);
  assert_norm (SP.check_node PT.core_schema [] (qi_node a1_cert a1_lhs a1_rhs) == checked a1_lhs a1_rhs);
  assert_norm (old_paths (qi_node a1_cert a1_lhs a1_rhs))

(* C2 a refutation of the negated equation through the quant-intro node:
   certified by the Root gate (which reads and covers the consumed
   certificate) for A1 and A2, pending for the mutant B1 and for the Int
   counterpart of B12 (a VALID closed A2 root over two cancelling corrupted
   open leaves; the A2 node is outside every other disjunct, C1, so only the
   replay could close it). The small A1 equation itself is also within the
   bounded propositional congruence of the old disjuncts, so a corrupted A1
   certificate is refused by the replay (B12) without changing that
   document's verdict. *)
let refutation (c:U.binder_certificate) (lhs rhs:expr) : P.document =
  doc [neg (eq lhs rhs)]
      [entry U.Asserted (neg (eq lhs rhs)) [];
       entry (U.QuantifierIntroduction c) (eq lhs rhs) [];
       entry U.UnitResolution R.false_expr [1; 0]]
      2

let c2_certified ()
  : Lemma (RD.check_root_document PT.core_schema (refutation a1_cert a1_lhs a1_rhs) == RD.RootCertified /\
           RD.check_root_document PT.core_schema (refutation a2_cert a2_lhs a2_rhs) == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (refutation a1_cert a1_lhs a1_rhs) == RD.RootCertified);
  assert_norm (RD.check_root_document PT.core_schema (refutation a2_cert a2_lhs a2_rhs) == RD.RootCertified)

(* The Int B12: (not D => pi x) = (and (not D) (pi x)) and
   (and (not D) (pi x)) = (or D (pi x)), both false when D holds. *)
let kx : expr = mk_and [neg dxy; pix]
let b12i_entries : list U.binder_entry = [
  be "rewrite" (eq gxy (neg lxy)) [];
  be "rewrite" (eq lxy dxy) [];
  be "monotonicity" (eq (neg lxy) (neg dxy)) [1];
  be "trans" (eq gxy (neg dxy)) [0; 2];
  be "monotonicity" (eq b2_l b2_m) [3];
  be "rewrite" (eq b2_m kx) [];
  be "rewrite" (eq kx b2_r) [];
  be "trans" (eq b2_m b2_r) [5; 6];
  be "trans" (eq b2_l b2_r) [4; 7];
  bq "quant-intro" [integer] (eq a2_inner_l a2_inner_r) [8];
  bq "quant-intro" [integer] (eq a2_lhs a2_rhs) [9]]

let c2_mutants_pending ()
  : Lemma (RD.check_root_document PT.core_schema (refutation (cert b1_entries 5) a1_lhs b1_rhs) == RD.RootPending 1 /\
           pending (cert b12i_entries 10) a2_lhs a2_rhs /\
           RD.check_root_document PT.core_schema (refutation (cert b12i_entries 10) a2_lhs a2_rhs) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (refutation (cert b1_entries 5) a1_lhs b1_rhs) == RD.RootPending 1);
  assert_norm (pending (cert b12i_entries 10) a2_lhs a2_rhs);
  assert_norm (RD.check_root_document PT.core_schema (refutation (cert b12i_entries 10) a2_lhs a2_rhs) == RD.RootPending 1)

(* A malformed quant-intro certificate (the A1 certificate with a forward
   premise id in its first leaf) rejects its document, which A1 certifies. *)
let a1_forward : U.binder_certificate = cert (be "rewrite" (eq in_l in_r) [1] :: L.tl a1_entries) 5
let c2_malformed_rejected ()
  : Lemma (malformed a1_forward a1_lhs a1_rhs /\
           RD.check_root_document PT.core_schema (refutation a1_forward a1_lhs a1_rhs) == RD.RootRejected) =
  assert_norm (malformed a1_forward a1_lhs a1_rhs);
  assert_norm (RD.check_root_document PT.core_schema (refutation a1_forward a1_lhs a1_rhs) == RD.RootRejected)

(* C3 the certified refutations are falsified in EVERY root model, so the
   A1 and A2 equations are root-true in every root model (every u): the
   replay theorem's conclusion in a populated model, reached through the
   document theorem (quantifier laws derived from R1, nothing assumed). *)
let lemma_not_holds (u:TR.uninterpreted) (i:TR.interp u PT.core_schema) (x:expr)
  : Lemma (requires TR.root_model u PT.core_schema i /\ D.scoped [] (neg x) /\ not (RD.root_holds u PT.core_schema i (neg x)))
          (ensures RD.root_holds u PT.core_schema i x) =
  Z3NnfReplayTests.lemma_not_value u i [] (RD.empty_root u PT.core_schema) x

let c3_valid (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures RD.root_holds u PT.core_schema i (eq a1_lhs a1_rhs) /\
                   RD.root_holds u PT.core_schema i (eq a2_lhs a2_rhs)) =
  c2_certified ();
  RD.lemma_root_certified u PT.core_schema (refutation a1_cert a1_lhs a1_rhs) i;
  RD.lemma_root_certified u PT.core_schema (refutation a2_cert a2_lhs a2_rhs) i;
  assert_norm (D.scoped [] (neg (eq a1_lhs a1_rhs)) /\ D.scoped [] (neg (eq a2_lhs a2_rhs)));
  lemma_not_holds u i (eq a1_lhs a1_rhs);
  lemma_not_holds u i (eq a2_lhs a2_rhs)

(* ... in particular in the standard root model of every u and every free
   choice uf (L1): a populated, unconditional instance. *)
let c3_standard (u:TR.uninterpreted) (uf:TR.symbols u PT.core_schema)
  : Lemma (RD.root_holds u PT.core_schema (TR.standard u PT.core_schema uf) (eq a1_lhs a1_rhs) /\
           RD.root_holds u PT.core_schema (TR.standard u PT.core_schema uf) (eq a2_lhs a2_rhs)) =
  TR.lemma_standard_root u PT.core_schema uf;
  c3_valid u (TR.standard u PT.core_schema uf)

(* C4 coverage of the consumed quant-intro certificate: A1 and A2 are
   covered; an unsupported internal term (a zero-index array constant in an
   entry the root does not even use) makes a consumed quant-intro
   certificate uncovered; a certificate with another root is not consumed
   and not gated. *)
let zero_index : expr = App (symbol "zero-index" [] (ArraySort [] integer)) []
let c4_coverage ()
  : Lemma (RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction a1_cert) /\
           RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction a2_cert) /\
           not (RD.certificate_covered (S.signature PT.core_schema)
                  (U.QuantifierIntroduction (cert (L.append a1_entries [be "refl" (eq zero_index zero_index) []]) 5))) /\
           RD.certificate_covered (S.signature PT.core_schema)
             (U.QuantifierIntroduction (cert (L.append a1_entries [be "refl" (eq zero_index zero_index) []]) 6))) =
  assert_norm (RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction a1_cert));
  assert_norm (RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction a2_cert));
  assert_norm (not (RD.certificate_covered (S.signature PT.core_schema)
                      (U.QuantifierIntroduction (cert (L.append a1_entries [be "refl" (eq zero_index zero_index) []]) 5))));
  assert_norm (RD.certificate_covered (S.signature PT.core_schema)
                 (U.QuantifierIntroduction (cert (L.append a1_entries [be "refl" (eq zero_index zero_index) []]) 6)))
