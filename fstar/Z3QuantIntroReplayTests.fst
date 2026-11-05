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
         two-sorted binder list in de Bruijn order;
      A4 the iff/negation normalization of a wide disjunction (decided at
         the coarser depth-2 cut; B13 are its wrong-sign mutants);
      A5 the truth-table guard of the bounded propositional check: the
         same result as before, 12 atoms checked, 13 atoms refused;
      A6 regrouped connectives (the Pulse.Checker.Base-1 q1 node 356
         re-association leaves, decided by NR.regrouped, beyond the depth-2
         table), small regroupings, and the theorem in every Sorted model;
         B14 are its refused mutants.
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
module N = Z3BooleanNormalForm

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

(* A4 the iff/negation normalization of a wide disjunction (the actual
   shape of FStar.Sequence.Permutation q5 node383 and Pulse.Lib.RingBuffer
   q22 node85, there with 14-38 literals):  (= a (not o)) = (not (= o a))
   with o a disjunction of 12 negated atoms under a Term binder. With `a`
   the depth-64 cut has 13 atoms, one more than its truth-table bound, so
   only the coarser depth-2 cut (atoms a and o) decides it.
   B13 wrong-sign mutants, both pending: the outer negation dropped,
   (= o a) (refused at both depths: o is expanded at depth 2 too), and the
   negation moved inside, (= (not o) (not a)) (refuted by the two-atom
   depth-2 table). Both are the complement of the A4 leaf (counter-model
   D8 of Z3QuantIntroCounterModelTests). *)
let wd (name:string) : func_decl = symbol name [term] bool_sort
let w_ (name:string) : expr = App (wd name) [t0]
let a4_lits : list expr = [
  neg (w_ "w1"); neg (w_ "w2"); neg (w_ "w3"); neg (w_ "w4"); neg (w_ "w5"); neg (w_ "w6");
  neg (w_ "w7"); neg (w_ "w8"); neg (w_ "w9"); neg (w_ "w10"); neg (w_ "w11"); neg (w_ "w12")]
let a4_o : expr = mk_or a4_lits
let a4_l : expr = eq (p_ t0) (neg a4_o)
let a4_r : expr = neg (eq a4_o (p_ t0))
let b13_r : expr = eq a4_o (p_ t0)
let b13_inner_r : expr = eq (neg a4_o) (neg (p_ t0))
let a4_cert (rhs:expr) : U.binder_certificate =
  cert [be "rewrite" (eq a4_l rhs) []; bq "quant-intro" [term] (eq (forall_ [term] a4_l) (forall_ [term] rhs)) [0]] 1
let a4_iff_negation ()
  : Lemma (not (NR.propositional_at 64 a4_l a4_r) /\ NR.propositional_at 2 a4_l a4_r /\
           replays (a4_cert a4_r) (forall_ [term] a4_l) (forall_ [term] a4_r)) =
  assert_norm (not (NR.propositional_at 64 a4_l a4_r));
  assert_norm (NR.propositional_at 2 a4_l a4_r);
  assert_norm (replays (a4_cert a4_r) (forall_ [term] a4_l) (forall_ [term] a4_r))

let b13_iff_sign ()
  : Lemma (pending (a4_cert b13_r) (forall_ [term] a4_l) (forall_ [term] b13_r) /\
           not (NR.propositional_at 2 a4_l b13_inner_r) /\
           pending (a4_cert b13_inner_r) (forall_ [term] a4_l) (forall_ [term] b13_inner_r)) =
  assert_norm (pending (a4_cert b13_r) (forall_ [term] a4_l) (forall_ [term] b13_r));
  assert_norm (not (NR.propositional_at 2 a4_l b13_inner_r));
  assert_norm (pending (a4_cert b13_inner_r) (forall_ [term] a4_l) (forall_ [term] b13_inner_r))

(* A5 the truth-table guard of the bounded propositional check. The `if`
   of Z3SortedDatatype.propositional_core returns exactly the Boolean of
   the `&&` it replaced (prior_core is the previous definition verbatim),
   so the bound is still 12 atoms. At exactly 12 atoms (11 literals and
   `a`, closed atoms) the iff/negation leaf misses every earlier disjunct
   and the truth table accepts it; with 13 atoms (A4) it misses them too and
   is refused by the atom bound, without enumerating rows. *)
let prior_core (bounded_context:bool) (f:B.skeleton) : bool =
  if DT.shape_equivalence f then true else
  let simplified = N.normalize false f in
  if simplified = B.Bool true then true
  else if N.clause_tautology simplified then true
  else if (not bounded_context || Some? (DT.context_budget 256 f)) &&
          N.equivalent f (B.Bool true) then true
  else
    let atoms = B.unique (B.support simplified) in
    L.length atoms <= 12 && B.check_rows atoms (fun _ -> false) simplified (B.Bool true)

let a5_guard_unchanged (bounded_context:bool) (f:B.skeleton)
  : Lemma (DT.propositional_core bounded_context f == prior_core bounded_context f) = ()

let c_ (name:string) : expr = App (symbol name [] bool_sort) []
let a5_o : expr = mk_or [neg (c_ "c1"); neg (c_ "c2"); neg (c_ "c3"); neg (c_ "c4"); neg (c_ "c5"); neg (c_ "c6");
                         neg (c_ "c7"); neg (c_ "c8"); neg (c_ "c9"); neg (c_ "c10"); neg (c_ "c11")]
let a5_l : expr = eq (c_ "a") (neg a5_o)
let a5_r : expr = neg (eq a5_o (c_ "a"))
let a5_f : B.skeleton = B.Eq (T.cut 64 a5_l) (T.cut 64 a5_r)
let a4_f : B.skeleton = B.Eq (T.cut 64 a4_l) (T.cut 64 a4_r)

let a5_twelve_atoms ()
  : Lemma (L.length (B.unique (B.support (N.normalize false a5_f))) = 12 /\
           not (DT.shape_equivalence a5_f) /\ not (N.clause_tautology (N.normalize false a5_f)) /\
           not (N.equivalent a5_f (B.Bool true)) /\
           DT.bounded_propositional a5_f /\ NR.propositional_at 64 a5_l a5_r) =
  assert_norm (L.length (B.unique (B.support (N.normalize false a5_f))) = 12);
  assert_norm (not (DT.shape_equivalence a5_f) /\ not (N.clause_tautology (N.normalize false a5_f)));
  assert_norm (not (N.equivalent a5_f (B.Bool true)));
  assert_norm (DT.bounded_propositional a5_f)

let a5_thirteen_atoms ()
  : Lemma (L.length (B.unique (B.support (N.normalize false a4_f))) = 13 /\
           not (DT.shape_equivalence a4_f) /\ not (N.clause_tautology (N.normalize false a4_f)) /\
           not (N.equivalent a4_f (B.Bool true)) /\
           not (DT.bounded_propositional a4_f)) =
  assert_norm (L.length (B.unique (B.support (N.normalize false a4_f))) = 13);
  assert_norm (not (N.normalize false a4_f = B.Bool true));
  assert_norm (not (DT.shape_equivalence a4_f) /\ not (N.clause_tautology (N.normalize false a4_f)));
  assert_norm (not (N.equivalent a4_f (B.Bool true)));
  a5_guard_unchanged true a4_f

(* A6 regrouped connectives: the n-ary re-association leaves of
   Pulse.Checker.Base-1 q1 (callback 1, node 356, entries 146/150/156/164),
   e.g. (or d1 d2 d3 d4) = (or (or d1 d2) (or d3 d4)) with 80-94 KB
   operands. In a6_l/a6_r one operand, `deep`, nests alternating and/or 71
   Boolean levels deep (two closed atoms per level), so, as in the actual
   leaves, the two sides' cuts put their atom boundaries inside it at
   different depths: the depth-2 table refutes the leaf (below) and the
   depth-64 check refuses it too (normalizing that refusal takes F* about
   15 minutes, so it is asserted by the native bridge test instead,
   test_native_bridge.ml `sorted_quant_intro_regrouping`). The leaf is
   decided by the regrouping (NR.regrouped) and the certificate replays.
   The small shapes are the regrouping's own verdicts: re-association,
   commutation and duplicates (at most 12 operands), nested and, unary and
   empty connectives, and an and operand inside an or. *)
let g_ (name:string) : expr = c_ name
let rec chain (n:nat) : expr =
  let level = [c_ ("y" ^ string_of_int n); c_ ("z" ^ string_of_int n)] in
  if n = 0 then mk_or level
  else if n % 2 = 0 then mk_or (L.append level [chain (n - 1)])
  else mk_and (L.append level [chain (n - 1)])
let deep : expr = chain 70
let a6_l : expr = mk_or [g_ "g1"; g_ "g2"; g_ "g3"; deep]
let a6_r : expr = mk_or [mk_or [g_ "g1"; g_ "g2"]; mk_or [g_ "g3"; deep]]
let a6_cert (l r:expr) : U.binder_certificate =
  cert [be "rewrite" (eq l r) []; bq "quant-intro" [term] (eq (forall_ [term] l) (forall_ [term] r)) [0]] 1

let a6_regrouped ()
  : Lemma (not (Z3SortedArithmetic.equivalent a6_l a6_r) /\ not (NR.propositional_at 2 a6_l a6_r) /\
           NR.regrouped a6_l a6_r /\ NR.rewrite_ok a6_l a6_r /\
           replays (a6_cert a6_l a6_r) (forall_ [term] a6_l) (forall_ [term] a6_r)) =
  assert_norm (not (Z3SortedArithmetic.equivalent a6_l a6_r));
  assert_norm (not (NR.propositional_at 2 a6_l a6_r));
  assert_norm (NR.regrouped a6_l a6_r);
  assert_norm (NR.rewrite_ok a6_l a6_r);
  assert_norm (replays (a6_cert a6_l a6_r) (forall_ [term] a6_l) (forall_ [term] a6_r))

let a6_shapes : list (expr & expr) = [
  mk_or [g_ "g1"; g_ "g2"; g_ "g3"; g_ "g4"], mk_or [mk_or [g_ "g1"; g_ "g2"]; mk_or [g_ "g3"; g_ "g4"]];
  mk_or [g_ "g1"; g_ "g2"; g_ "g3"], mk_or [g_ "g3"; mk_or [g_ "g2"; g_ "g1"]];
  mk_or [g_ "g1"; g_ "g2"; g_ "g1"], mk_or [mk_or [g_ "g2"; g_ "g1"]];
  mk_and [g_ "g1"; mk_and [g_ "g2"; g_ "g3"]; g_ "g4"], mk_and [mk_and [g_ "g1"; g_ "g2"]; mk_and [g_ "g3"; g_ "g4"]];
  mk_or [g_ "g1"], g_ "g1";
  mk_or [], mk_or [mk_or []];
  mk_and [], mk_and [mk_and []; mk_and []];
  mk_or [mk_and [g_ "g1"; g_ "g2"]; g_ "g3"], mk_or [mk_or [mk_and [g_ "g1"; g_ "g2"]]; g_ "g3"]]

let a6_ok (lr:expr & expr) : bool =
  NR.regrouped (fst lr) (snd lr) && NR.rewrite_ok (fst lr) (snd lr) &&
  replays (a6_cert (fst lr) (snd lr)) (forall_ [term] (fst lr)) (forall_ [term] (snd lr))

let scoped_pair (lr:expr & expr) : bool = D.scoped [term] (fst lr) && D.scoped [term] (snd lr)

let a6_small_shapes () : Lemma (L.for_all a6_ok a6_shapes /\ L.for_all scoped_pair a6_shapes) =
  assert_norm (L.for_all a6_ok a6_shapes);
  assert_norm (L.for_all scoped_pair a6_shapes)

let rec lemma_for_all_memP (#a:Type) (f:a -> Tot bool) (l:list a) (x:a)
  : Lemma (requires L.for_all f l /\ L.memP x l) (ensures f x) (decreases l) =
  match l with
  | [] -> ()
  | _ :: rest -> FStar.Classical.move_requires (lemma_for_all_memP f rest) x

(* The theorem in EVERY Sorted model, at every typed environment of the
   leaf's scope [Term]: both sides have one value (NR.lemma_rewrite_at,
   from the regrouping's soundness lemma NR.lemma_regrouped_at). *)
let a6_valid (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
             (rho:V.environment base (S.signature s) [term])
  : Lemma (NR.same_at s bc eq other [term] rho a6_l a6_r /\
           (forall (lr:expr & expr). L.memP lr a6_shapes ==>
              NR.same_at s bc eq other [term] rho (fst lr) (snd lr))) =
  a6_regrouped (); a6_small_shapes ();
  assert_norm (D.scoped [term] a6_l /\ D.scoped [term] a6_r);
  NR.lemma_rewrite_at s bc eq other [term] rho a6_l a6_r;
  let at (lr:expr & expr)
    : Lemma (requires L.memP lr a6_shapes) (ensures NR.same_at s bc eq other [term] rho (fst lr) (snd lr)) =
    lemma_for_all_memP a6_ok a6_shapes lr;
    lemma_for_all_memP scoped_pair a6_shapes lr;
    NR.lemma_rewrite_at s bc eq other [term] rho (fst lr) (snd lr) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires at)

(* B14 regrouping mutants, each refused by the whole rewrite check (the
   regrouping and the propositional checks alike) and pending as a
   certificate; opposite-value counter-models at an environment of the
   leaf's scope [Term] are D9 in Z3QuantIntroCounterModelTests: a dropped
   operand, an extra operand, and in place of or (swapped), a counterfeit
   `or` (another declaration: no interpretation), xor in place of or, an
   operand of the wrong polarity, a wrong atom, and the empty or against
   the empty and. An `or`-named operator over a non-Boolean argument sort
   is not a canonical connective, so it is never opened (one operand). *)
let fake_or : func_decl = symbol "or" [bool_sort; bool_sort] bool_sort
let xor_d : func_decl = { decl_name = "xor"; domain = [bool_sort; bool_sort]; range = bool_sort;
                          interp = Some op_xor; int_params = [] }
let or_mixed : func_decl = { decl_name = "or"; domain = [bool_sort; term]; range = bool_sort;
                             interp = Some op_or; int_params = [] }
let b14_or3 : expr = mk_or [g_ "g1"; g_ "g2"; g_ "g3"]
let b14_dropped : expr & expr = b14_or3, mk_or [mk_or [g_ "g1"; g_ "g2"]]
let b14_extra : expr & expr = mk_or [g_ "g1"; g_ "g2"], mk_or [mk_or [g_ "g1"; g_ "g2"]; g_ "g3"]
let b14_swapped : expr & expr =
  mk_or [g_ "g1"; g_ "g2"; g_ "g3"; g_ "g4"], mk_or [mk_and [g_ "g1"; g_ "g2"]; mk_or [g_ "g3"; g_ "g4"]]
let b14_counterfeit : expr & expr = b14_or3, mk_or [App fake_or [g_ "g1"; g_ "g2"]; g_ "g3"]
let b14_xor : expr & expr = b14_or3, mk_or [App xor_d [g_ "g1"; g_ "g2"]; g_ "g3"]
let b14_polarity : expr & expr = b14_or3, mk_or [mk_or [g_ "g1"; neg (g_ "g2")]; g_ "g3"]
let b14_wrong_atom : expr & expr = b14_or3, mk_or [mk_or [g_ "g1"; g_ "g2"]; g_ "g4"]
let b14_empty : expr & expr = mk_or [], mk_and []
let b14_mutants : list (expr & expr) = [
  b14_dropped; b14_extra; b14_swapped; b14_counterfeit; b14_xor; b14_polarity; b14_wrong_atom; b14_empty]

let refused (lr:expr & expr) : bool =
  not (NR.regrouped (fst lr) (snd lr)) && not (NR.rewrite_ok (fst lr) (snd lr)) &&
  pending (a6_cert (fst lr) (snd lr)) (forall_ [term] (fst lr)) (forall_ [term] (snd lr))

let b14_regrouping_mutants ()
  : Lemma (L.for_all refused b14_mutants /\
           NR.operands B.Or (App or_mixed [g_ "g1"; App (symbol "tc" [] term) []]) ==
             Some [App or_mixed [g_ "g1"; App (symbol "tc" [] term) []]]) =
  assert_norm (L.for_all refused b14_mutants);
  assert_norm (NR.operands B.Or (App or_mixed [g_ "g1"; App (symbol "tc" [] term) []]) ==
               Some [App or_mixed [g_ "g1"; App (symbol "tc" [] term) []]])

(* B15 the depth admission: both sides of a regrouping must be at most 4096
   levels deep, which bounds the structural operand comparisons. With the
   operand f^k(a) (an uninterpreted f), the right side's deepest node is at
   level k + 2: k = 4094 is regrouped, k = 4095 is refused (a sound
   refusal; the leaf is true). *)
let fd : func_decl = symbol "f" [bool_sort] bool_sort
let rec applied (k:nat) (acc:expr) : Tot expr (decreases k) =
  if k = 0 then acc else applied (k - 1) (App fd [acc])
let b15_shape (k:nat) : expr & expr =
  mk_or [applied k (g_ "a"); g_ "g2"; g_ "g3"], mk_or [mk_or [applied k (g_ "a"); g_ "g2"]; g_ "g3"]
let b15_depth_admission ()
  : Lemma (NR.regrouped (fst (b15_shape 4094)) (snd (b15_shape 4094)) /\
           not (NR.regrouped (fst (b15_shape 4095)) (snd (b15_shape 4095)))) =
  assert_norm (NR.regrouped (fst (b15_shape 4094)) (snd (b15_shape 4094)));
  assert_norm (not (NR.regrouped (fst (b15_shape 4095)) (snd (b15_shape 4095))))

(* A7 the ITE laws of bool_rewriter::mk_ite_core (NR.ite_rewritten) at every
   result sort. First the captured term-ITE leaves of the 9af capture,
   reconstructed from its certdump (declarations keep their marshalled
   names; their signatures are inferred from the leaf itself, U_zero is a
   Universe and BoxReal takes a Real; s1 receipt, to_fstar.py), each as the
   leaf of a certificate at its captured binder list:
     Pulse.Checker.Base-1 q1 node 3021 entry 25, the negated condition at
       sort Term (39/38 tree nodes, scope [Term; Term; Fuel]);
     Pulse.Checker.Base-1 q1 node 3010 entry 0, the then merge by a binary
       `or` (599/598 tree nodes, the same scope);
     Pulse.Lib.AnchoredReference q13 node 447 entry 0, the else merge whose
       condition the producer flattened, (and A B) and (and C D) into
       (and A B C D), with a Real numeral inside a branch (its whole
       captured certificate: rewrite, monotonicity, quant-intro over
       [Universe; Term x 6]).
   At 9af the three leaves are pending: the sides are Term-sorted, so the
   Int equivalence and the Boolean checks refuse them; the ITE laws accept
   them (and nothing reads the Real numeral). *)
let term_s : sort = BaseSort "sort!2147483829:Term"
let universe_s : sort = BaseSort "sort!2147483800:Universe"
let fuel_s : sort = BaseSort "sort!2147483833:Fuel"
let real_s : sort = TR.real_s

let ite_ (c x y:expr) : expr = App (T.ite_decl (get_sort x)) [c; x; y]

let native_num (name:string) (n:int) : expr =
  App { decl_name = name; domain = []; range = integer; interp = Some op_num_rational; int_params = [n; 1] } []

let real_num (name:string) (n:int) : expr =
  App { decl_name = name; domain = []; range = real_s; interp = Some op_num_rational; int_params = [n; 1] } []

(* Pulse.Checker.Base-1 q1 node 3021, entry 25 (base1-q1-n3021.certdump.jsonl): lhs 39 / rhs 38 tree nodes *)
let n3021_x_U_zero_3801 : func_decl =
  symbol "decl!2147483801:U_zero" [] universe_s
let n3021_x_Term_constr_id_3830 : func_decl =
  symbol "decl!2147483830:Term_constr_id" [term_s] integer
let n3021_x_Tm_unit_3922 : func_decl =
  symbol "decl!2147483922:Tm_unit" [] term_s
let n3021_x_Some_4048 : func_decl =
  symbol "decl!2147484048:FStar.Pervasives.Native.Some" [universe_s; term_s; term_s] term_s
let n3021_x_Some__0_4049 : func_decl =
  symbol "decl!2147484049:FStar.Pervasives.Native.Some_@0" [term_s] universe_s
let n3021_x_Some__a_4050 : func_decl =
  symbol "decl!2147484050:FStar.Pervasives.Native.Some_@a" [term_s] term_s
let n3021_x_Some__v_4051 : func_decl =
  symbol "decl!2147484051:FStar.Pervasives.Native.Some_@v" [term_s] term_s
let n3021_x_fuel_instrumented_4137 : func_decl =
  symbol "decl!2147484137:FStar.Reflection.Typing.subst_match_returns.fuel_instrumented" [fuel_s; term_s; term_s] term_s
let n3021_x_inspect_ln_4182 : func_decl =
  symbol "decl!2147484182:FStar.Stubs.Reflection.V2.Builtins.inspect_ln" [term_s] term_s
let n3021_x_Tv_Match__ret_4290 : func_decl =
  symbol "decl!2147484290:FStar.Stubs.Reflection.V2.Data.Tv_Match_@ret" [term_s] term_s
let n3021_x_match_returns_ascription_4351 : func_decl =
  symbol "decl!2147484351:FStar.Stubs.Syntax.Syntax.match_returns_ascription" [] term_s
let n3021_lhs : expr =
  (ite_ (neg (mk_or [(neg (eq (App n3021_x_Term_constr_id_3830 [(App n3021_x_Tv_Match__ret_4290 [(App
    n3021_x_inspect_ln_4182 [(Var 1 term_s)])])]) (native_num "113" 113))); (neg (eq (App
    n3021_x_Tv_Match__ret_4290 [(App n3021_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3021_x_Some_4048 [(App
    n3021_x_Some__0_4049 [(App n3021_x_Tv_Match__ret_4290 [(App n3021_x_inspect_ln_4182 [(Var 1
    term_s)])])]); (App n3021_x_Some__a_4050 [(App n3021_x_Tv_Match__ret_4290 [(App n3021_x_inspect_ln_4182
    [(Var 1 term_s)])])]); (App n3021_x_Some__v_4051 [(App n3021_x_Tv_Match__ret_4290 [(App
    n3021_x_inspect_ln_4182 [(Var 1 term_s)])])])])))])) (App n3021_x_Some_4048 [(App n3021_x_U_zero_3801
    []); (App n3021_x_match_returns_ascription_4351 []); (App n3021_x_fuel_instrumented_4137 [(Var 2 fuel_s);
    (App n3021_x_Some__v_4051 [(App n3021_x_Tv_Match__ret_4290 [(App n3021_x_inspect_ln_4182 [(Var 1
    term_s)])])]); (Var 0 term_s)])]) (App n3021_x_Tm_unit_3922 []))
let n3021_rhs : expr =
  (ite_ (mk_or [(neg (eq (App n3021_x_Term_constr_id_3830 [(App n3021_x_Tv_Match__ret_4290 [(App
    n3021_x_inspect_ln_4182 [(Var 1 term_s)])])]) (native_num "113" 113))); (neg (eq (App
    n3021_x_Tv_Match__ret_4290 [(App n3021_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3021_x_Some_4048 [(App
    n3021_x_Some__0_4049 [(App n3021_x_Tv_Match__ret_4290 [(App n3021_x_inspect_ln_4182 [(Var 1
    term_s)])])]); (App n3021_x_Some__a_4050 [(App n3021_x_Tv_Match__ret_4290 [(App n3021_x_inspect_ln_4182
    [(Var 1 term_s)])])]); (App n3021_x_Some__v_4051 [(App n3021_x_Tv_Match__ret_4290 [(App
    n3021_x_inspect_ln_4182 [(Var 1 term_s)])])])])))]) (App n3021_x_Tm_unit_3922 []) (App n3021_x_Some_4048
    [(App n3021_x_U_zero_3801 []); (App n3021_x_match_returns_ascription_4351 []); (App
    n3021_x_fuel_instrumented_4137 [(Var 2 fuel_s); (App n3021_x_Some__v_4051 [(App
    n3021_x_Tv_Match__ret_4290 [(App n3021_x_inspect_ln_4182 [(Var 1 term_s)])])]); (Var 0 term_s)])]))

(* Pulse.Lib.AnchoredReference q13 node 447, entry 0 (anchoredref-q13-n447.certdump.jsonl): lhs 89 / rhs 86 tree nodes *)
let n447_x_U_zero_3801 : func_decl =
  symbol "decl!2147483801:U_zero" [] universe_s
let n447_x_Term_constr_id_3830 : func_decl =
  symbol "decl!2147483830:Term_constr_id" [term_s] integer
let n447_x_Tm_unit_3922 : func_decl =
  symbol "decl!2147483922:Tm_unit" [] term_s
let n447_x_BoxReal_3966 : func_decl =
  symbol "decl!2147483966:BoxReal" [real_s] term_s
let n447_x_Mktuple2_4034 : func_decl =
  symbol "decl!2147484034:FStar.Pervasives.Native.Mktuple2" [universe_s; universe_s; term_s; term_s; term_s; term_s] term_s
let n447_x_Mktuple2___1_4037 : func_decl =
  symbol "decl!2147484037:FStar.Pervasives.Native.Mktuple2_@_1" [term_s] term_s
let n447_x_Mktuple2___2_4038 : func_decl =
  symbol "decl!2147484038:FStar.Pervasives.Native.Mktuple2_@_2" [term_s] term_s
let n447_x_Some_4044 : func_decl =
  symbol "decl!2147484044:FStar.Pervasives.Native.Some" [universe_s; term_s; term_s] term_s
let n447_x_Some__0_4045 : func_decl =
  symbol "decl!2147484045:FStar.Pervasives.Native.Some_@0" [term_s] universe_s
let n447_x_Some__a_4046 : func_decl =
  symbol "decl!2147484046:FStar.Pervasives.Native.Some_@a" [term_s] term_s
let n447_x_Some__v_4047 : func_decl =
  symbol "decl!2147484047:FStar.Pervasives.Native.Some_@v" [term_s] term_s
let n447_x_option_4053 : func_decl =
  symbol "decl!2147484053:FStar.Pervasives.Native.option" [universe_s; term_s] term_s
let n447_x_Owns_4135 : func_decl =
  symbol "decl!2147484135:Pulse.Lib.FractionalAnchoredPreorder.Owns" [universe_s; term_s; term_s; term_s; term_s] term_s
let n447_x_Owns__0_4136 : func_decl =
  symbol "decl!2147484136:Pulse.Lib.FractionalAnchoredPreorder.Owns_@0" [term_s] universe_s
let n447_x_Owns___0_4137 : func_decl =
  symbol "decl!2147484137:Pulse.Lib.FractionalAnchoredPreorder.Owns_@_0" [term_s] term_s
let n447_x_Owns__anchors_4138 : func_decl =
  symbol "decl!2147484138:Pulse.Lib.FractionalAnchoredPreorder.Owns_@anchors" [term_s] term_s
let n447_x_Owns__p_4139 : func_decl =
  symbol "decl!2147484139:Pulse.Lib.FractionalAnchoredPreorder.Owns_@p" [term_s] term_s
let n447_x_Owns__v_4140 : func_decl =
  symbol "decl!2147484140:Pulse.Lib.FractionalAnchoredPreorder.Owns_@v" [term_s] term_s
let n447_x_permission_4168 : func_decl =
  symbol "decl!2147484168:Pulse.Lib.FractionalAnchoredPreorder.permission" [universe_s; term_s] term_s
let n447_x_perm_4175 : func_decl =
  symbol "decl!2147484175:PulseCore.FractionalPermission.perm" [] term_s
let n447_x_vhist_4189 : func_decl =
  symbol "decl!2147484189:PulseCore.Preorder.vhist" [universe_s; term_s; term_s] term_s
let n447_x_op_Slash_Dot_6280 : func_decl =
  symbol "decl!2147486280:FStar.Real.op_Slash_Dot" [term_s; term_s] term_s
let n447_lhs : expr =
  (ite_ (mk_and [(eq (App n447_x_Term_constr_id_3830 [(Var 0 term_s)]) (native_num "136" 136)); (eq (Var 0
    term_s) (App n447_x_Owns_4135 [(App n447_x_Owns__0_4136 [(Var 0 term_s)]); (App n447_x_Owns__v_4140 [(Var
    0 term_s)]); (App n447_x_Owns__p_4139 [(Var 0 term_s)]); (App n447_x_Owns__anchors_4138 [(Var 0
    term_s)]); (App n447_x_Owns___0_4137 [(Var 0 term_s)])]))]) (ite_ (mk_and [(eq (App
    n447_x_Term_constr_id_3830 [(App n447_x_Mktuple2___1_4037 [(App n447_x_Mktuple2___1_4037 [(App
    n447_x_Owns___0_4137 [(Var 0 term_s)])])])]) (native_num "113" 113)); (eq (App n447_x_Mktuple2___1_4037
    [(App n447_x_Mktuple2___1_4037 [(App n447_x_Owns___0_4137 [(Var 0 term_s)])])]) (App n447_x_Some_4044
    [(App n447_x_Some__0_4045 [(App n447_x_Mktuple2___1_4037 [(App n447_x_Mktuple2___1_4037 [(App
    n447_x_Owns___0_4137 [(Var 0 term_s)])])])]); (App n447_x_Some__a_4046 [(App n447_x_Mktuple2___1_4037
    [(App n447_x_Mktuple2___1_4037 [(App n447_x_Owns___0_4137 [(Var 0 term_s)])])])]); (App
    n447_x_Some__v_4047 [(App n447_x_Mktuple2___1_4037 [(App n447_x_Mktuple2___1_4037 [(App
    n447_x_Owns___0_4137 [(Var 0 term_s)])])])])]))]) (App n447_x_Owns_4135 [(Var 6 universe_s); (Var 5
    term_s); (Var 4 term_s); (Var 3 term_s); (App n447_x_Mktuple2_4034 [(Var 6 universe_s); (Var 6
    universe_s); (App n447_x_permission_4168 [(Var 6 universe_s); (Var 5 term_s)]); (App n447_x_vhist_4189
    [(Var 6 universe_s); (Var 5 term_s); (Var 4 term_s)]); (App n447_x_Mktuple2_4034 [(App n447_x_U_zero_3801
    []); (Var 6 universe_s); (App n447_x_option_4053 [(App n447_x_U_zero_3801 []); (App n447_x_perm_4175
    [])]); (App n447_x_option_4053 [(Var 6 universe_s); (Var 5 term_s)]); (App n447_x_Some_4044 [(App
    n447_x_U_zero_3801 []); (App n447_x_perm_4175 []); (App n447_x_op_Slash_Dot_6280 [(Var 2 term_s); (App
    n447_x_BoxReal_3966 [(real_num "2.0" 2)])])]); (App n447_x_Mktuple2___2_4038 [(App
    n447_x_Mktuple2___1_4037 [(App n447_x_Owns___0_4137 [(Var 0 term_s)])])])]); (App
    n447_x_Mktuple2___2_4038 [(App n447_x_Owns___0_4137 [(Var 0 term_s)])])])]) (App n447_x_Tm_unit_3922 []))
    (App n447_x_Tm_unit_3922 []))
let n447_rhs : expr =
  (ite_ (mk_and [(eq (App n447_x_Term_constr_id_3830 [(Var 0 term_s)]) (native_num "136" 136)); (eq (Var 0
    term_s) (App n447_x_Owns_4135 [(App n447_x_Owns__0_4136 [(Var 0 term_s)]); (App n447_x_Owns__v_4140 [(Var
    0 term_s)]); (App n447_x_Owns__p_4139 [(Var 0 term_s)]); (App n447_x_Owns__anchors_4138 [(Var 0
    term_s)]); (App n447_x_Owns___0_4137 [(Var 0 term_s)])])); (eq (App n447_x_Term_constr_id_3830 [(App
    n447_x_Mktuple2___1_4037 [(App n447_x_Mktuple2___1_4037 [(App n447_x_Owns___0_4137 [(Var 0
    term_s)])])])]) (native_num "113" 113)); (eq (App n447_x_Mktuple2___1_4037 [(App n447_x_Mktuple2___1_4037
    [(App n447_x_Owns___0_4137 [(Var 0 term_s)])])]) (App n447_x_Some_4044 [(App n447_x_Some__0_4045 [(App
    n447_x_Mktuple2___1_4037 [(App n447_x_Mktuple2___1_4037 [(App n447_x_Owns___0_4137 [(Var 0
    term_s)])])])]); (App n447_x_Some__a_4046 [(App n447_x_Mktuple2___1_4037 [(App n447_x_Mktuple2___1_4037
    [(App n447_x_Owns___0_4137 [(Var 0 term_s)])])])]); (App n447_x_Some__v_4047 [(App
    n447_x_Mktuple2___1_4037 [(App n447_x_Mktuple2___1_4037 [(App n447_x_Owns___0_4137 [(Var 0
    term_s)])])])])]))]) (App n447_x_Owns_4135 [(Var 6 universe_s); (Var 5 term_s); (Var 4 term_s); (Var 3
    term_s); (App n447_x_Mktuple2_4034 [(Var 6 universe_s); (Var 6 universe_s); (App n447_x_permission_4168
    [(Var 6 universe_s); (Var 5 term_s)]); (App n447_x_vhist_4189 [(Var 6 universe_s); (Var 5 term_s); (Var 4
    term_s)]); (App n447_x_Mktuple2_4034 [(App n447_x_U_zero_3801 []); (Var 6 universe_s); (App
    n447_x_option_4053 [(App n447_x_U_zero_3801 []); (App n447_x_perm_4175 [])]); (App n447_x_option_4053
    [(Var 6 universe_s); (Var 5 term_s)]); (App n447_x_Some_4044 [(App n447_x_U_zero_3801 []); (App
    n447_x_perm_4175 []); (App n447_x_op_Slash_Dot_6280 [(Var 2 term_s); (App n447_x_BoxReal_3966 [(real_num
    "2.0" 2)])])]); (App n447_x_Mktuple2___2_4038 [(App n447_x_Mktuple2___1_4037 [(App n447_x_Owns___0_4137
    [(Var 0 term_s)])])])]); (App n447_x_Mktuple2___2_4038 [(App n447_x_Owns___0_4137 [(Var 0 term_s)])])])])
    (App n447_x_Tm_unit_3922 []))

(* Pulse.Checker.Base-1 q1 node 3010, entry 0 (base1-q1-n3010.certdump.jsonl): lhs 599 / rhs 598 tree nodes *)
let n3010_x_U_zero_3801 : func_decl =
  symbol "decl!2147483801:U_zero" [] universe_s
let n3010_x_Term_constr_id_3830 : func_decl =
  symbol "decl!2147483830:Term_constr_id" [term_s] integer
let n3010_x_Tm_unit_3922 : func_decl =
  symbol "decl!2147483922:Tm_unit" [] term_s
let n3010_x_BoxBool_3940 : func_decl =
  symbol "decl!2147483940:BoxBool" [bool_sort] term_s
let n3010_x_Mktuple2_4028 : func_decl =
  symbol "decl!2147484028:FStar.Pervasives.Native.Mktuple2" [universe_s; universe_s; term_s; term_s; term_s; term_s] term_s
let n3010_x_None_4045 : func_decl =
  symbol "decl!2147484045:FStar.Pervasives.Native.None" [universe_s; term_s] term_s
let n3010_x_None__0_4046 : func_decl =
  symbol "decl!2147484046:FStar.Pervasives.Native.None_@0" [term_s] universe_s
let n3010_x_None__a_4047 : func_decl =
  symbol "decl!2147484047:FStar.Pervasives.Native.None_@a" [term_s] term_s
let n3010_x_Some_4048 : func_decl =
  symbol "decl!2147484048:FStar.Pervasives.Native.Some" [universe_s; term_s; term_s] term_s
let n3010_x_Some__0_4049 : func_decl =
  symbol "decl!2147484049:FStar.Pervasives.Native.Some_@0" [term_s] universe_s
let n3010_x_Some__a_4050 : func_decl =
  symbol "decl!2147484050:FStar.Pervasives.Native.Some_@a" [term_s] term_s
let n3010_x_Some__v_4051 : func_decl =
  symbol "decl!2147484051:FStar.Pervasives.Native.Some_@v" [term_s] term_s
let n3010_x_fst_4054 : func_decl =
  symbol "decl!2147484054:FStar.Pervasives.Native.fst" [universe_s; universe_s; term_s; term_s; term_s] term_s
let n3010_x_snd_4058 : func_decl =
  symbol "decl!2147484058:FStar.Pervasives.Native.snd" [universe_s; universe_s; term_s; term_s; term_s] term_s
let n3010_x_shift_subst_4121 : func_decl =
  symbol "decl!2147484121:FStar.Reflection.Typing.shift_subst" [term_s] term_s
let n3010_x_fuel_instrumented_4130 : func_decl =
  symbol "decl!2147484130:FStar.Reflection.Typing.subst_binder.fuel_instrumented" [fuel_s; term_s; term_s] term_s
let n3010_x_fuel_instrumented_4132 : func_decl =
  symbol "decl!2147484132:FStar.Reflection.Typing.subst_branches.fuel_instrumented" [fuel_s; term_s; term_s] term_s
let n3010_x_fuel_instrumented_4133 : func_decl =
  symbol "decl!2147484133:FStar.Reflection.Typing.subst_comp.fuel_instrumented" [fuel_s; term_s; term_s] term_s
let n3010_x_subst_ctx_uvar_and_subst_4134 : func_decl =
  symbol "decl!2147484134:FStar.Reflection.Typing.subst_ctx_uvar_and_subst" [term_s; term_s] term_s
let n3010_x_subst_db_4135 : func_decl =
  symbol "decl!2147484135:FStar.Reflection.Typing.subst_db" [term_s; term_s] term_s
let n3010_x_fuel_instrumented_4137 : func_decl =
  symbol "decl!2147484137:FStar.Reflection.Typing.subst_match_returns.fuel_instrumented" [fuel_s; term_s; term_s] term_s
let n3010_x_fuel_instrumented_4141 : func_decl =
  symbol "decl!2147484141:FStar.Reflection.Typing.subst_term.fuel_instrumented" [fuel_s; term_s; term_s] term_s
let n3010_x_fuel_instrumented_4142 : func_decl =
  symbol "decl!2147484142:FStar.Reflection.Typing.subst_terms.fuel_instrumented" [fuel_s; term_s; term_s] term_s
let n3010_x_subst_var_4143 : func_decl =
  symbol "decl!2147484143:FStar.Reflection.Typing.subst_var" [term_s; term_s] term_s
let n3010_x_term_4174 : func_decl =
  symbol "decl!2147484174:FStar.Stubs.Reflection.Types.term" [] term_s
let n3010_x_inspect_ln_4182 : func_decl =
  symbol "decl!2147484182:FStar.Stubs.Reflection.V2.Builtins.inspect_ln" [term_s] term_s
let n3010_x_pack_ln_4188 : func_decl =
  symbol "decl!2147484188:FStar.Stubs.Reflection.V2.Builtins.pack_ln" [term_s] term_s
let n3010_x_Tv_Abs_4257 : func_decl =
  symbol "decl!2147484257:FStar.Stubs.Reflection.V2.Data.Tv_Abs" [term_s; term_s] term_s
let n3010_x_Tv_Abs__body_4258 : func_decl =
  symbol "decl!2147484258:FStar.Stubs.Reflection.V2.Data.Tv_Abs_@body" [term_s] term_s
let n3010_x_Tv_Abs__bv_4259 : func_decl =
  symbol "decl!2147484259:FStar.Stubs.Reflection.V2.Data.Tv_Abs_@bv" [term_s] term_s
let n3010_x_Tv_App_4260 : func_decl =
  symbol "decl!2147484260:FStar.Stubs.Reflection.V2.Data.Tv_App" [term_s; term_s] term_s
let n3010_x_Tv_App__a_4261 : func_decl =
  symbol "decl!2147484261:FStar.Stubs.Reflection.V2.Data.Tv_App_@a" [term_s] term_s
let n3010_x_Tv_App__hd_4262 : func_decl =
  symbol "decl!2147484262:FStar.Stubs.Reflection.V2.Data.Tv_App_@hd" [term_s] term_s
let n3010_x_Tv_Arrow_4263 : func_decl =
  symbol "decl!2147484263:FStar.Stubs.Reflection.V2.Data.Tv_Arrow" [term_s; term_s] term_s
let n3010_x_Tv_Arrow__bv_4264 : func_decl =
  symbol "decl!2147484264:FStar.Stubs.Reflection.V2.Data.Tv_Arrow_@bv" [term_s] term_s
let n3010_x_Tv_Arrow__c_4265 : func_decl =
  symbol "decl!2147484265:FStar.Stubs.Reflection.V2.Data.Tv_Arrow_@c" [term_s] term_s
let n3010_x_Tv_AscribedC_4266 : func_decl =
  symbol "decl!2147484266:FStar.Stubs.Reflection.V2.Data.Tv_AscribedC" [term_s; term_s; term_s; term_s] term_s
let n3010_x_Tv_AscribedC__c_4267 : func_decl =
  symbol "decl!2147484267:FStar.Stubs.Reflection.V2.Data.Tv_AscribedC_@c" [term_s] term_s
let n3010_x_Tv_AscribedC__e_4268 : func_decl =
  symbol "decl!2147484268:FStar.Stubs.Reflection.V2.Data.Tv_AscribedC_@e" [term_s] term_s
let n3010_x_Tv_AscribedC__tac_4269 : func_decl =
  symbol "decl!2147484269:FStar.Stubs.Reflection.V2.Data.Tv_AscribedC_@tac" [term_s] term_s
let n3010_x_Tv_AscribedC__use_eq_4270 : func_decl =
  symbol "decl!2147484270:FStar.Stubs.Reflection.V2.Data.Tv_AscribedC_@use_eq" [term_s] term_s
let n3010_x_Tv_AscribedT_4271 : func_decl =
  symbol "decl!2147484271:FStar.Stubs.Reflection.V2.Data.Tv_AscribedT" [term_s; term_s; term_s; term_s] term_s
let n3010_x_Tv_AscribedT__e_4272 : func_decl =
  symbol "decl!2147484272:FStar.Stubs.Reflection.V2.Data.Tv_AscribedT_@e" [term_s] term_s
let n3010_x_Tv_AscribedT__t_4273 : func_decl =
  symbol "decl!2147484273:FStar.Stubs.Reflection.V2.Data.Tv_AscribedT_@t" [term_s] term_s
let n3010_x_Tv_AscribedT__tac_4274 : func_decl =
  symbol "decl!2147484274:FStar.Stubs.Reflection.V2.Data.Tv_AscribedT_@tac" [term_s] term_s
let n3010_x_Tv_AscribedT__use_eq_4275 : func_decl =
  symbol "decl!2147484275:FStar.Stubs.Reflection.V2.Data.Tv_AscribedT_@use_eq" [term_s] term_s
let n3010_x_Tv_BVar_4276 : func_decl =
  symbol "decl!2147484276:FStar.Stubs.Reflection.V2.Data.Tv_BVar" [term_s] term_s
let n3010_x_Tv_BVar__v_4277 : func_decl =
  symbol "decl!2147484277:FStar.Stubs.Reflection.V2.Data.Tv_BVar_@v" [term_s] term_s
let n3010_x_Tv_Let_4282 : func_decl =
  symbol "decl!2147484282:FStar.Stubs.Reflection.V2.Data.Tv_Let" [term_s; term_s; term_s; term_s; term_s] term_s
let n3010_x_Tv_Let__attrs_4283 : func_decl =
  symbol "decl!2147484283:FStar.Stubs.Reflection.V2.Data.Tv_Let_@attrs" [term_s] term_s
let n3010_x_Tv_Let__b_4284 : func_decl =
  symbol "decl!2147484284:FStar.Stubs.Reflection.V2.Data.Tv_Let_@b" [term_s] term_s
let n3010_x_Tv_Let__body_4285 : func_decl =
  symbol "decl!2147484285:FStar.Stubs.Reflection.V2.Data.Tv_Let_@body" [term_s] term_s
let n3010_x_Tv_Let__def_4286 : func_decl =
  symbol "decl!2147484286:FStar.Stubs.Reflection.V2.Data.Tv_Let_@def" [term_s] term_s
let n3010_x_Tv_Let__recf_4287 : func_decl =
  symbol "decl!2147484287:FStar.Stubs.Reflection.V2.Data.Tv_Let_@recf" [term_s] term_s
let n3010_x_Tv_Match_4288 : func_decl =
  symbol "decl!2147484288:FStar.Stubs.Reflection.V2.Data.Tv_Match" [term_s; term_s; term_s] term_s
let n3010_x_Tv_Match__brs_4289 : func_decl =
  symbol "decl!2147484289:FStar.Stubs.Reflection.V2.Data.Tv_Match_@brs" [term_s] term_s
let n3010_x_Tv_Match__ret_4290 : func_decl =
  symbol "decl!2147484290:FStar.Stubs.Reflection.V2.Data.Tv_Match_@ret" [term_s] term_s
let n3010_x_Tv_Match__scrutinee_4291 : func_decl =
  symbol "decl!2147484291:FStar.Stubs.Reflection.V2.Data.Tv_Match_@scrutinee" [term_s] term_s
let n3010_x_Tv_Refine_4292 : func_decl =
  symbol "decl!2147484292:FStar.Stubs.Reflection.V2.Data.Tv_Refine" [term_s; term_s] term_s
let n3010_x_Tv_Refine__b_4293 : func_decl =
  symbol "decl!2147484293:FStar.Stubs.Reflection.V2.Data.Tv_Refine_@b" [term_s] term_s
let n3010_x_Tv_Refine__ref_4294 : func_decl =
  symbol "decl!2147484294:FStar.Stubs.Reflection.V2.Data.Tv_Refine_@ref" [term_s] term_s
let n3010_x_Tv_Unknown_4300 : func_decl =
  symbol "decl!2147484300:FStar.Stubs.Reflection.V2.Data.Tv_Unknown" [] term_s
let n3010_x_Tv_Unsupp_4302 : func_decl =
  symbol "decl!2147484302:FStar.Stubs.Reflection.V2.Data.Tv_Unsupp" [] term_s
let n3010_x_Tv_Uvar_4304 : func_decl =
  symbol "decl!2147484304:FStar.Stubs.Reflection.V2.Data.Tv_Uvar" [term_s; term_s] term_s
let n3010_x_Tv_Uvar___0_4305 : func_decl =
  symbol "decl!2147484305:FStar.Stubs.Reflection.V2.Data.Tv_Uvar_@_0" [term_s] term_s
let n3010_x_Tv_Uvar___1_4306 : func_decl =
  symbol "decl!2147484306:FStar.Stubs.Reflection.V2.Data.Tv_Uvar_@_1" [term_s] term_s
let n3010_x_Tv_Var_4307 : func_decl =
  symbol "decl!2147484307:FStar.Stubs.Reflection.V2.Data.Tv_Var" [term_s] term_s
let n3010_x_Tv_Var__v_4308 : func_decl =
  symbol "decl!2147484308:FStar.Stubs.Reflection.V2.Data.Tv_Var_@v" [term_s] term_s
let n3010_x_aqualv_4333 : func_decl =
  symbol "decl!2147484333:FStar.Stubs.Reflection.V2.Data.aqualv" [] term_s
let n3010_x_match_returns_ascription_4351 : func_decl =
  symbol "decl!2147484351:FStar.Stubs.Syntax.Syntax.match_returns_ascription" [] term_s
let n3010_lhs : expr =
  (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])
    (native_num "499" 499)); (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Unsupp_4302
    []))]) (Var 1 term_s) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])]) (native_num "497" 497)); (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App
    n3010_x_Tv_Unknown_4300 []))]) (Var 1 term_s) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "422" 422)); (eq (App n3010_x_inspect_ln_4182
    [(Var 1 term_s)]) (App n3010_x_Tv_Var_4307 [(App n3010_x_Tv_Var__v_4308 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])])]))]) (App n3010_x_subst_var_4143 [(App n3010_x_Tv_Var__v_4308 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]) (ite_ (mk_and [(eq (App
    n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "427" 427));
    (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_BVar_4276 [(App
    n3010_x_Tv_BVar__v_4277 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App n3010_x_subst_db_4135
    [(App n3010_x_Tv_BVar__v_4277 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]) (ite_
    (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])
    (native_num "442" 442)); (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_App_4260
    [(App n3010_x_Tv_App__hd_4262 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_App__a_4261 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App n3010_x_pack_ln_4188
    [(App n3010_x_Tv_App_4260 [(App n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App
    n3010_x_Tv_App__hd_4262 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (App
    n3010_x_Mktuple2_4028 [(App n3010_x_U_zero_3801 []); (App n3010_x_U_zero_3801 []); (App n3010_x_term_4174
    []); (App n3010_x_aqualv_4333 []); (App n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App
    n3010_x_fst_4054 [(App n3010_x_U_zero_3801 []); (App n3010_x_U_zero_3801 []); (App n3010_x_term_4174 []);
    (App n3010_x_aqualv_4333 []); (App n3010_x_Tv_App__a_4261 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]); (Var 0 term_s)]); (App n3010_x_snd_4058 [(App n3010_x_U_zero_3801 []); (App
    n3010_x_U_zero_3801 []); (App n3010_x_term_4174 []); (App n3010_x_aqualv_4333 []); (App
    n3010_x_Tv_App__a_4261 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])])])])]) (ite_ (mk_and [(eq (App
    n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "447" 447));
    (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Abs_4257 [(App n3010_x_Tv_Abs__bv_4259
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_Tv_Abs__body_4258 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App n3010_x_pack_ln_4188 [(App n3010_x_Tv_Abs_4257
    [(App n3010_x_fuel_instrumented_4130 [(Var 2 fuel_s); (App n3010_x_Tv_Abs__bv_4259 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (App n3010_x_fuel_instrumented_4141 [(Var
    2 fuel_s); (App n3010_x_Tv_Abs__body_4258 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_shift_subst_4121 [(Var 0 term_s)])])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "452" 452)); (eq (App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Arrow_4263 [(App n3010_x_Tv_Arrow__bv_4264
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_Tv_Arrow__c_4265 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App n3010_x_pack_ln_4188 [(App n3010_x_Tv_Arrow_4263
    [(App n3010_x_fuel_instrumented_4130 [(Var 2 fuel_s); (App n3010_x_Tv_Arrow__bv_4264 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (App n3010_x_fuel_instrumented_4133 [(Var
    2 fuel_s); (App n3010_x_Tv_Arrow__c_4265 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_shift_subst_4121 [(Var 0 term_s)])])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "462" 462)); (eq (App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Refine_4292 [(App n3010_x_Tv_Refine__b_4293
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_Tv_Refine__ref_4294 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App n3010_x_pack_ln_4188 [(App n3010_x_Tv_Refine_4292
    [(App n3010_x_fuel_instrumented_4130 [(Var 2 fuel_s); (App n3010_x_Tv_Refine__b_4293 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (App n3010_x_fuel_instrumented_4141 [(Var
    2 fuel_s); (App n3010_x_Tv_Refine__ref_4294 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_shift_subst_4121 [(Var 0 term_s)])])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "472" 472)); (eq (App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Uvar_4304 [(App n3010_x_Tv_Uvar___0_4305 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_Tv_Uvar___1_4306 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])])]))]) (App n3010_x_pack_ln_4188 [(App n3010_x_Tv_Uvar_4304 [(App
    n3010_x_Tv_Uvar___0_4305 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_subst_ctx_uvar_and_subst_4134 [(App n3010_x_Tv_Uvar___1_4306 [(App n3010_x_inspect_ln_4182 [(Var
    1 term_s)])]); (Var 0 term_s)])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "477" 477)); (eq (App n3010_x_inspect_ln_4182
    [(Var 1 term_s)]) (App n3010_x_Tv_Let_4282 [(App n3010_x_Tv_Let__recf_4287 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])]); (App n3010_x_Tv_Let__attrs_4283 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]);
    (App n3010_x_Tv_Let__b_4284 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_Let__def_4286 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_Let__body_4285 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App
    n3010_x_pack_ln_4188 [(App n3010_x_Tv_Let_4282 [(App n3010_x_Tv_Let__recf_4287 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_fuel_instrumented_4142 [(Var 2 fuel_s); (App
    n3010_x_Tv_Let__attrs_4283 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (App
    n3010_x_fuel_instrumented_4130 [(Var 2 fuel_s); (App n3010_x_Tv_Let__b_4284 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])]); (Var 0 term_s)]); (ite_ (eq (App n3010_x_Tv_Let__recf_4287 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_BoxBool_3940 [R.true_expr])) (App
    n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App n3010_x_Tv_Let__def_4286 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_shift_subst_4121 [(Var 0 term_s)])]) (App
    n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App n3010_x_Tv_Let__def_4286 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)])); (App n3010_x_fuel_instrumented_4141 [(Var
    2 fuel_s); (App n3010_x_Tv_Let__body_4285 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_shift_subst_4121 [(Var 0 term_s)])])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "482" 482)); (eq (App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Match_4288 [(App
    n3010_x_Tv_Match__scrutinee_4291 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_Match__brs_4289 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App
    n3010_x_pack_ln_4188 [(App n3010_x_Tv_Match_4288 [(App n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s);
    (App n3010_x_Tv_Match__scrutinee_4291 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0
    term_s)]); (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_Tv_Match__ret_4290 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]) (native_num "108" 108)); (eq (App
    n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_None_4045 [(App
    n3010_x_None__0_4046 [(App n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]); (App n3010_x_None__a_4047 [(App n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])])])]))]) (App n3010_x_None_4045 [(App n3010_x_U_zero_3801 []); (App
    n3010_x_match_returns_ascription_4351 [])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App
    n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]) (native_num "113" 113));
    (eq (App n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App
    n3010_x_Some_4048 [(App n3010_x_Some__0_4049 [(App n3010_x_Tv_Match__ret_4290 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App n3010_x_Some__a_4050 [(App n3010_x_Tv_Match__ret_4290
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])])]))]) (App
    n3010_x_Some_4048 [(App n3010_x_U_zero_3801 []); (App n3010_x_match_returns_ascription_4351 []); (App
    n3010_x_fuel_instrumented_4137 [(Var 2 fuel_s); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (Var 0 term_s)])]) (App
    n3010_x_Tm_unit_3922 []))); (App n3010_x_fuel_instrumented_4132 [(Var 2 fuel_s); (App
    n3010_x_Tv_Match__brs_4289 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)])])]) (ite_
    (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])
    (native_num "487" 487)); (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App
    n3010_x_Tv_AscribedT_4271 [(App n3010_x_Tv_AscribedT__e_4272 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])]); (App n3010_x_Tv_AscribedT__t_4273 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_AscribedT__use_eq_4275 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App
    n3010_x_pack_ln_4188 [(App n3010_x_Tv_AscribedT_4271 [(App n3010_x_fuel_instrumented_4141 [(Var 2
    fuel_s); (App n3010_x_Tv_AscribedT__e_4272 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0
    term_s)]); (App n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App n3010_x_Tv_AscribedT__t_4273 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (ite_ (mk_and [(eq (App
    n3010_x_Term_constr_id_3830 [(App n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]) (native_num "108" 108)); (eq (App n3010_x_Tv_AscribedT__tac_4274 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_None_4045 [(App n3010_x_None__0_4046 [(App
    n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App
    n3010_x_None__a_4047 [(App n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])])]))]) (App n3010_x_None_4045 [(App n3010_x_U_zero_3801 []); (App n3010_x_term_4174 [])])
    (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_Tv_AscribedT__tac_4274 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]) (native_num "113" 113)); (eq (App
    n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_Some_4048
    [(App n3010_x_Some__0_4049 [(App n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]); (App n3010_x_Some__a_4050 [(App n3010_x_Tv_AscribedT__tac_4274 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])])]))]) (App
    n3010_x_Some_4048 [(App n3010_x_U_zero_3801 []); (App n3010_x_term_4174 []); (App
    n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (Var 0 term_s)])])
    (App n3010_x_Tm_unit_3922 []))); (App n3010_x_Tv_AscribedT__use_eq_4275 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])]) (native_num "492" 492)); (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App
    n3010_x_Tv_AscribedC_4266 [(App n3010_x_Tv_AscribedC__e_4268 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])]); (App n3010_x_Tv_AscribedC__c_4267 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_AscribedC__use_eq_4270 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App
    n3010_x_pack_ln_4188 [(App n3010_x_Tv_AscribedC_4266 [(App n3010_x_fuel_instrumented_4141 [(Var 2
    fuel_s); (App n3010_x_Tv_AscribedC__e_4268 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0
    term_s)]); (App n3010_x_fuel_instrumented_4133 [(Var 2 fuel_s); (App n3010_x_Tv_AscribedC__c_4267 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (ite_ (mk_and [(eq (App
    n3010_x_Term_constr_id_3830 [(App n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]) (native_num "108" 108)); (eq (App n3010_x_Tv_AscribedC__tac_4269 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_None_4045 [(App n3010_x_None__0_4046 [(App
    n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App
    n3010_x_None__a_4047 [(App n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])])]))]) (App n3010_x_None_4045 [(App n3010_x_U_zero_3801 []); (App n3010_x_term_4174 [])])
    (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_Tv_AscribedC__tac_4269 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]) (native_num "113" 113)); (eq (App
    n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_Some_4048
    [(App n3010_x_Some__0_4049 [(App n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]); (App n3010_x_Some__a_4050 [(App n3010_x_Tv_AscribedC__tac_4269 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])])]))]) (App
    n3010_x_Some_4048 [(App n3010_x_U_zero_3801 []); (App n3010_x_term_4174 []); (App
    n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (Var 0 term_s)])])
    (App n3010_x_Tm_unit_3922 []))); (App n3010_x_Tv_AscribedC__use_eq_4270 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])])])]) (App n3010_x_Tm_unit_3922 []))))))))))))))
let n3010_rhs : expr =
  (ite_ (mk_or [(mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])]) (native_num "499" 499)); (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App
    n3010_x_Tv_Unsupp_4302 []))]); (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "497" 497)); (eq (App n3010_x_inspect_ln_4182
    [(Var 1 term_s)]) (App n3010_x_Tv_Unknown_4300 []))])]) (Var 1 term_s) (ite_ (mk_and [(eq (App
    n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "422" 422));
    (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Var_4307 [(App n3010_x_Tv_Var__v_4308
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App n3010_x_subst_var_4143 [(App
    n3010_x_Tv_Var__v_4308 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]) (ite_ (mk_and
    [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "427"
    427)); (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_BVar_4276 [(App
    n3010_x_Tv_BVar__v_4277 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App n3010_x_subst_db_4135
    [(App n3010_x_Tv_BVar__v_4277 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]) (ite_
    (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])
    (native_num "442" 442)); (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_App_4260
    [(App n3010_x_Tv_App__hd_4262 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_App__a_4261 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App n3010_x_pack_ln_4188
    [(App n3010_x_Tv_App_4260 [(App n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App
    n3010_x_Tv_App__hd_4262 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (App
    n3010_x_Mktuple2_4028 [(App n3010_x_U_zero_3801 []); (App n3010_x_U_zero_3801 []); (App n3010_x_term_4174
    []); (App n3010_x_aqualv_4333 []); (App n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App
    n3010_x_fst_4054 [(App n3010_x_U_zero_3801 []); (App n3010_x_U_zero_3801 []); (App n3010_x_term_4174 []);
    (App n3010_x_aqualv_4333 []); (App n3010_x_Tv_App__a_4261 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]); (Var 0 term_s)]); (App n3010_x_snd_4058 [(App n3010_x_U_zero_3801 []); (App
    n3010_x_U_zero_3801 []); (App n3010_x_term_4174 []); (App n3010_x_aqualv_4333 []); (App
    n3010_x_Tv_App__a_4261 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])])])])]) (ite_ (mk_and [(eq (App
    n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "447" 447));
    (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Abs_4257 [(App n3010_x_Tv_Abs__bv_4259
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_Tv_Abs__body_4258 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App n3010_x_pack_ln_4188 [(App n3010_x_Tv_Abs_4257
    [(App n3010_x_fuel_instrumented_4130 [(Var 2 fuel_s); (App n3010_x_Tv_Abs__bv_4259 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (App n3010_x_fuel_instrumented_4141 [(Var
    2 fuel_s); (App n3010_x_Tv_Abs__body_4258 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_shift_subst_4121 [(Var 0 term_s)])])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "452" 452)); (eq (App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Arrow_4263 [(App n3010_x_Tv_Arrow__bv_4264
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_Tv_Arrow__c_4265 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App n3010_x_pack_ln_4188 [(App n3010_x_Tv_Arrow_4263
    [(App n3010_x_fuel_instrumented_4130 [(Var 2 fuel_s); (App n3010_x_Tv_Arrow__bv_4264 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (App n3010_x_fuel_instrumented_4133 [(Var
    2 fuel_s); (App n3010_x_Tv_Arrow__c_4265 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_shift_subst_4121 [(Var 0 term_s)])])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "462" 462)); (eq (App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Refine_4292 [(App n3010_x_Tv_Refine__b_4293
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_Tv_Refine__ref_4294 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App n3010_x_pack_ln_4188 [(App n3010_x_Tv_Refine_4292
    [(App n3010_x_fuel_instrumented_4130 [(Var 2 fuel_s); (App n3010_x_Tv_Refine__b_4293 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (App n3010_x_fuel_instrumented_4141 [(Var
    2 fuel_s); (App n3010_x_Tv_Refine__ref_4294 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_shift_subst_4121 [(Var 0 term_s)])])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "472" 472)); (eq (App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Uvar_4304 [(App n3010_x_Tv_Uvar___0_4305 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_Tv_Uvar___1_4306 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])])]))]) (App n3010_x_pack_ln_4188 [(App n3010_x_Tv_Uvar_4304 [(App
    n3010_x_Tv_Uvar___0_4305 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_subst_ctx_uvar_and_subst_4134 [(App n3010_x_Tv_Uvar___1_4306 [(App n3010_x_inspect_ln_4182 [(Var
    1 term_s)])]); (Var 0 term_s)])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "477" 477)); (eq (App n3010_x_inspect_ln_4182
    [(Var 1 term_s)]) (App n3010_x_Tv_Let_4282 [(App n3010_x_Tv_Let__recf_4287 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])]); (App n3010_x_Tv_Let__attrs_4283 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]);
    (App n3010_x_Tv_Let__b_4284 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_Let__def_4286 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_Let__body_4285 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App
    n3010_x_pack_ln_4188 [(App n3010_x_Tv_Let_4282 [(App n3010_x_Tv_Let__recf_4287 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_fuel_instrumented_4142 [(Var 2 fuel_s); (App
    n3010_x_Tv_Let__attrs_4283 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (App
    n3010_x_fuel_instrumented_4130 [(Var 2 fuel_s); (App n3010_x_Tv_Let__b_4284 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])]); (Var 0 term_s)]); (ite_ (eq (App n3010_x_Tv_Let__recf_4287 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_BoxBool_3940 [R.true_expr])) (App
    n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App n3010_x_Tv_Let__def_4286 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App n3010_x_shift_subst_4121 [(Var 0 term_s)])]) (App
    n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App n3010_x_Tv_Let__def_4286 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)])); (App n3010_x_fuel_instrumented_4141 [(Var
    2 fuel_s); (App n3010_x_Tv_Let__body_4285 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_shift_subst_4121 [(Var 0 term_s)])])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (native_num "482" 482)); (eq (App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App n3010_x_Tv_Match_4288 [(App
    n3010_x_Tv_Match__scrutinee_4291 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_Match__brs_4289 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App
    n3010_x_pack_ln_4188 [(App n3010_x_Tv_Match_4288 [(App n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s);
    (App n3010_x_Tv_Match__scrutinee_4291 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0
    term_s)]); (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_Tv_Match__ret_4290 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]) (native_num "108" 108)); (eq (App
    n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_None_4045 [(App
    n3010_x_None__0_4046 [(App n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]); (App n3010_x_None__a_4047 [(App n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])])])]))]) (App n3010_x_None_4045 [(App n3010_x_U_zero_3801 []); (App
    n3010_x_match_returns_ascription_4351 [])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App
    n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]) (native_num "113" 113));
    (eq (App n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App
    n3010_x_Some_4048 [(App n3010_x_Some__0_4049 [(App n3010_x_Tv_Match__ret_4290 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App n3010_x_Some__a_4050 [(App n3010_x_Tv_Match__ret_4290
    [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])])]))]) (App
    n3010_x_Some_4048 [(App n3010_x_U_zero_3801 []); (App n3010_x_match_returns_ascription_4351 []); (App
    n3010_x_fuel_instrumented_4137 [(Var 2 fuel_s); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_Match__ret_4290 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (Var 0 term_s)])]) (App
    n3010_x_Tm_unit_3922 []))); (App n3010_x_fuel_instrumented_4132 [(Var 2 fuel_s); (App
    n3010_x_Tv_Match__brs_4289 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)])])]) (ite_
    (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])
    (native_num "487" 487)); (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App
    n3010_x_Tv_AscribedT_4271 [(App n3010_x_Tv_AscribedT__e_4272 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])]); (App n3010_x_Tv_AscribedT__t_4273 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_AscribedT__use_eq_4275 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App
    n3010_x_pack_ln_4188 [(App n3010_x_Tv_AscribedT_4271 [(App n3010_x_fuel_instrumented_4141 [(Var 2
    fuel_s); (App n3010_x_Tv_AscribedT__e_4272 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0
    term_s)]); (App n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App n3010_x_Tv_AscribedT__t_4273 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (ite_ (mk_and [(eq (App
    n3010_x_Term_constr_id_3830 [(App n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]) (native_num "108" 108)); (eq (App n3010_x_Tv_AscribedT__tac_4274 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_None_4045 [(App n3010_x_None__0_4046 [(App
    n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App
    n3010_x_None__a_4047 [(App n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])])]))]) (App n3010_x_None_4045 [(App n3010_x_U_zero_3801 []); (App n3010_x_term_4174 [])])
    (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_Tv_AscribedT__tac_4274 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]) (native_num "113" 113)); (eq (App
    n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_Some_4048
    [(App n3010_x_Some__0_4049 [(App n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]); (App n3010_x_Some__a_4050 [(App n3010_x_Tv_AscribedT__tac_4274 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])])]))]) (App
    n3010_x_Some_4048 [(App n3010_x_U_zero_3801 []); (App n3010_x_term_4174 []); (App
    n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_AscribedT__tac_4274 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (Var 0 term_s)])])
    (App n3010_x_Tm_unit_3922 []))); (App n3010_x_Tv_AscribedT__use_eq_4275 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])])])]) (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])]) (native_num "492" 492)); (eq (App n3010_x_inspect_ln_4182 [(Var 1 term_s)]) (App
    n3010_x_Tv_AscribedC_4266 [(App n3010_x_Tv_AscribedC__e_4268 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])]); (App n3010_x_Tv_AscribedC__c_4267 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (App
    n3010_x_Tv_AscribedC__use_eq_4270 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]))]) (App
    n3010_x_pack_ln_4188 [(App n3010_x_Tv_AscribedC_4266 [(App n3010_x_fuel_instrumented_4141 [(Var 2
    fuel_s); (App n3010_x_Tv_AscribedC__e_4268 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0
    term_s)]); (App n3010_x_fuel_instrumented_4133 [(Var 2 fuel_s); (App n3010_x_Tv_AscribedC__c_4267 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]); (Var 0 term_s)]); (ite_ (mk_and [(eq (App
    n3010_x_Term_constr_id_3830 [(App n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]) (native_num "108" 108)); (eq (App n3010_x_Tv_AscribedC__tac_4269 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_None_4045 [(App n3010_x_None__0_4046 [(App
    n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App
    n3010_x_None__a_4047 [(App n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])])]))]) (App n3010_x_None_4045 [(App n3010_x_U_zero_3801 []); (App n3010_x_term_4174 [])])
    (ite_ (mk_and [(eq (App n3010_x_Term_constr_id_3830 [(App n3010_x_Tv_AscribedC__tac_4269 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]) (native_num "113" 113)); (eq (App
    n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])]) (App n3010_x_Some_4048
    [(App n3010_x_Some__0_4049 [(App n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1
    term_s)])])]); (App n3010_x_Some__a_4050 [(App n3010_x_Tv_AscribedC__tac_4269 [(App
    n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])])]))]) (App
    n3010_x_Some_4048 [(App n3010_x_U_zero_3801 []); (App n3010_x_term_4174 []); (App
    n3010_x_fuel_instrumented_4141 [(Var 2 fuel_s); (App n3010_x_Some__v_4051 [(App
    n3010_x_Tv_AscribedC__tac_4269 [(App n3010_x_inspect_ln_4182 [(Var 1 term_s)])])]); (Var 0 term_s)])])
    (App n3010_x_Tm_unit_3922 []))); (App n3010_x_Tv_AscribedC__use_eq_4270 [(App n3010_x_inspect_ln_4182
    [(Var 1 term_s)])])])]) (App n3010_x_Tm_unit_3922 [])))))))))))))

(* The certificate of a leaf `l ~ r` read at the body scope of bs: the leaf,
   the congruence (= h l) ~ (= h r) and the quant-intro over bs (the shape
   of the captured n447 certificate, entry for entry). *)
let ite_cert (bs:list sort) (h l r:expr) : U.binder_certificate =
  cert [be "rewrite" (eq l r) [];
        be "monotonicity" (eq (eq h l) (eq h r)) [0];
        bq "quant-intro" bs (eq (forall_ bs (eq h l)) (forall_ bs (eq h r))) [1]] 2

let ite_replays (bs:list sort) (h l r:expr) : bool =
  replays (ite_cert bs h l r) (forall_ bs (eq h l)) (forall_ bs (eq h r))

let ite_pending (bs:list sort) (h l r:expr) : bool =
  pending (ite_cert bs h l r) (forall_ bs (eq h l)) (forall_ bs (eq h r))

let base1_bs : list sort = [fuel_s; term_s; term_s]
let n447_bs : list sort = [universe_s; term_s; term_s; term_s; term_s; term_s; term_s]
let n447_half_frac : func_decl =
  symbol "decl!2147486341:Pulse.Lib.FractionalAnchoredPreorder.half_frac" n447_bs term_s
let n447_h : expr =
  App n447_half_frac [Var 6 universe_s; Var 5 term_s; Var 4 term_s; Var 3 term_s; Var 2 term_s; Var 1 term_s;
                      Var 0 term_s]
let n447_cert : U.binder_certificate = ite_cert n447_bs n447_h n447_lhs n447_rhs
let n447_root_l : expr = forall_ n447_bs (eq n447_h n447_lhs)
let n447_root_r : expr = forall_ n447_bs (eq n447_h n447_rhs)

let a7_captured_pending_at_9af ()
  : Lemma (get_sort n3021_lhs == term_s /\ get_sort n3010_lhs == term_s /\ get_sort n447_lhs == term_s /\
           not (Z3SortedArithmetic.equivalent n3021_lhs n3021_rhs) /\
           not (Z3SortedArithmetic.equivalent n3010_lhs n3010_rhs) /\
           not (Z3SortedArithmetic.equivalent n447_lhs n447_rhs)) =
  assert_norm (get_sort n3021_lhs == term_s /\ get_sort n3010_lhs == term_s /\ get_sort n447_lhs == term_s);
  assert_norm (not (Z3SortedArithmetic.equivalent n3021_lhs n3021_rhs));
  assert_norm (not (Z3SortedArithmetic.equivalent n3010_lhs n3010_rhs));
  assert_norm (not (Z3SortedArithmetic.equivalent n447_lhs n447_rhs))

let a7_captured_n3021 ()
  : Lemma (NR.ite_rewritten n3021_lhs n3021_rhs /\ NR.rewrite_ok n3021_lhs n3021_rhs /\
           ite_replays base1_bs (Var 0 term_s) n3021_lhs n3021_rhs) =
  assert_norm (NR.ite_rewritten n3021_lhs n3021_rhs /\ NR.rewrite_ok n3021_lhs n3021_rhs);
  assert_norm (ite_replays base1_bs (Var 0 term_s) n3021_lhs n3021_rhs)

let a7_captured_n3010 ()
  : Lemma (NR.ite_rewritten n3010_lhs n3010_rhs /\ NR.rewrite_ok n3010_lhs n3010_rhs /\
           ite_replays base1_bs (Var 0 term_s) n3010_lhs n3010_rhs) =
  assert_norm (NR.ite_rewritten n3010_lhs n3010_rhs /\ NR.rewrite_ok n3010_lhs n3010_rhs);
  assert_norm (ite_replays base1_bs (Var 0 term_s) n3010_lhs n3010_rhs)

let a7_captured_n447 ()
  : Lemma (NR.ite_rewritten n447_lhs n447_rhs /\ NR.rewrite_ok n447_lhs n447_rhs /\
           replays n447_cert n447_root_l n447_root_r) =
  assert_norm (NR.ite_rewritten n447_lhs n447_rhs /\ NR.rewrite_ok n447_lhs n447_rhs);
  assert_norm (replays n447_cert n447_root_l n447_root_r)

(* The captured equations in EVERY Sorted model, at EVERY typed environment
   of their scopes (NR.lemma_rewrite_at). *)
let a7_captured_valid (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (rho:V.environment base (S.signature s) [term_s; term_s; fuel_s])
                      (rho':V.environment base (S.signature s) [term_s; term_s; term_s; term_s; term_s; term_s; universe_s])
  : Lemma (NR.same_at s bc eq other [term_s; term_s; fuel_s] rho n3021_lhs n3021_rhs /\
           NR.same_at s bc eq other [term_s; term_s; fuel_s] rho n3010_lhs n3010_rhs /\
           NR.same_at s bc eq other [term_s; term_s; term_s; term_s; term_s; term_s; universe_s] rho' n447_lhs n447_rhs) =
  a7_captured_n3021 (); a7_captured_n3010 (); a7_captured_n447 ();
  assert_norm (D.scoped [term_s; term_s; fuel_s] n3021_lhs /\ D.scoped [term_s; term_s; fuel_s] n3021_rhs);
  assert_norm (D.scoped [term_s; term_s; fuel_s] n3010_lhs /\ D.scoped [term_s; term_s; fuel_s] n3010_rhs);
  assert_norm (D.scoped [term_s; term_s; term_s; term_s; term_s; term_s; universe_s] n447_lhs /\
               D.scoped [term_s; term_s; term_s; term_s; term_s; term_s; universe_s] n447_rhs);
  NR.lemma_rewrite_at s bc eq other [term_s; term_s; fuel_s] rho n3021_lhs n3021_rhs;
  NR.lemma_rewrite_at s bc eq other [term_s; term_s; fuel_s] rho n3010_lhs n3010_rhs;
  NR.lemma_rewrite_at s bc eq other [term_s; term_s; term_s; term_s; term_s; term_s; universe_s] rho' n447_lhs n447_rhs

(* The Real boundary: the n447 leaf with the branches of its merged side
   swapped (the Real numeral still inside) is refused by every disjunct of
   the rewrite check and its certificate is pending; its acceptance above
   read no Real law, and its refusal here reads none either. *)
let n447_swapped_rhs : expr =
  match n447_rhs with App f [c; x; y] -> App f [c; y; x] | e -> e

let a7_real_boundary_mutant ()
  : Lemma (not (NR.rewrite_ok n447_lhs n447_swapped_rhs) /\
           pending (ite_cert n447_bs n447_h n447_lhs n447_swapped_rhs)
                   n447_root_l (forall_ n447_bs (eq n447_h n447_swapped_rhs))) =
  assert_norm (not (NR.rewrite_ok n447_lhs n447_swapped_rhs));
  assert_norm (pending (ite_cert n447_bs n447_h n447_lhs n447_swapped_rhs)
                       n447_root_l (forall_ n447_bs (eq n447_h n447_swapped_rhs)))

(* Each law at every result sort, at the scope [Term] (c1 reads the
   binder): Bool, Int, Real (opaque values: Real numerals), the
   uninterpreted Term, the datatype Box of Z3SortedProofTests and an array
   sort; the negated condition in both orientations, the then merge, and
   the else merge by a binary `and`, with c1 flattened, with c1 and c2
   flattened (the n447 shape), and by a binary `and` over a conjunction. *)
let ic1 : expr = p_ t0
let ic2 : expr = c_ "c2"
let ic3 : expr = c_ "c3"
let ic4 : expr = c_ "c4"

let ite_laws (x y:expr) : list (expr & expr) = [
  ite_ (neg ic1) x y, ite_ ic1 y x;
  ite_ ic1 x y, ite_ (neg ic1) y x;
  ite_ ic1 x (ite_ ic2 x y), ite_ (mk_or [ic1; ic2]) x y;
  ite_ ic1 (ite_ ic2 x y) y, ite_ (mk_and [ic1; ic2]) x y;
  ite_ (mk_and [ic1; ic3]) (ite_ ic2 x y) y, ite_ (mk_and [ic1; ic3; ic2]) x y;
  ite_ (mk_and [ic1; ic3]) (ite_ (mk_and [ic2; ic4]) x y) y, ite_ (mk_and [ic1; ic3; ic2; ic4]) x y;
  ite_ (mk_and [ic1; ic3]) (ite_ ic2 x y) y, ite_ (mk_and [mk_and [ic1; ic3]; ic2]) x y]

let arr_s : sort = ArraySort [integer] term

let ite_branches : list (expr & expr) = [
  g_ "g1", g_ "g2";
  num 1, num 2;
  real_num "1.0" 1, real_num "2.0" 2;
  t0, App (symbol "a" [] term) [];
  App PT.empty [], App PT.pair [num 1; R.true_expr];
  App (symbol "arr1" [] arr_s) [], App (symbol "arr2" [] arr_s) []]

let ite_cases : list (expr & expr) = L.flatten (L.map (fun (xy:expr & expr) -> ite_laws (fst xy) (snd xy)) ite_branches)

let ite_h (l:expr) : expr = App (symbol "h" [] (get_sort l)) []

let a7_ok (lr:expr & expr) : bool =
  NR.ite_rewritten (fst lr) (snd lr) && NR.rewrite_ok (fst lr) (snd lr) &&
  ite_replays [term] (ite_h (fst lr)) (fst lr) (snd lr)

let a7_every_sort ()
  : Lemma (L.length ite_cases == 42 /\ L.for_all a7_ok ite_cases /\ L.for_all scoped_pair ite_cases) =
  assert_norm (L.length ite_cases == 42);
  assert_norm (L.for_all a7_ok ite_cases);
  assert_norm (L.for_all scoped_pair ite_cases)

(* ... and their equations in EVERY Sorted model, at EVERY typed
   environment of [Term] (NR.lemma_ite_rewritten_at). *)
let a7_valid (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
             (rho:V.environment base (S.signature s) [term])
  : Lemma (forall (lr:expr & expr). L.memP lr ite_cases ==> NR.same_at s bc eq other [term] rho (fst lr) (snd lr)) =
  a7_every_sort ();
  let at (lr:expr & expr)
    : Lemma (requires L.memP lr ite_cases) (ensures NR.same_at s bc eq other [term] rho (fst lr) (snd lr)) =
    lemma_for_all_memP a7_ok ite_cases lr;
    lemma_for_all_memP scoped_pair ite_cases lr;
    NR.lemma_ite_rewritten_at s bc eq other [term] rho (fst lr) (snd lr) in
  FStar.Classical.forall_intro (FStar.Classical.move_requires at)

(* Nested binders: the negated-condition leaf (ite (not (Q x y)) y x) =
   (ite (Q x y) x y) at the inner scope [Term; Term] (y = Var 0, x = Var 1)
   under two nested quant-intros replays; reading Q's arguments one binder
   off (Q y x) on the right is refused and pending. *)
let nb_l : expr = ite_ (neg (q_ t1 t0)) t0 t1
let nb_r : expr = ite_ (q_ t1 t0) t1 t0
let nb_shifted : expr = ite_ (q_ t0 t1) t1 t0
let nb_h : expr = App (symbol "h" [] term) []
let nested_cert (l r:expr) : U.binder_certificate =
  cert [be "rewrite" (eq l r) [];
        be "monotonicity" (eq (eq nb_h l) (eq nb_h r)) [0];
        bq "quant-intro" [term] (eq (forall_ [term] (eq nb_h l)) (forall_ [term] (eq nb_h r))) [1];
        bq "quant-intro" [term] (eq (forall_ [term] (forall_ [term] (eq nb_h l)))
                                    (forall_ [term] (forall_ [term] (eq nb_h r)))) [2]] 3

let a7_nested_binders ()
  : Lemma (replays (nested_cert nb_l nb_r) (forall_ [term] (forall_ [term] (eq nb_h nb_l)))
                                           (forall_ [term] (forall_ [term] (eq nb_h nb_r))) /\
           not (NR.rewrite_ok nb_l nb_shifted) /\
           pending (nested_cert nb_l nb_shifted) (forall_ [term] (forall_ [term] (eq nb_h nb_l)))
                                                 (forall_ [term] (forall_ [term] (eq nb_h nb_shifted)))) =
  assert_norm (replays (nested_cert nb_l nb_r) (forall_ [term] (forall_ [term] (eq nb_h nb_l)))
                                               (forall_ [term] (forall_ [term] (eq nb_h nb_r))));
  assert_norm (not (NR.rewrite_ok nb_l nb_shifted));
  assert_norm (pending (nested_cert nb_l nb_shifted) (forall_ [term] (forall_ [term] (eq nb_h nb_l)))
                                                     (forall_ [term] (forall_ [term] (eq nb_h nb_shifted))))

(* Binder order: the negated-condition leaf over x:Int, t:Term (body scope
   [Term; Int]: Var 0 is t, Var 1 is x) replays under the quant-intro over
   [Int; Term]; under the reversed list [Term; Int] the same body is not
   typed (Var 1 would be the Term) and the certificate is pending. *)
let rb_cond : expr = gt (Var 1 integer) (num 0)
let rb_a : expr = App (symbol "a" [] term) []
let rb_l : expr = ite_ (neg rb_cond) t0 rb_a
let rb_r : expr = ite_ rb_cond rb_a t0

let a7_binder_order ()
  : Lemma (ite_replays [integer; term] (ite_h rb_l) rb_l rb_r /\ ite_pending [term; integer] (ite_h rb_l) rb_l rb_r) =
  assert_norm (ite_replays [integer; term] (ite_h rb_l) rb_l rb_r);
  assert_norm (ite_pending [term; integer] (ite_h rb_l) rb_l rb_r)

(* The depth admission of the ITE laws is the regrouping's `NR.shallow`
   (B15 normalizes its 4096-level boundary); the deep and shared guards of
   the ITE laws run natively on both backends (test_native_bridge.ml
   `sorted_quant_intro_ite_laws`, Z3CherryTests `qi_ite_scale`). *)

(* B16 ITE law mutants over two Term binders (x = Var 0, y = Var 1) and
   closed Boolean atoms c1, c2, c3, each refused by the whole rewrite check
   and pending as a certificate: the merged branches swapped, the negation
   dropped (opposite guard), `and` in place of `or` and `or` in place of
   `and`, xor (another canonical operator), a counterfeit `or` and a
   counterfeit `not` (same name and signature, no interpretation), a
   dropped conjunct of a flattened `and`, a branch reading the other
   binder (capture), a counterfeit `if` on both sides, on one side, and as
   the nested ite; all well typed (opposite-value counter-models at an
   environment of [Term; Term] are D10 of Z3QuantIntroCounterModelTests).
   Finally a nested ite at ANOTHER sort is ill typed: refused by the law
   (another declaration) and by the scope guard. *)
let mc1 : expr = c_ "c1"
let mc2 : expr = c_ "c2"
let mc3 : expr = c_ "c3"
let fake_not : func_decl = symbol "not" [bool_sort] bool_sort
let twin_if : func_decl = symbol "if" [bool_sort; term; term] term
let term2 : sort = BaseSort "Term2"

let b16_swapped : expr & expr = ite_ mc1 t0 (ite_ mc2 t0 t1), ite_ (mk_or [mc1; mc2]) t1 t0
let b16_guard : expr & expr = ite_ (neg mc1) t0 t1, ite_ mc1 t0 t1
let b16_then_and : expr & expr = ite_ mc1 t0 (ite_ mc2 t0 t1), ite_ (mk_and [mc1; mc2]) t0 t1
let b16_else_or : expr & expr = ite_ mc1 (ite_ mc2 t0 t1) t1, ite_ (mk_or [mc1; mc2]) t0 t1
let b16_xor : expr & expr = ite_ mc1 t0 (ite_ mc2 t0 t1), ite_ (App xor_d [mc1; mc2]) t0 t1
let b16_twin_or : expr & expr = ite_ mc1 t0 (ite_ mc2 t0 t1), ite_ (App fake_or [mc1; mc2]) t0 t1
let b16_twin_not : expr & expr = ite_ (App fake_not [mc1]) t0 t1, ite_ mc1 t1 t0
let b16_dropped : expr & expr = ite_ (mk_and [mc1; mc3]) (ite_ mc2 t0 t1) t1, ite_ (mk_and [mc1; mc2]) t0 t1
let b16_capture : expr & expr = ite_ (neg mc1) t0 t1, ite_ mc1 t1 t1
let b16_twin_if : expr & expr = App twin_if [neg mc1; t0; t1], App twin_if [mc1; t1; t0]
let b16_mixed_if : expr & expr = ite_ (neg mc1) t0 t1, App twin_if [mc1; t1; t0]
let b16_inner_twin : expr & expr = ite_ mc1 t0 (App twin_if [mc2; t0; t1]), ite_ (mk_or [mc1; mc2]) t0 t1
let b16_inner_sort : expr & expr =
  ite_ mc1 t0 (App (T.ite_decl term2) [mc2; t0; t1]), ite_ (mk_or [mc1; mc2]) t0 t1

let b16_mutants : list (expr & expr) = [
  b16_swapped; b16_guard; b16_then_and; b16_else_or; b16_xor; b16_twin_or; b16_twin_not; b16_dropped;
  b16_capture; b16_twin_if; b16_mixed_if; b16_inner_twin]

let scope2 : list sort = [term; term]

let ite_refused (lr:expr & expr) : bool =
  not (NR.ite_rewritten (fst lr) (snd lr)) && not (NR.rewrite_ok (fst lr) (snd lr)) &&
  ite_pending scope2 nb_h (fst lr) (snd lr)

let scoped2 (lr:expr & expr) : bool = D.scoped scope2 (fst lr) && D.scoped scope2 (snd lr)

let b16_ite_mutants ()
  : Lemma (L.for_all ite_refused b16_mutants /\ L.for_all scoped2 b16_mutants /\
           ite_refused b16_inner_sort /\ not (D.scoped scope2 (fst b16_inner_sort))) =
  assert_norm (L.for_all ite_refused b16_mutants);
  assert_norm (L.for_all scoped2 b16_mutants);
  assert_norm (ite_refused b16_inner_sort /\ not (D.scoped scope2 (fst b16_inner_sort)))

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

(* C5 the term-ITE node and its document: the captured AnchoredReference
   q13 node 447 certificate (the else merge by a flattened `and`, a Real
   numeral inside a branch) is outside every other disjunct of
   check_node_cached and the replay checks it; the refutation of its
   negated equation is RootCertified (the Root gate reads and covers the
   consumed certificate) and the same document over the mutant with the
   merged branches swapped is pending. Hence the captured equation holds in
   every root model and in the standard root model of every u and every
   free choice uf (NR.lemma_replay through the document theorem; no Real
   law is assumed or derived). *)
let n447_mutant_cert : U.binder_certificate = ite_cert n447_bs n447_h n447_lhs n447_swapped_rhs
let n447_mutant_root : expr = forall_ n447_bs (eq n447_h n447_swapped_rhs)

let c5_ite_node ()
  : Lemma (not (old_paths (qi_node n447_cert n447_root_l n447_root_r)) /\
           SP.check_node PT.core_schema [] (qi_node n447_cert n447_root_l n447_root_r) ==
             checked n447_root_l n447_root_r /\
           RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction n447_cert) /\
           RD.check_root_document PT.core_schema (refutation n447_cert n447_root_l n447_root_r) == RD.RootCertified /\
           RD.check_root_document PT.core_schema (refutation n447_mutant_cert n447_root_l n447_mutant_root) ==
             RD.RootPending 1) =
  assert_norm (not (old_paths (qi_node n447_cert n447_root_l n447_root_r)));
  assert_norm (SP.check_node PT.core_schema [] (qi_node n447_cert n447_root_l n447_root_r) ==
               checked n447_root_l n447_root_r);
  assert_norm (RD.certificate_covered (S.signature PT.core_schema) (U.QuantifierIntroduction n447_cert));
  assert_norm (RD.check_root_document PT.core_schema (refutation n447_cert n447_root_l n447_root_r) == RD.RootCertified);
  assert_norm (RD.check_root_document PT.core_schema (refutation n447_mutant_cert n447_root_l n447_mutant_root) ==
               RD.RootPending 1)

let c5_valid (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures RD.root_holds u PT.core_schema i (eq n447_root_l n447_root_r)) =
  c5_ite_node ();
  RD.lemma_root_certified u PT.core_schema (refutation n447_cert n447_root_l n447_root_r) i;
  assert_norm (D.scoped [] (neg (eq n447_root_l n447_root_r)));
  lemma_not_holds u i (eq n447_root_l n447_root_r)

let c5_standard (u:TR.uninterpreted) (uf:TR.symbols u PT.core_schema)
  : Lemma (RD.root_holds u PT.core_schema (TR.standard u PT.core_schema uf) (eq n447_root_l n447_root_r)) =
  TR.lemma_standard_root u PT.core_schema uf;
  c5_valid u (TR.standard u PT.core_schema uf)
