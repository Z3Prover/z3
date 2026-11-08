module Z3SortedRealDocumentTests

(* Typed Int/Real Farkas certificates through the ACTUAL checker
   (Z3SortedProof.check_node_cached via check_document and
   check_document_epsilon, by normalization), the root gate
   (Z3SortedRootDocument.check_root_document) and the root theorems in EVERY
   root model. The literals compare closed Real terms over uninterpreted Real
   constants c, d (and an Int constant n under to_real). Positives are
   certified and false in every root model; each mutant is a well-typed
   document whose Farkas step stays an open obligation (RootPending 1). The
   0 < x < 1 bounds are satisfiable at x = 1/2 in the standard root
   (Z3SortedRealRoot.lemma_real_rounding_countermodel). Section R6 runs the
   ground ITE rewrite equations (SP.ite_rewrite) at every result sort. *)

open Z3AstTheory
open Z3ValueTheory
module S = Z3DatatypeSignature
module L = FStar.List.Tot
module TR = Z3TypedRoot
module SP = Z3SortedProof
module P = Z3ProofDocument
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module PT = Z3SortedProofTests
module RD = Z3SortedRootDocument
module RL = Z3SortedReal
module RR = Z3SortedRealRoot
module SS = Z3SortedSemantics
module BR = Z3BooleanRewrite
module V = Z3DatatypeValue
module D = Z3Definitions

let real : sort = TR.real_s
let integer : sort = TR.int_s

let constant (name:string) (s:sort) (params:list int) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = params } []

let c : expr = constant "c" real []
let d : expr = constant "d" real []
let c_twin : expr = constant "c" real [7]
let n : expr = constant "n" integer []
let rzero : expr = App (TR.real_numeral 0 1) []
let rone : expr = App (TR.real_numeral 1 1) []
let izero : expr = App (TR.int_numeral 0) []

let gt (a b:expr) : expr = App (TR.gt_decl real) [a; b]
let lt (a b:expr) : expr = App (TR.lt_decl real) [a; b]
let le (a b:expr) : expr = App (TR.le_decl real) [a; b]
let to_real (a:expr) : expr = App TR.to_real_decl [a]
let fake_gt (a b:expr) : expr = App ({ TR.gt_decl real with interp = None }) [a; b]

let entry (r:U.rule) (f:expr) (ids:list int) : P.entry = { P.rule = r; formula = f; premise_ids = ids }

let doc (assertions:list expr) (entries:list P.entry) (root:int) : P.document = {
  P.declarations = []; P.expressions = []; P.assertions = assertions; P.entries = entries; P.root = root;
}

(* Two asserted literals, one Farkas step to false over both. *)
let farkas_pair (a b:expr) (cs:list Z3LinearArithmeticAst.coefficient) : P.document =
  doc [a; b] [entry U.Asserted a []; entry U.Asserted b []; entry (U.ArithmeticFarkas cs) R.false_expr [0; 1]] 2

let one : Z3LinearArithmeticAst.coefficient = (1, 1)

let falsified (u:TR.uninterpreted) (sch:S.checked_schema) (dc:P.document) (i:TR.interp u sch) : prop =
  RD.typed_assertions dc.P.assertions /\ not (RD.root_truths u sch i dc.P.assertions)

let lemma_core_primitive () : Lemma (RL.real_primitive PT.core_schema) =
  assert_norm (RL.real_primitive PT.core_schema)

(* ---------------------------------------------------------------------- *)
(* R1. Positives: certified, and false in every root model                  *)
(* ---------------------------------------------------------------------- *)

(* {c > 0, c <= 0}: refuted by the typed replay; the Int path refuses Real. *)
let r1_strict_conflict ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_pair (gt c rzero) (le c rzero) [one; one]) ==
           RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (gt c rzero) (le c rzero) [one; one]) ==
               RD.RootCertified)

let farkas_node (premises:list expr) (cs:list Z3LinearArithmeticAst.coefficient) : U.proof_node = {
  U.kind = U.ArithmeticFarkas cs; conclusion = U.Holds R.false_expr;
  premises = L.map (fun e -> { U.conclusion = U.Holds e; hypotheses = [] }) premises;
}

let r1_dispatch ()
  : Lemma (SP.real_farkas PT.core_schema (farkas_node [gt c rzero; le c rzero] [one; one]) /\
           not (SP.arithmetic_farkas (farkas_node [gt c rzero; le c rzero] [one; one]))) =
  assert_norm (SP.real_farkas PT.core_schema (farkas_node [gt c rzero; le c rzero] [one; one]));
  assert_norm (not (SP.arithmetic_farkas (farkas_node [gt c rzero; le c rzero] [one; one])))

(* {c < d, d <= c}: the strict premise carries a nonzero weight. *)
let r1_strict_pair ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_pair (lt c d) (le d c) [one; one]) ==
           RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (lt c d) (le d c) [one; one]) ==
               RD.RootCertified)

(* Non-integral rational weights in the right ratio. *)
let r1_rational_weights ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_pair (lt c d) (le d c) [(1, 2); (2, 4)]) ==
           RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (lt c d) (le d c) [(1, 2); (2, 4)]) ==
               RD.RootCertified)

(* A negative inequality weight is read as its absolute value (A.weighted,
   shared with the Int path): the certificate is the valid one (1/2, 1/2). *)
let r1_negative_weight_magnitude ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_pair (lt c d) (le d c) [(-1, 2); (1, 2)]) ==
           RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (lt c d) (le d c) [(-1, 2); (1, 2)]) ==
               RD.RootCertified)

(* Mixed Int/Real through an explicit to_real: {to_real n > 0, n <= 0}. *)
let r1_mixed_to_real ()
  : Lemma (RD.check_root_document PT.core_schema
             (farkas_pair (gt (to_real n) rzero) (App (TR.le_decl integer) [n; izero]) [one; one]) ==
           RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema
                 (farkas_pair (gt (to_real n) rzero) (App (TR.le_decl integer) [n; izero]) [one; one]) ==
               RD.RootCertified)

(* The epsilon route (the one the native checker runs) agrees. *)
let r1_epsilon_route ()
  : Lemma (RD.check_root_document_epsilon PT.core_schema (farkas_pair (gt c rzero) (le c rzero) [one; one]) ==
           RD.RootCertified) =
  assert_norm (RD.check_root_document_epsilon PT.core_schema (farkas_pair (gt c rzero) (le c rzero) [one; one]) ==
               RD.RootCertified)

let r1_false_in_every_root (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema (farkas_pair (gt c rzero) (le c rzero) [one; one]) i /\
                   falsified u PT.core_schema (farkas_pair (lt c d) (le d c) [one; one]) i /\
                   falsified u PT.core_schema (farkas_pair (lt c d) (le d c) [(1, 2); (2, 4)]) i /\
                   falsified u PT.core_schema
                     (farkas_pair (gt (to_real n) rzero) (App (TR.le_decl integer) [n; izero]) [one; one]) i) =
  r1_strict_conflict ();
  RD.lemma_root_certified u PT.core_schema (farkas_pair (gt c rzero) (le c rzero) [one; one]) i;
  r1_strict_pair ();
  RD.lemma_root_certified u PT.core_schema (farkas_pair (lt c d) (le d c) [one; one]) i;
  r1_rational_weights ();
  RD.lemma_root_certified u PT.core_schema (farkas_pair (lt c d) (le d c) [(1, 2); (2, 4)]) i;
  r1_mixed_to_real ();
  RD.lemma_root_certified u PT.core_schema
    (farkas_pair (gt (to_real n) rzero) (App (TR.le_decl integer) [n; izero]) [one; one]) i

let r1_epsilon_false_in_every_root (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures not (RD.root_truths u PT.core_schema i [gt c rzero; le c rzero])) =
  r1_epsilon_route ();
  RD.lemma_root_certified_epsilon u PT.core_schema (farkas_pair (gt c rzero) (le c rzero) [one; one]) i

(* ---------------------------------------------------------------------- *)
(* R2. Satisfiable inputs and wrong certificates stay open                  *)
(* ---------------------------------------------------------------------- *)

(* 0 < c < 1 (true at c = 1/2): no Int lattice reasoning at Real, with unit
   weights or any other positive pair. *)
let r2_between_pending ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_pair (lt rzero c) (lt c rone) [one; one]) ==
             RD.RootPending 1 /\
           RD.check_root_document PT.core_schema (farkas_pair (lt rzero c) (lt c rone) [(2, 3); (2, 3)]) ==
             RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (lt rzero c) (lt c rone) [one; one]) ==
               RD.RootPending 1);
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (lt rzero c) (lt c rone) [(2, 3); (2, 3)]) ==
               RD.RootPending 1)

(* {c <= d, d <= c} holds at c = d: non-strict equal bounds do not contradict. *)
let r2_non_strict_pending ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_pair (le c d) (le d c) [one; one]) ==
           RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (le c d) (le d c) [one; one]) ==
               RD.RootPending 1)

(* A zero weight on the strict premise cannot supply strictness. *)
let r2_zero_weight_strict_pending ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_pair (lt c d) (le d c) [(0, 1); one]) ==
           RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (lt c d) (le d c) [(0, 1); one]) ==
               RD.RootPending 1)

(* Wrong magnitudes: the weighted sum does not cancel. *)
let r2_wrong_magnitude_pending ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_pair (lt c d) (le d c) [(1, 2); (3, 7)]) ==
             RD.RootPending 1 /\
           RD.check_root_document PT.core_schema (farkas_pair (gt c rzero) (le c rzero) [(2, 1); one]) ==
             RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (lt c d) (le d c) [(1, 2); (3, 7)]) ==
               RD.RootPending 1);
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (gt c rzero) (le c rzero) [(2, 1); one]) ==
               RD.RootPending 1)

(* A dropped needed premise: the step reads only c > 0. *)
let r2_dropped_premise_pending ()
  : Lemma (RD.check_root_document PT.core_schema
             (doc [gt c rzero; le c rzero]
                  [entry U.Asserted (gt c rzero) []; entry U.Asserted (le c rzero) [];
                   entry (U.ArithmeticFarkas [one]) R.false_expr [0]] 2) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (doc [gt c rzero; le c rzero]
                      [entry U.Asserted (gt c rzero) []; entry U.Asserted (le c rzero) [];
                       entry (U.ArithmeticFarkas [one]) R.false_expr [0]] 2) == RD.RootPending 1)

(* A wrong target: from c > 0 the step claims c > 1 (c = 1/2 refutes it). *)
let wrong_target_document : P.document =
  doc [gt c rzero; R.mk_not_expr (gt c rone)]
      [entry U.Asserted (gt c rzero) []; entry (U.ArithmeticFarkas [one; one]) (gt c rone) [0];
       entry U.Asserted (R.mk_not_expr (gt c rone)) []; entry U.UnitResolution R.false_expr [1; 2]]
      3

let r2_wrong_target_pending ()
  : Lemma (RD.check_root_document PT.core_schema wrong_target_document == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema wrong_target_document == RD.RootPending 1)

(* A counterfeit > (same name and signature, no interpretation tag) and a
   same-spelled distinct constant: no Real law relates them. *)
let r2_fake_operator_pending ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_pair (fake_gt c rzero) (le c rzero) [one; one]) ==
           RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (fake_gt c rzero) (le c rzero) [one; one]) ==
               RD.RootPending 1)

let r2_twin_constant_pending ()
  : Lemma (RD.check_root_document PT.core_schema (farkas_pair (gt c rzero) (le c_twin rzero) [one; one]) ==
           RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema (farkas_pair (gt c rzero) (le c_twin rzero) [one; one]) ==
               RD.RootPending 1)

(* ---------------------------------------------------------------------- *)
(* R3. The schema gate and the unchanged Int path                           *)
(* ---------------------------------------------------------------------- *)

(* A checked schema registering a datatype named Real: the gate is closed. *)
let r3_real_datatype_gate ()
  : Lemma (not (SP.real_farkas RR.real_datatype_schema (farkas_node [gt c rzero; le c rzero] [one; one]))) =
  assert_norm (not (SP.real_farkas RR.real_datatype_schema (farkas_node [gt c rzero; le c rzero] [one; one])))

(* The typed replay rounds Int literals exactly as the Int path: the integer
   bounds 0 < x < 1 are refuted by both, and the mutant (1, 0) by neither
   (Z3SortedRootDocumentTests G5/G6 keep their verdicts). *)
let x_int : expr = constant "x" integer []
let int_positive : expr = App (TR.gt_decl integer) [x_int; izero]
let int_below_one : expr = App (TR.lt_decl integer) [x_int; App (TR.int_numeral 1) []]

let r3_int_path ()
  : Lemma (SP.arithmetic_farkas (farkas_node [int_positive; int_below_one] [one; one]) /\
           SP.real_farkas PT.core_schema (farkas_node [int_positive; int_below_one] [one; one]) /\
           not (SP.arithmetic_farkas (farkas_node [int_positive; int_below_one] [one; (0, 1)])) /\
           not (SP.real_farkas PT.core_schema (farkas_node [int_positive; int_below_one] [one; (0, 1)]))) =
  assert_norm (SP.arithmetic_farkas (farkas_node [int_positive; int_below_one] [one; one]));
  assert_norm (SP.real_farkas PT.core_schema (farkas_node [int_positive; int_below_one] [one; one]));
  assert_norm (not (SP.arithmetic_farkas (farkas_node [int_positive; int_below_one] [one; (0, 1)])));
  assert_norm (not (SP.real_farkas PT.core_schema (farkas_node [int_positive; int_below_one] [one; (0, 1)])))

(* ---------------------------------------------------------------------- *)
(* R4. Premise-free Real rewrite equations (SP.real_rewrite)                *)
(* ---------------------------------------------------------------------- *)

let rewrite_node (a b:expr) : U.proof_node = {
  U.kind = U.RewriteRule; conclusion = U.Equal a b; premises = [];
}

let rewrite_pending (sch:S.checked_schema) (a b:expr) : option nat =
  match SP.check_node_cached sch [] (rewrite_node a b) with
  | Some (_, pending) -> Some pending
  | None -> None

(* The producer's top-level shapes: (c > 0) = not (c <= 0), (to_real 0) = 0;
   mutants: not (c < 0), the Int-style strict rounding c < d to c <= d - 1, a
   counterfeit >, and the closed gate of a schema registering a datatype
   named Real. *)
let r4_rewrite_nodes ()
  : Lemma (rewrite_pending PT.core_schema (gt c rzero) (R.mk_not_expr (le c rzero)) == Some 0 /\
           rewrite_pending PT.core_schema (to_real izero) rzero == Some 0 /\
           rewrite_pending PT.core_schema (gt c rzero) (R.mk_not_expr (lt c rzero)) == Some 1 /\
           rewrite_pending PT.core_schema (lt c d) (le c (App (TR.minus_decl real) [d; rone])) == Some 1 /\
           rewrite_pending PT.core_schema (fake_gt c rzero) (R.mk_not_expr (le c rzero)) == Some 1 /\
           rewrite_pending RR.real_datatype_schema (gt c rzero) (R.mk_not_expr (le c rzero)) == Some 1) =
  assert_norm (rewrite_pending PT.core_schema (gt c rzero) (R.mk_not_expr (le c rzero)) == Some 0);
  assert_norm (rewrite_pending PT.core_schema (to_real izero) rzero == Some 0);
  assert_norm (rewrite_pending PT.core_schema (gt c rzero) (R.mk_not_expr (lt c rzero)) == Some 1);
  assert_norm (rewrite_pending PT.core_schema (lt c d) (le c (App (TR.minus_decl real) [d; rone])) == Some 1);
  assert_norm (rewrite_pending PT.core_schema (fake_gt c rzero) (R.mk_not_expr (le c rzero)) == Some 1);
  assert_norm (rewrite_pending RR.real_datatype_schema (gt c rzero) (R.mk_not_expr (le c rzero)) == Some 1)

(* The producer's refutation shape: the asserted c > 0 rewritten to
   not (c <= 0), then the Farkas step over c <= 0 and the rewritten fact. *)
let rewritten : expr = R.mk_not_expr (le c rzero)
let rewrite_document : P.document =
  doc [gt c rzero; le c rzero]
      [entry U.Asserted (gt c rzero) [];
       entry U.RewriteRule (R.mk_eq_expr (gt c rzero) rewritten) [];
       entry U.ModusPonens rewritten [0; 1];
       entry U.Asserted (le c rzero) [];
       entry (U.ArithmeticFarkas [one; one]) R.false_expr [2; 3]]
      4

let r4_rewrite_document ()
  : Lemma (RD.check_root_document_epsilon PT.core_schema rewrite_document == RD.RootCertified) =
  assert_norm (RD.check_root_document_epsilon PT.core_schema rewrite_document == RD.RootCertified)

let r4_rewrite_document_false (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures not (RD.root_truths u PT.core_schema i rewrite_document.P.assertions)) =
  r4_rewrite_document ();
  RD.lemma_root_certified_epsilon u PT.core_schema rewrite_document i

(* ---------------------------------------------------------------------- *)
(* R6. Ground ITE rewrite equations (SP.ite_rewrite)                        *)
(* ---------------------------------------------------------------------- *)

(* The producer's premise-free top-level `rewrite` steps of the three ITE
   laws of Z3NnfReplay.ite_rewritten, at the result sorts Bool, Int, Real,
   an uninterpreted sort, an array sort, a datatype (PT.schema's Box) and
   with guards and branches under function applications. Each positive is
   checked as a node and certifies the refutation of its negation (false in
   every root model); each mutant (swapped branches, `or` for `and` and
   back, the opposite guard, a counterfeit ite/and declaration, a
   same-spelled twin branch) leaves the rewrite step open. No Real law is
   read: the laws also certify on a schema whose Real gate is closed. *)

let usort : sort = BaseSort "U"
let ite_ (g x y:expr) : expr = App (SS.ite_decl (get_sort x)) [g; x; y]
let and_ (a b:expr) : expr = App (BR.connective_decl BR.Conjunction [a; b]) [a; b]
let or_ (a b:expr) : expr = App (BR.connective_decl BR.Disjunction [a; b]) [a; b]

let g : expr = constant "g" bool_sort []
let h : expr = constant "h" bool_sort []

let else_merged (g h x y:expr) : expr & expr = (ite_ g (ite_ h x y) y, ite_ (and_ g h) x y)
let then_merged (g h x y:expr) : expr & expr = (ite_ g x (ite_ h x y), ite_ (or_ g h) x y)
let not_swapped (g x y:expr) : expr & expr = (ite_ (R.mk_not_expr g) x y, ite_ g y x)

let laws (x y:expr) : list (expr & expr) = [else_merged g h x y; then_merged g h x y; not_swapped g x y]

let at_sort (srt:sort) : list (expr & expr) = laws (constant "x" srt []) (constant "y" srt [])

let pu : expr = App { decl_name = "P"; domain = [usort]; range = bool_sort; interp = None; int_params = [] }
                    [constant "a" usort []]
let qu : expr = App { decl_name = "Q"; domain = [usort]; range = bool_sort; interp = None; int_params = [] }
                    [constant "a" usort []]
let fu : expr = App { decl_name = "F"; domain = [usort]; range = integer; interp = None; int_params = [] }
                    [constant "a" usort []]
let gu : expr = App { decl_name = "G"; domain = [usort]; range = integer; interp = None; int_params = [] }
                    [constant "a" usort []]

let applied : list (expr & expr) = [else_merged pu qu fu gu; then_merged pu qu fu gu; not_swapped pu fu gu]

let core_positives : list (expr & expr) =
  L.concatMap at_sort [bool_sort; integer; real; usort; ArraySort [usort] integer] `L.append` applied

let box_positives : list (expr & expr) = laws PT.x PT.y

let ite_rewrite_node (lr:expr & expr) : U.proof_node = rewrite_node (fst lr) (snd lr)

(* not (lhs = rhs), the rewrite lhs = rhs, and unit resolution to false. *)
let ite_document (lr:expr & expr) : P.document =
  let e = R.mk_eq_expr (fst lr) (snd lr) in
  doc [R.mk_not_expr e]
      [entry U.Asserted (R.mk_not_expr e) []; entry U.RewriteRule e []; entry U.UnitResolution R.false_expr [0; 1]]
      2

let node_checked (sch:S.checked_schema) (lr:expr & expr) : bool =
  SP.ite_rewrite (ite_rewrite_node lr) && rewrite_pending sch (fst lr) (snd lr) = Some 0

let certified (sch:S.checked_schema) (lr:expr & expr) : bool =
  RD.check_root_document sch (ite_document lr) = RD.RootCertified

let certified_epsilon (sch:S.checked_schema) (lr:expr & expr) : bool =
  RD.check_root_document_epsilon sch (ite_document lr) = RD.RootCertified

let r6_nodes ()
  : Lemma (L.for_all (node_checked PT.core_schema) core_positives /\
           L.for_all (node_checked PT.schema) box_positives) =
  assert_norm (L.for_all (node_checked PT.core_schema) core_positives);
  assert_norm (L.for_all (node_checked PT.schema) box_positives)

let r6_certified ()
  : Lemma (L.for_all (certified PT.core_schema) core_positives /\
           L.for_all (certified PT.schema) box_positives /\
           L.for_all (certified_epsilon PT.core_schema) (at_sort usort) /\
           L.for_all (certified_epsilon PT.schema) box_positives) =
  assert_norm (L.for_all (certified PT.core_schema) core_positives);
  assert_norm (L.for_all (certified PT.schema) box_positives);
  assert_norm (L.for_all (certified_epsilon PT.core_schema) (at_sort usort));
  assert_norm (L.for_all (certified_epsilon PT.schema) box_positives)

let rec lemma_for_all_memP (#a:Type) (f:a -> Tot bool) (l:list a) (x:a)
  : Lemma (requires L.for_all f l /\ L.memP x l) (ensures f x) (decreases l) =
  match l with
  | [] -> ()
  | _ :: rest -> FStar.Classical.move_requires (lemma_for_all_memP f rest) x

let r6_false_in_every_root (u:TR.uninterpreted) (i:TR.interp u PT.core_schema) (j:TR.interp u PT.schema)
  : Lemma (requires TR.root_model u PT.core_schema i /\ TR.root_model u PT.schema j)
          (ensures (forall (lr:expr & expr). L.memP lr core_positives ==>
                      falsified u PT.core_schema (ite_document lr) i) /\
                   (forall (lr:expr & expr). L.memP lr box_positives ==>
                      falsified u PT.schema (ite_document lr) j)) =
  r6_certified ();
  let core (lr:expr & expr)
    : Lemma (requires L.memP lr core_positives) (ensures falsified u PT.core_schema (ite_document lr) i) =
    lemma_for_all_memP (certified PT.core_schema) core_positives lr;
    RD.lemma_root_certified u PT.core_schema (ite_document lr) i in
  let box (lr:expr & expr)
    : Lemma (requires L.memP lr box_positives) (ensures falsified u PT.schema (ite_document lr) j) =
    lemma_for_all_memP (certified PT.schema) box_positives lr;
    RD.lemma_root_certified u PT.schema (ite_document lr) j in
  FStar.Classical.forall_intro (FStar.Classical.move_requires core);
  FStar.Classical.forall_intro (FStar.Classical.move_requires box)

(* Mutants at U: each equation is false at some interpretation of g, h, x, y
   (x <> y), so its document is satisfiable and the rewrite step stays open. *)
let xu : expr = constant "x" usort []
let yu : expr = constant "y" usort []
let fake_ite : func_decl = { SS.ite_decl usort with interp = None }
let fake_and : func_decl = { BR.connective_decl BR.Conjunction [g; h] with interp = None }

let mutants : list (expr & expr) = [
  (ite_ g (ite_ h xu yu) yu, ite_ (and_ g h) yu xu);                    (* swapped branches *)
  (ite_ g (ite_ h xu yu) yu, ite_ (or_ g h) xu yu);                     (* or for and *)
  (ite_ g xu (ite_ h xu yu), ite_ (and_ g h) xu yu);                    (* and for or *)
  (ite_ g (ite_ h xu yu) yu, ite_ (and_ g (R.mk_not_expr h)) xu yu);    (* opposite inner guard *)
  (ite_ g xu yu, ite_ g yu xu);                                         (* swap without negation *)
  (ite_ (R.mk_not_expr g) xu yu, ite_ g xu yu);                         (* negation, branches kept *)
  (ite_ g (ite_ h xu yu) yu, App fake_ite [and_ g h; xu; yu]);          (* counterfeit ite *)
  (ite_ g (ite_ h xu yu) yu, ite_ (App fake_and [g; h]) xu yu);         (* counterfeit and *)
  (ite_ g (ite_ h xu yu) yu, ite_ (and_ g h) (constant "x" usort [7]) yu)  (* twin branch *)
]

let node_open (lr:expr & expr) : bool =
  not (SP.ite_rewrite (ite_rewrite_node lr)) && rewrite_pending PT.core_schema (fst lr) (snd lr) = Some 1

let document_open (lr:expr & expr) : bool =
  RD.check_root_document PT.core_schema (ite_document lr) = RD.RootPending 1

let r6_mutants_open ()
  : Lemma (L.for_all node_open mutants /\ L.for_all document_open mutants) =
  assert_norm (L.for_all node_open mutants);
  assert_norm (L.for_all document_open mutants)

(* The direct path reads closed equations with no premises and the
   RewriteRule label only: an open side, a premise or another rule label is
   refused by SP.ite_rewrite. *)
let r6_shape_guards ()
  : Lemma (not (SP.ite_rewrite (rewrite_node (ite_ g (ite_ h (Var 0 usort) yu) yu)
                                             (ite_ (and_ g h) (Var 0 usort) yu))) /\
           not (SP.ite_rewrite ({ ite_rewrite_node (else_merged g h xu yu) with
                                  U.premises = [{ U.conclusion = U.Holds g; hypotheses = [] }] })) /\
           not (SP.ite_rewrite ({ ite_rewrite_node (else_merged g h xu yu) with U.kind = U.LemmaRule }))) =
  assert_norm (not (SP.ite_rewrite (rewrite_node (ite_ g (ite_ h (Var 0 usort) yu) yu)
                                                 (ite_ (and_ g h) (Var 0 usort) yu))));
  assert_norm (not (SP.ite_rewrite ({ ite_rewrite_node (else_merged g h xu yu) with
                                      U.premises = [{ U.conclusion = U.Holds g; hypotheses = [] }] })));
  assert_norm (not (SP.ite_rewrite ({ ite_rewrite_node (else_merged g h xu yu) with U.kind = U.LemmaRule })))

(* The Real gate closed (RR.real_datatype_schema registers a datatype named
   Real): the ITE laws still certify, and the document is false in EVERY
   Sorted model of that schema, with no Real law and no binder law. *)
let r6_real_gate_closed ()
  : Lemma (not (RL.real_primitive RR.real_datatype_schema) /\
           L.for_all (fun lr -> SP.check_document RR.real_datatype_schema (ite_document lr) = Some 0)
             (L.append (at_sort usort) (at_sort bool_sort)) /\
           not (SP.real_rewrite RR.real_datatype_schema (ite_rewrite_node (else_merged g h xu yu)))) =
  RR.lemma_real_datatype_refused ();
  assert_norm (L.for_all (fun lr -> SP.check_document RR.real_datatype_schema (ite_document lr) = Some 0)
                 (L.append (at_sort usort) (at_sort bool_sort)));
  assert_norm (not (SP.real_rewrite RR.real_datatype_schema (ite_rewrite_node (else_merged g h xu yu))))

let gate_closed_document : P.document = ite_document (else_merged g h xu yu)

let r6_real_gate_closed_false (#base:sort -> Type0) (bc:S.boolean_carrier base)
                              (eq:SS.scalar_model base)
                              (other:V.interpretation base (S.signature RR.real_datatype_schema))
  : Lemma (not (SS.truths RR.real_datatype_schema bc eq other gate_closed_document.P.assertions)) =
  assert_norm (SP.check_document RR.real_datatype_schema gate_closed_document == Some 0);
  assert_norm (not (SP.needs_forall_semantics gate_closed_document.P.entries) /\
               not (SP.needs_forall_truth gate_closed_document.P.entries) /\
               not (SP.needs_binder_semantics gate_closed_document.P.entries) /\
               not (SP.needs_real_semantics RR.real_datatype_schema gate_closed_document.P.entries) /\
               not (SP.needs_division_semantics gate_closed_document.P.entries));
  SP.lemma_check_document RR.real_datatype_schema bc eq other gate_closed_document
