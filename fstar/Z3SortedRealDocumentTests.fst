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
   (Z3SortedRealRoot.lemma_real_rounding_countermodel). *)

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
