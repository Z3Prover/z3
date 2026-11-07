module Z3SortedRealOrderTests

(* Tests of the Real equality/order laws on the Sorted route: the producer's
   arith_eq_adapter clauses over Real terms (Z3SortedProof.real_order, the
   Real mirror of the Int order_clause) and the Real equation rewrites
   (Z3SortedRealLinear.real_equivalent: renormalized, negated and proportional
   difference polynomials, and equations of constants).

   O1 the clause check (normalized): the hosted th-lemma shapes
      (`not (0 = a) \/ a >= 0`, `not (2 = a) \/ a >= 2`, the difference forms
      `a + (-1)*b` in both operand orders, a three-operand sum atom, a
      nonlinear atom, a quotient atom, a to_real atom, rational constants) and
      the antisymmetric three-literal clauses in every literal order, each
      checked by real_order and by no other kernel, and their refusals: strict
      comparison, same-orientation bounds, a wrong coefficient / sign /
      target, a counterfeit `=` and `-1`, twin constants, Int operands, an
      unsupported orientation (a valid clause written with Real `-`; a SHAPE
      control, not a false mutant), more than three literals, a non-clause,
      the Real gate of a schema registering a datatype named Real, and the
      leaf and lemma rules.
   O2 documents: the refutation of c = 2, c > 3 (z3's own triangle-eq proof
      shape) is RootCertified on both routes and false in every root model;
      the mutant documents stay RootPending 1.
   O3 the equation rewrites (normalized): the hosted shapes, the proportional
      and commuted forms, equations of constants, and the wrong sign, offset,
      target, constant, sort and operator mutants; the node check
      (SP.real_rewrite), a refutation using one, and the quant-intro leaf
      replay with the Real gate (and its pending verdict without it).
   O4 counter-models: every mutant of O1 and O3 that claims a false statement
      is FALSE in the standard root model at a concrete typed environment of
      Real variables (equal values for the strict, coefficient and target
      mutants, opposite bounds for the orientation mutant), so a check that
      accepted any of them would be unsound.
   O5 the laws in every Sorted model with the Real laws, hence in every root
      model: the accepted clauses and equations hold there, read through
      Z3SortedProof.lemma_real_order_clause and
      Z3SortedRealLinear.lemma_real_equivalent.

   Every expected refusal is the checker's own verdict on a well-sorted input,
   computed by normalization; none is a parse, effect or refinement error.
   Deep and large inputs run natively (test_native_bridge.ml, Z3CherryTests.fst). *)

open Z3AstTheory
open Z3ValueTheory
open FStar.Real
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
module BR = Z3BooleanRewrite
module B = Z3BoundedBoolEquiv
module NR = Z3NnfReplay
module RD = Z3SortedRootDocument
module PT = Z3SortedProofTests
module RL = Z3SortedReal
module RR = Z3SortedRealRoot
module LIN = Z3SortedRealLinear
module LA = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module RPT = Z3SortedRealReplayTests

(* ---------------------------------------------------------------------- *)
(* Shapes                                                                   *)
(* ---------------------------------------------------------------------- *)

let real : sort = TR.real_s
let integer : sort = TR.int_s

let constant (name:string) (s:sort) (params:list int) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = params } []

let c : expr = constant "c" real []
let d : expr = constant "d" real []
let e : expr = constant "e" real []
let c_twin : expr = constant "c" real [7]
let i : expr = constant "i" integer []
let j : expr = constant "j" integer []

let num (n:int) : expr = App (TR.real_numeral n 1) []
let rat (n:int) (q:pos) : expr = App (TR.real_numeral n q) []
let zero : expr = num 0
let two : expr = num 2
let m1 : expr = num (-1)

let eq (a b:expr) : expr = R.mk_eq_expr a b
let neg (a:expr) : expr = R.mk_not_expr a
let le (a b:expr) : expr = App (TR.le_decl real) [a; b]
let lt (a b:expr) : expr = App (TR.lt_decl real) [a; b]
let ge (a b:expr) : expr = App (TR.ge_decl real) [a; b]
let gt (a b:expr) : expr = App (TR.gt_decl real) [a; b]
let plus (a b:expr) : expr = App (TR.plus_decl real) [a; b]
let times (a b:expr) : expr = App (TR.times_decl real) [a; b]
let minus (a b:expr) : expr = App (TR.minus_decl real) [a; b]
let quotient (a b:expr) : expr = App TR.divide_decl [a; b]
let to_real (a:expr) : expr = App TR.to_real_decl [a]
let sum3 (a b c':expr) : expr =
  App ({ TR.plus_decl real with domain = [real; real; real] }) [a; b; c']

let or2 (a b:expr) : expr = App (BR.connective_decl BR.Disjunction [a; b]) [a; b]
let or3 (a b c':expr) : expr = App (BR.connective_decl BR.Disjunction [a; b; c']) [a; b; c']
let or4 (a b c' d':expr) : expr = App (BR.connective_decl BR.Disjunction [a; b; c'; d']) [a; b; c'; d']

(* x - y as the producer writes it (x + (-1)*y), in the solver's own order
   ((-1)*y + x), and the reversed difference. *)
let diff (x y:expr) : expr = plus x (times m1 y)
let diff_swapped (x y:expr) : expr = plus (times m1 y) x

(* Counterfeits: same spelling and signature, no interpretation tag. *)
let fake_eq_decl : func_decl = { R.eq_decl real with interp = None }
let fake_eq (a b:expr) : expr = App fake_eq_decl [a; b]
let fake_m1 : expr = constant "-1" real []
let fake_le (a b:expr) : expr = App ({ TR.le_decl real with interp = None }) [a; b]
let fake_plus (a b:expr) : expr = App ({ TR.plus_decl real with interp = None }) [a; b]
let fake_times (a b:expr) : expr = App ({ TR.times_decl real with interp = None }) [a; b]
let twin_m1 : expr = App ({ TR.real_numeral (-1) 1 with int_params = [-2; 2] }) []
let int_eq (a b:expr) : expr = R.mk_eq_expr a b
let int_le (a b:expr) : expr = App (TR.le_decl integer) [a; b]

let th_node (clause:expr) : U.proof_node =
  { U.kind = U.Unverified "th-lemma"; conclusion = U.Holds clause; premises = [] }

let pending_of (sch:S.checked_schema) (n:U.proof_node) : option nat =
  match SP.check_node_cached sch [] n with
  | Some (_, p) -> Some p
  | None -> None

(* The disjuncts of check_node_cached that read a premise-free theory-lemma
   clause other than the Real order check: the bounded propositional, equality,
   Int order and datatype consequence, and the coefficient-free Int search. *)
let old_paths (clause:expr) : bool =
  SP.consequence PT.core_schema [] clause ||
  DT.consequence PT.core_schema [] (SP.scoped_proposition ({ U.conclusion = U.Holds clause; hypotheses = [] })) ||
  SP.linear_consequence [] clause

let checked_clause (clause:expr) : bool =
  SP.real_order PT.core_schema (th_node clause) && not (old_paths clause) &&
  pending_of PT.core_schema (th_node clause) = Some 0

let refused_clause (clause:expr) : bool =
  not (SP.real_order PT.core_schema (th_node clause)) && not (old_paths clause) &&
  pending_of PT.core_schema (th_node clause) = Some 1

(* ---------------------------------------------------------------------- *)
(* O1. The clause check                                                     *)
(* ---------------------------------------------------------------------- *)

(* The hosted shapes (Pulse.Class.PtsTo, Pulse.Lib.Box: arith_eq_adapter over
   BoxReal projections, here over the opaque Real constants c, d, e), both
   operand orders of the difference, atoms that are sums, products,
   quotients and to_real, and the three-literal clauses in every order. *)
let positives : list expr = [
  or2 (neg (eq c d)) (le c d);
  or2 (neg (eq c d)) (ge c d);
  or2 (neg (eq c d)) (le d c);
  or2 (neg (eq c d)) (ge (diff c d) zero);
  or2 (neg (eq c d)) (le (diff c d) zero);
  or2 (neg (eq c d)) (eq (diff c d) zero);
  or2 (neg (eq c d)) (le (diff_swapped c d) zero);
  or2 (neg (eq c d)) (ge (diff d c) zero);
  or2 (ge (diff c d) zero) (neg (eq c d));
  or2 (neg (eq zero c)) (ge c zero);
  or2 (neg (eq zero c)) (le c zero);
  or2 (neg (eq two c)) (ge c two);
  or2 (neg (eq c (rat 1 2))) (le c (rat 1 2));
  or2 (neg (eq (sum3 c d (times m1 e)) zero)) (le (sum3 c d (times m1 e)) zero);
  or2 (neg (eq zero (sum3 c d (times m1 e)))) (le (sum3 c d (times m1 e)) zero);
  or2 (neg (eq c (times d e))) (le (diff c (times d e)) zero);
  or2 (neg (eq c (quotient d e))) (ge (diff c (quotient d e)) zero);
  or2 (neg (eq (to_real i) c)) (le (to_real i) c);
  or2 (neg (eq (to_real i) (to_real j))) (le (to_real j) (to_real i));
  or3 (eq c d) (neg (le (diff c d) zero)) (neg (ge (diff c d) zero));
  or3 (neg (le (diff c d) zero)) (eq c d) (neg (ge (diff c d) zero));
  or3 (neg (ge (diff c d) zero)) (neg (le (diff c d) zero)) (eq c d);
  or3 (eq c d) (neg (le c d)) (neg (ge c d));
  or3 (eq c d) (neg (le c d)) (neg (le d c));
  or3 (neg (ge (diff c d) zero)) (eq c d) (neg (le (diff_swapped c d) zero))
]

let o1_positives () : Lemma (L.for_all checked_clause positives) =
  assert_norm (L.for_all checked_clause positives)

(* The Int clauses keep their own kernel, and the Real check does not read them. *)
let int_clause : expr = or2 (neg (int_eq i j)) (int_le i j)

let o1_int_unchanged ()
  : Lemma (SP.order_clause int_clause /\ not (SP.real_order PT.core_schema (th_node int_clause)) /\
           pending_of PT.core_schema (th_node int_clause) = Some 0) =
  assert_norm (SP.order_clause int_clause);
  assert_norm (not (SP.real_order PT.core_schema (th_node int_clause)));
  assert_norm (pending_of PT.core_schema (th_node int_clause) = Some 0)

(* Refusals, each stays pending. These clauses are FALSE statements: the
   strict comparison (equal operands), same-orientation bounds, a wrong
   coefficient, sign and target (O4 builds opposite-value models for them),
   a counterfeit or twin declaration (a free symbol), Int operands, a
   positive equation, a doubled negation and a single literal. *)
let mutants : list expr = [
  or2 (neg (eq c d)) (lt (diff c d) zero);
  or2 (neg (eq c d)) (lt c d);
  or2 (neg (eq c d)) (gt c d);
  or3 (eq c d) (neg (le (diff c d) zero)) (neg (ge (diff d c) zero));
  or3 (eq c d) (neg (le c d)) (neg (ge d c));
  or2 (neg (eq c d)) (le (plus c (times (num 1) d)) zero);
  or2 (neg (eq c d)) (ge (plus c (times (num (-2)) d)) zero);
  or2 (neg (eq c d)) (le (plus (times (num 2) c) (times m1 d)) zero);
  or2 (neg (eq c d)) (le (diff c e) zero);
  or2 (neg (eq c d)) (le c e);
  or2 (neg (eq c d)) (le (diff e d) zero);
  or2 (neg (eq c c_twin)) (le c d);
  or2 (neg (eq c d)) (le c_twin d);
  or2 (neg (eq c d)) (le (diff c_twin d) zero);
  or2 (neg (fake_eq c d)) (le c d);
  or2 (neg (eq c d)) (fake_le c d);
  or2 (neg (eq c d)) (le (plus c (fake_times m1 d)) zero);
  or2 (neg (eq c d)) (le (fake_plus c (times m1 d)) zero);
  or2 (neg (eq c d)) (le (plus c (times fake_m1 d)) zero);
  or2 (neg (int_eq i j)) (le c d);
  or2 (neg (eq c d)) (int_le i j);
  or2 (eq c d) (le c d);
  or2 (neg (neg (eq c d))) (le c d);
  neg (eq c d);
  eq c d;
  le c d
]

let o1_mutants () : Lemma (L.for_all refused_clause mutants) =
  assert_norm (L.for_all refused_clause mutants)

(* VALID clauses in an unsupported shape: SHAPE-refusal controls, not false
   mutants. The Real `-` and `c <= d + 0` are not the producer's
   x + (-1)*y; a numeral -2/2 is not the canonical -1; the bound must be
   against the numeral 0 on the right; a strict literal is no bound; four
   literals, three literals without an equation, and the totality clause are
   other laws. *)
let unsupported : list expr = [
  or2 (neg (eq c d)) (le (minus c d) zero);
  or2 (neg (eq c d)) (le c (plus d zero));
  or2 (neg (eq c d)) (le (plus c (times twin_m1 d)) zero);
  or2 (neg (eq c d)) (le (diff c d) (num 1));
  or2 (neg (eq c d)) (le zero (diff c d));
  or3 (eq c d) (neg (le c d)) (neg (lt d c));
  or4 (neg (eq c d)) (le c d) (le d c) (le c e);
  or3 (neg (eq c d)) (le c d) (le d c);
  or2 (neg (le c d)) (le d c)
]

let o1_unsupported () : Lemma (L.for_all refused_clause unsupported) =
  assert_norm (L.for_all refused_clause unsupported)

(* Three literals are accepted and four are refused; a conclusion that is
   not an or-clause is no clause. *)
let o1_literal_bounds ()
  : Lemma (checked_clause (or3 (eq c d) (neg (le c d)) (neg (ge c d))) /\
           refused_clause (or4 (eq c d) (neg (le c d)) (neg (ge c d)) (le c e))) =
  assert_norm (checked_clause (or3 (eq c d) (neg (le c d)) (neg (ge c d))));
  assert_norm (refused_clause (or4 (eq c d) (neg (le c d)) (neg (ge c d)) (le c e)))

(* The gate: a schema registering a datatype named Real has no Real laws, so
   the clause is refused there (and the check is open); the rule label, the
   premises and the judgment form are what they are. *)
let o1_node_guards ()
  : Lemma (not (SP.real_order RR.real_datatype_schema (th_node (or2 (neg (eq c d)) (le c d)))) /\
           SP.real_order PT.core_schema ({ th_node (or2 (neg (eq c d)) (le c d)) with U.kind = U.Skolemization }) /\
           SP.real_order PT.core_schema ({ th_node (or2 (neg (eq c d)) (le c d)) with U.kind = U.Unverified "other" }) /\
           not (SP.real_order PT.core_schema ({ th_node (or2 (neg (eq c d)) (le c d)) with U.kind = U.LemmaRule })) /\
           not (SP.real_order PT.core_schema ({ th_node (or2 (neg (eq c d)) (le c d)) with U.kind = U.Asserted })) /\
           not (SP.real_order PT.core_schema ({ th_node (or2 (neg (eq c d)) (le c d)) with U.kind = U.Hypothesis })) /\
           not (SP.real_order PT.core_schema
                  ({ th_node (or2 (neg (eq c d)) (le c d)) with U.conclusion = U.Equal (eq c d) (le c d) }))) =
  RR.lemma_real_datatype_refused ();
  assert_norm (not (SP.real_order RR.real_datatype_schema (th_node (or2 (neg (eq c d)) (le c d)))));
  assert_norm (SP.real_order PT.core_schema ({ th_node (or2 (neg (eq c d)) (le c d)) with U.kind = U.Skolemization }));
  assert_norm (SP.real_order PT.core_schema ({ th_node (or2 (neg (eq c d)) (le c d)) with U.kind = U.Unverified "other" }));
  assert_norm (not (SP.real_order PT.core_schema ({ th_node (or2 (neg (eq c d)) (le c d)) with U.kind = U.LemmaRule })));
  assert_norm (not (SP.real_order PT.core_schema ({ th_node (or2 (neg (eq c d)) (le c d)) with U.kind = U.Asserted })));
  assert_norm (not (SP.real_order PT.core_schema ({ th_node (or2 (neg (eq c d)) (le c d)) with U.kind = U.Hypothesis })));
  assert_norm (not (SP.real_order PT.core_schema
                      ({ th_node (or2 (neg (eq c d)) (le c d)) with U.conclusion = U.Equal (eq c d) (le c d) })))

(* ---------------------------------------------------------------------- *)
(* O2. Documents                                                            *)
(* ---------------------------------------------------------------------- *)

let entry (r:U.rule) (f:expr) (ids:list int) : P.entry = { P.rule = r; formula = f; premise_ids = ids }

let doc (assertions:list expr) (entries:list P.entry) (root:int) : P.document = {
  P.declarations = []; P.expressions = []; P.assertions = assertions; P.entries = entries; P.root = root;
}

let one : LA.coefficient = (1, 1)
let three : expr = num 3

(* z3's own proof of {c = 2, c > 3} (an uninterpreted function application in
   place of c): the Farkas lemma over the two bounds, the rewrite of the
   strict bound, the triangle-eq clause of the equation, and unit resolution.
   `triangle` is that clause; every other step is checked by the existing
   Real kernels. *)
let triangle_document (triangle:expr) : P.document =
  doc [eq c two; gt c three]
      [entry U.Asserted (eq c two) [];
       entry U.Asserted (gt c three) [];
       entry U.RewriteRule (eq (gt c three) (neg (le c three))) [];
       entry U.ModusPonens (neg (le c three)) [1; 2];
       entry (U.ArithmeticFarkas [one; one]) (or2 (neg (le c two)) (le c three)) [];
       entry U.UnitResolution (neg (le c two)) [4; 3];
       entry (U.Unverified "th-lemma") triangle [];
       entry U.UnitResolution R.false_expr [6; 0; 5]]
      7

let hosted_triangle : expr = or2 (neg (eq c two)) (le c two)

let falsified (u:TR.uninterpreted) (sch:S.checked_schema) (dc:P.document) (i:TR.interp u sch) : prop =
  RD.typed_assertions dc.P.assertions /\ not (RD.root_truths u sch i dc.P.assertions)

let o2_certified ()
  : Lemma (RD.check_root_document PT.core_schema (triangle_document hosted_triangle) == RD.RootCertified /\
           RD.check_root_document_epsilon PT.core_schema (triangle_document hosted_triangle) == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (triangle_document hosted_triangle) == RD.RootCertified);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (triangle_document hosted_triangle) == RD.RootCertified)

let o2_false_in_every_root (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema (triangle_document hosted_triangle) i) =
  o2_certified ();
  RD.lemma_root_certified u PT.core_schema (triangle_document hosted_triangle) i

(* The same document with a mutant clause in place of the triangle clause
   stays open: the clause is checked by no kernel, and the unit resolution
   that reads it is no longer a consequence either. *)
let is_pending (v:RD.root_verdict) : bool = RD.RootPending? v
let uncertified (v:RD.root_verdict) : bool = not (RD.RootCertified? v)

let o2_mutant_documents ()
  : Lemma (is_pending (RD.check_root_document PT.core_schema (triangle_document (or2 (neg (eq c two)) (lt c two)))) /\
           is_pending (RD.check_root_document PT.core_schema (triangle_document (or2 (neg (eq c two)) (le d two))))) =
  assert_norm (is_pending (RD.check_root_document PT.core_schema (triangle_document (or2 (neg (eq c two)) (lt c two)))));
  assert_norm (is_pending (RD.check_root_document PT.core_schema (triangle_document (or2 (neg (eq c two)) (le d two)))))

(* The gate of a schema registering a datatype named Real: the clause stays
   open there. *)
let o2_gate_closed ()
  : Lemma (not (RL.real_primitive RR.real_datatype_schema) /\
           pending_of RR.real_datatype_schema (th_node hosted_triangle) == Some 1) =
  RR.lemma_real_datatype_refused ();
  assert_norm (pending_of RR.real_datatype_schema (th_node hosted_triangle) == Some 1)

(* ---------------------------------------------------------------------- *)
(* O3. Real equation rewrites                                               *)
(* ---------------------------------------------------------------------- *)

let rewrite_node (a b:expr) : U.proof_node =
  { U.kind = U.RewriteRule; conclusion = U.Equal a b; premises = [] }

(* The previous decision of real_equivalent (numeric and commuted-product
   identities and the comparison constraints, which have no equation). *)
let previous_equivalent (a b:expr) : bool =
  Some? (expression_budget 256 a) && Some? (expression_budget 256 b) &&
  ((get_sort a = LA.real_s && get_sort b = LA.real_s &&
    (Z3ArithmeticRewrite.numeric_equivalent a b || Z3ArithmeticRewrite.commuted_product a = Some b)) ||
   Z3ArithmeticRewrite.boolean_equivalent a b)

let rewrite_checked (l r:expr) : bool =
  LIN.real_equivalent l r && not (previous_equivalent l r) &&
  SP.real_rewrite PT.core_schema (rewrite_node l r) &&
  pending_of PT.core_schema (rewrite_node l r) = Some 0

let rewrite_refused (l r:expr) : bool =
  not (LIN.real_equivalent l r) && not (SP.real_rewrite PT.core_schema (rewrite_node l r)) &&
  pending_of PT.core_schema (rewrite_node l r) = Some 1

let rbox : func_decl = RPT.box
let rproj : func_decl = RPT.proj

(* The hosted shapes: Pulse.Lib.RWLock-2 node 178 (a product renormalized
   with the coefficient on the other side), Pulse.Lib.Borrow node 118 (the
   negated difference), Pulse.Lib.Box node 69 and the constant equations, and
   the commuted, proportional, rational, nonlinear-atom and to_real forms. *)
let eq_positives : list (expr & expr) = [
  (eq c (times two d), eq (plus c (times (num (-2)) d)) zero);
  (eq c (times two d), eq (plus (times two d) (times m1 c)) zero);
  (eq c d, eq (diff c d) zero);
  (eq c d, eq d c);
  (eq c d, eq (plus (times three c) (times (num (-3)) d)) zero);
  (eq (times (rat 1 2) c) (times (rat 1 2) d), eq c d);
  (eq (times (rat 1 2) c) (rat 1 2), eq c (num 1));
  (eq (times c d) e, eq e (times c d));
  (eq (quotient c d) e, eq (plus e (times m1 (quotient c d))) zero);
  (eq (to_real i) c, eq c (to_real i));
  (eq (plus c d) (plus d (times two e)), eq (plus c (times (num (-2)) e)) zero);
  (eq two zero, R.false_expr);
  (eq zero zero, R.true_expr);
  (eq (rat 1 2) (rat 2 4), R.true_expr);
  (eq (plus c (times m1 c)) zero, R.true_expr);
  (eq c c, R.true_expr);
  (eq (plus two three) (num 5), R.true_expr);
  (R.false_expr, eq two zero);
  (R.true_expr, eq (rat 1 3) (rat 2 6))
]

let o3_positives () : Lemma (L.for_all (fun (lr:expr & expr) -> rewrite_checked (fst lr) (snd lr)) eq_positives) =
  assert_norm (L.for_all (fun (lr:expr & expr) -> rewrite_checked (fst lr) (snd lr)) eq_positives)

(* Wrong sign, offset, target, coefficient and constant, a different
   relation, a nonlinear atom dropped, a counterfeit `=` and a twin atom, and
   an Int equation (the Int path is a separate decision). *)
let iplus (a b:expr) : expr = App (TR.plus_decl integer) [a; b]
let itimes (a b:expr) : expr = App (TR.times_decl integer) [a; b]
let inum (n:int) : expr = App (TR.int_numeral n) []

let eq_mutants : list (expr & expr) = [
  (eq c d, eq (plus c d) zero);
  (eq c d, eq (diff c d) (num 1));
  (eq c d, eq (diff c e) zero);
  (eq c (times two d), eq (plus c (times (num (-3)) d)) zero);
  (eq c d, eq (diff c d) two);
  (eq two zero, R.true_expr);
  (eq two two, R.false_expr);
  (eq (rat 1 2) (rat 2 4), R.false_expr);
  (eq c d, R.true_expr);
  (eq c d, le (diff c d) zero);
  (eq c d, neg (eq c d));
  (eq (times c d) zero, eq c zero);
  (fake_eq c d, eq (diff c d) zero);
  (eq c d, eq (diff c_twin d) zero);
  (eq (to_real i) c, eq (to_real j) c)
]

let o3_mutants () : Lemma (L.for_all (fun (lr:expr & expr) -> rewrite_refused (fst lr) (snd lr)) eq_mutants) =
  assert_norm (L.for_all (fun (lr:expr & expr) -> rewrite_refused (fst lr) (snd lr)) eq_mutants)

(* Int equations are outside the Real check (the Int path is a separate
   decision): neither real_equivalent nor real_rewrite reads them. *)
let int_equation_controls : list (expr & expr) = [
  (eq i j, eq (iplus i (itimes (inum (-1)) j)) (inum 0));
  (eq (inum 2) (inum 0), R.false_expr)
]

let o3_int_outside ()
  : Lemma (L.for_all (fun (lr:expr & expr) ->
             not (LIN.real_equivalent (fst lr) (snd lr)) && not (SP.real_rewrite PT.core_schema (rewrite_node (fst lr) (snd lr))))
             int_equation_controls) =
  assert_norm (L.for_all (fun (lr:expr & expr) ->
                 not (LIN.real_equivalent (fst lr) (snd lr)) && not (SP.real_rewrite PT.core_schema (rewrite_node (fst lr) (snd lr))))
                 int_equation_controls)

(* Valid rewrites outside the fragment (a negated equation, a to_real
   difference) are SHAPE controls, and the Real gate of a schema registering
   a datatype named Real is closed. *)
let o3_unsupported ()
  : Lemma (rewrite_refused (neg (eq c d)) (neg (eq (diff c d) zero)) /\
           pending_of RR.real_datatype_schema (rewrite_node (eq c d) (eq (diff c d) zero)) == Some 1) =
  RR.lemma_real_datatype_refused ();
  assert_norm (rewrite_refused (neg (eq c d)) (neg (eq (diff c d) zero)));
  assert_norm (pending_of RR.real_datatype_schema (rewrite_node (eq c d) (eq (diff c d) zero)) == Some 1)

(* A refutation using an equation rewrite and one using a constant equation:
   RootCertified on both routes, false in every root model; the wrong-sign
   mutants are not certified. *)
let eq_rewrite_document (rhs:expr) : P.document =
  doc [eq c d; neg (eq (diff c d) zero)]
      [entry U.Asserted (eq c d) [];
       entry U.Asserted (neg (eq (diff c d) zero)) [];
       entry U.RewriteRule (eq (eq c d) rhs) [];
       entry U.ModusPonens rhs [0; 2];
       entry U.UnitResolution R.false_expr [3; 1]]
      4

let constant_rewrite_document (r:expr) : P.document =
  doc [eq two zero]
      [entry U.Asserted (eq two zero) [];
       entry U.RewriteRule (eq (eq two zero) r) [];
       entry U.ModusPonens r [0; 1]]
      2

let o3_documents ()
  : Lemma (RD.check_root_document PT.core_schema (eq_rewrite_document (eq (diff c d) zero)) == RD.RootCertified /\
           RD.check_root_document_epsilon PT.core_schema (eq_rewrite_document (eq (diff c d) zero)) == RD.RootCertified /\
           RD.check_root_document PT.core_schema (constant_rewrite_document R.false_expr) == RD.RootCertified /\
           uncertified (RD.check_root_document PT.core_schema (eq_rewrite_document (eq (plus c d) zero))) /\
           uncertified (RD.check_root_document PT.core_schema (constant_rewrite_document R.true_expr))) =
  assert_norm (RD.check_root_document PT.core_schema (eq_rewrite_document (eq (diff c d) zero)) == RD.RootCertified);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (eq_rewrite_document (eq (diff c d) zero)) == RD.RootCertified);
  assert_norm (RD.check_root_document PT.core_schema (constant_rewrite_document R.false_expr) == RD.RootCertified);
  assert_norm (uncertified (RD.check_root_document PT.core_schema (eq_rewrite_document (eq (plus c d) zero))));
  assert_norm (uncertified (RD.check_root_document PT.core_schema (constant_rewrite_document R.true_expr)))

let o3_documents_false_in_every_root (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures falsified u PT.core_schema (eq_rewrite_document (eq (diff c d) zero)) i /\
                   falsified u PT.core_schema (constant_rewrite_document R.false_expr) i) =
  o3_documents ();
  RD.lemma_root_certified u PT.core_schema (eq_rewrite_document (eq (diff c d) zero)) i;
  RD.lemma_root_certified u PT.core_schema (constant_rewrite_document R.false_expr) i

(* The quant-intro leaf (Pulse.Lib.RWLock-2): under two Term binders the
   equation rewrite replays with the Real gate and stays pending without it
   and in every mutant. *)
let box_product : expr = App rproj [App rbox [RPT.rtimes (RPT.rnum 2) RPT.p0]]
let leaf_l : expr = RPT.eq box_product (RPT.rtimes (RPT.rnum 2) RPT.p0)
let leaf_r : expr = RPT.eq (RPT.rplus box_product (RPT.rtimes (RPT.rnum (-2)) RPT.p0)) (RPT.rnum 0)

let leaf_cert (r:expr) : U.binder_certificate =
  RPT.cert [RPT.be "rewrite" (RPT.eq leaf_l r) [];
            RPT.bq "quant-intro" [RPT.term; RPT.term]
              (RPT.eq (RPT.forall_ [RPT.term; RPT.term] leaf_l) (RPT.forall_ [RPT.term; RPT.term] r)) [0]]
    1

let leaf_lhs : expr = RPT.forall_ [RPT.term; RPT.term] leaf_l
let leaf_rhs : expr = RPT.forall_ [RPT.term; RPT.term] leaf_r

let o3_leaf ()
  : Lemma (RPT.gate leaf_l leaf_r /\ not (RPT.old leaf_l leaf_r) /\ not (NR.real_rewrite_ok false leaf_l leaf_r) /\
           RPT.gated (leaf_cert leaf_r) leaf_lhs leaf_rhs /\ RPT.ungated_pending (leaf_cert leaf_r) leaf_lhs leaf_rhs) =
  assert_norm (RPT.gate leaf_l leaf_r);
  assert_norm (not (RPT.old leaf_l leaf_r));
  assert_norm (not (NR.real_rewrite_ok false leaf_l leaf_r));
  assert_norm (RPT.gated (leaf_cert leaf_r) leaf_lhs leaf_rhs);
  assert_norm (RPT.ungated_pending (leaf_cert leaf_r) leaf_lhs leaf_rhs)

let wrong_sign_r : expr = RPT.eq (RPT.rplus box_product (RPT.rtimes (RPT.rnum 2) RPT.p0)) (RPT.rnum 0)
let wrong_offset_r : expr = RPT.eq (RPT.rplus box_product (RPT.rtimes (RPT.rnum (-2)) RPT.p0)) (RPT.rnum 1)
let wrong_target_r : expr = RPT.eq (RPT.rplus box_product (RPT.rtimes (RPT.rnum (-2)) RPT.p1)) (RPT.rnum 0)

let o3_leaf_mutants ()
  : Lemma (not (RPT.gate leaf_l wrong_sign_r) /\ not (RPT.gate leaf_l wrong_offset_r) /\
           not (RPT.gate leaf_l wrong_target_r) /\
           RPT.gated_pending (leaf_cert wrong_sign_r) leaf_lhs (RPT.forall_ [RPT.term; RPT.term] wrong_sign_r) /\
           RPT.gated_pending (leaf_cert wrong_offset_r) leaf_lhs (RPT.forall_ [RPT.term; RPT.term] wrong_offset_r)) =
  assert_norm (not (RPT.gate leaf_l wrong_sign_r));
  assert_norm (not (RPT.gate leaf_l wrong_offset_r));
  assert_norm (not (RPT.gate leaf_l wrong_target_r));
  assert_norm (RPT.gated_pending (leaf_cert wrong_sign_r) leaf_lhs (RPT.forall_ [RPT.term; RPT.term] wrong_sign_r));
  assert_norm (RPT.gated_pending (leaf_cert wrong_offset_r) leaf_lhs (RPT.forall_ [RPT.term; RPT.term] wrong_offset_r))

(* The replay holds in every Sorted model with the Real laws, hence in every
   root model (the Real laws are derived from R2 of the same model). *)
let o3_leaf_valid (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq_model:T.scalar_model base) (other:V.interpretation base (S.signature s))
  : Lemma (requires Z3SortedQuantifier.forall_model s bc other /\ Z3SortedSkolem.exists_model s bc other /\
                    RL.real_model s bc eq_model other)
          (ensures NR.holds_at s bc eq_model other [] (T.empty_environment (S.signature s)) (U.Equal leaf_lhs leaf_rhs)) =
  o3_leaf ();
  NR.lemma_replay_with s bc eq_model other true [] (leaf_cert leaf_r) (U.Equal leaf_lhs leaf_rhs)

let o3_leaf_root (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch)
  : Lemma (requires TR.root_model u sch i /\ RL.real_primitive sch)
          (ensures NR.holds_at sch (TR.booleans u) (SR.root_scalars u) i [] (T.empty_environment (S.signature sch))
                     (U.Equal leaf_lhs leaf_rhs)) =
  RD.lemma_forall_model u sch i;
  RD.lemma_exists_model u sch i;
  RR.lemma_root_real_model u sch i;
  o3_leaf_valid sch (TR.booleans u) (SR.root_scalars u) i

(* ---------------------------------------------------------------------- *)
(* O4. Counter-models                                                       *)
(* ---------------------------------------------------------------------- *)

(* Each false mutant of O1 and O3 is FALSE in the standard root model of
   every u (Z3SortedRealRoot: R1-R6 and the Real laws jointly, over a schema
   whose Real gate is open), at a concrete typed environment of three Real
   variables x = Var 0, y = Var 1, z = Var 2. The model is the schema's
   inhabitant for every free symbol; the clauses use only canonical operators
   and variables, so the values are the Real laws' values. *)

let esch : S.checked_schema = RR.empty_schema

unfold let rscope : list sort = [TR.real_s; TR.real_s; TR.real_s]

let vx : expr = Var 0 real
let vy : expr = Var 1 real
let vz : expr = Var 2 real

let uf0 (u:TR.uninterpreted) : TR.symbols u esch = {
  TR.apply = (fun f _ -> S.value_inhabitant esch (TR.default_value u) f.range);
  TR.lambda = (fun bound t _ -> S.value_inhabitant esch (TR.default_value u) (ArraySort bound t));
}

let cm (u:TR.uninterpreted) : TR.interp u esch = TR.standard u esch (uf0 u)

let env3 (u:TR.uninterpreted) (a b c':real)
  : V.environment (TR.carrier u) (S.signature esch) rscope =
  RR.lemma_empty_primitive ();
  fun (n:nat{n < 3}) -> V.Scalar TR.real_s ((if n = 0 then a else if n = 1 then b else c') <: TR.carrier u TR.real_s)

let tv (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) rscope) (e:expr) : GTot bool =
  T.truth_at esch (TR.booleans u) (SR.root_scalars u) (cm u) rscope rho e

let rv (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) rscope) (e:expr) : GTot real =
  RL.real_at esch (TR.booleans u) (SR.root_scalars u) (cm u) (RR.root_reals u) rscope rho e

let lemma_cm (u:TR.uninterpreted)
  : Lemma (TR.root_model u esch (cm u) /\
           RL.real_laws esch (TR.booleans u) (SR.root_scalars u) (cm u) (RR.root_reals u)) =
  RR.lemma_empty_primitive ();
  RR.lemma_standard_real_root u esch (uf0 u)

let lemma_vars (u:TR.uninterpreted) (a b c':real)
  : Lemma (rv u (env3 u a b c') vx == a /\ rv u (env3 u a b c') vy == b /\ rv u (env3 u a b c') vz == c') =
  RR.lemma_empty_primitive ();
  assert_norm (D.scoped rscope vx /\ D.scoped rscope vy /\ D.scoped rscope vz)

let lemma_num (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) rscope) (n:int) (x:expr)
  : Lemma (requires D.scoped rscope x /\ LIN.real_numeral n x) (ensures rv u rho x == of_int n) =
  lemma_cm u;
  LIN.lemma_real_numeral_value esch (TR.booleans u) (SR.root_scalars u) (cm u) (RR.root_reals u) rscope rho n x

let lemma_diff (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) rscope) (x a b:expr)
  : Lemma (requires D.scoped rscope x /\ LIN.real_difference x == Some (a, b))
          (ensures rv u rho x == rv u rho a -. rv u rho b) =
  lemma_cm u;
  LIN.lemma_real_difference esch (TR.booleans u) (SR.root_scalars u) (cm u) (RR.root_reals u) rscope rho x a b

let lemma_binary (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) rscope)
                 (f:func_decl) (a b:expr) (o:LA.operation)
  : Lemma (requires D.scoped rscope (App f [a; b]) /\ RL.classify f == RL.Calculate o)
          (ensures (o == LA.Add ==> rv u rho (App f [a; b]) == rv u rho a +. rv u rho b) /\
                   (o == LA.Mul ==> rv u rho (App f [a; b]) == rv u rho a *. rv u rho b)) =
  lemma_cm u;
  RL.lemma_real_binary_at esch (TR.booleans u) (SR.root_scalars u) (cm u) (RR.root_reals u) rscope rho f a b o

let lemma_atom (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) rscope)
               (x:expr) (rel:LA.relation) (l r:expr)
  : Lemma (requires D.scoped rscope x /\ LA.comparison x == Some (rel, l, r) /\ get_sort l == real)
          (ensures tv u rho x <==> E.numeric_relation rel (rv u rho l) (rv u rho r)) =
  lemma_cm u;
  LIN.lemma_comparison esch (TR.booleans u) (SR.root_scalars u) (cm u) (RR.root_reals u) rscope rho x l r rel;
  LIN.lemma_numeric_at_real esch (TR.booleans u) (SR.root_scalars u) (cm u) (RR.root_reals u) rscope rho l;
  LIN.lemma_numeric_at_real esch (TR.booleans u) (SR.root_scalars u) (cm u) (RR.root_reals u) rscope rho r

(* not (x = y) \/ cc is false when x and y have the same value and cc is false. *)
let lemma_triangle_false (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) rscope)
                         (x y cc:expr)
  : Lemma (requires D.scoped rscope (or2 (neg (eq x y)) cc) /\ D.scoped rscope (neg (eq x y)) /\
                    D.scoped rscope (eq x y) /\ get_sort x == real /\
                    rv u rho x == rv u rho y /\ not (tv u rho cc))
          (ensures not (tv u rho (or2 (neg (eq x y)) cc))) =
  lemma_cm u;
  assert_norm (T.classify R.not_decl == T.Negation);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [neg (eq x y); cc]) == T.Nary B.Or);
  NR.lemma_truth_not esch (TR.booleans u) (SR.root_scalars u) (cm u) rscope rho R.not_decl (eq x y);
  lemma_atom u rho (eq x y) LA.Eq x y;
  NR.lemma_truth_or2 esch (TR.booleans u) (SR.root_scalars u) (cm u) rscope rho
    (BR.connective_decl BR.Disjunction [neg (eq x y); cc]) (neg (eq x y)) cc B.Or

(* (x = y) \/ not c1 \/ not c2 is false when x and y differ and c1 and c2 hold. *)
let lemma_geval3 (rho:expr -> GTot bool) (a b c':expr)
  : Lemma (B.geval_args rho B.Or [B.Atom a; B.Atom b; B.Atom c'] == (rho a || (rho b || (rho c' || false)))) =
  assert_norm (B.geval_args rho B.Or [B.Atom a; B.Atom b; B.Atom c'] == (rho a || (rho b || (rho c' || false))))

let lemma_antisymmetric_false (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) rscope)
                              (x y c1 c2:expr)
  : Lemma (requires D.scoped rscope (or3 (eq x y) (neg c1) (neg c2)) /\ D.scoped rscope (eq x y) /\
                    D.scoped rscope (neg c1) /\ D.scoped rscope (neg c2) /\ D.scoped rscope c1 /\
                    D.scoped rscope c2 /\ get_sort x == real /\
                    ~(rv u rho x == rv u rho y) /\ tv u rho c1 /\ tv u rho c2)
          (ensures not (tv u rho (or3 (eq x y) (neg c1) (neg c2)))) =
  lemma_cm u;
  assert_norm (T.classify R.not_decl == T.Negation);
  assert_norm (T.classify (BR.connective_decl BR.Disjunction [eq x y; neg c1; neg c2]) == T.Nary B.Or);
  NR.lemma_truth_not esch (TR.booleans u) (SR.root_scalars u) (cm u) rscope rho R.not_decl c1;
  NR.lemma_truth_not esch (TR.booleans u) (SR.root_scalars u) (cm u) rscope rho R.not_decl c2;
  lemma_atom u rho (eq x y) LA.Eq x y;
  NR.lemma_truth_nary esch (TR.booleans u) (SR.root_scalars u) (cm u) rscope rho
    (BR.connective_decl BR.Disjunction [eq x y; neg c1; neg c2]) [eq x y; neg c1; neg c2] B.Or;
  lemma_geval3 (T.truth_at esch (TR.booleans u) (SR.root_scalars u) (cm u) rscope rho) (eq x y) (neg c1) (neg c2)

(* A rewrite (= a b) between Boolean terms of different truth is false. *)
let lemma_iff_false (u:TR.uninterpreted) (rho:V.environment (TR.carrier u) (S.signature esch) rscope) (a b:expr)
  : Lemma (requires D.scoped rscope a /\ D.scoped rscope b /\ get_sort a == bool_sort /\ get_sort b == bool_sort /\
                    tv u rho a <> tv u rho b)
          (ensures not (tv u rho (eq a b))) =
  lemma_cm u;
  T.lemma_boolean_equality_at esch (TR.booleans u) (SR.root_scalars u) (cm u) rscope rho a b

let r_one : expr = num 1

(* Strict: x = y = 0 makes x - y < 0 false. *)
let strict_clause : expr = or2 (neg (eq vx vy)) (lt (diff vx vy) zero)

let o4_strict (u:TR.uninterpreted)
  : Lemma (not (tv u (env3 u 0.0R 0.0R 0.0R) strict_clause)) =
  let rho = env3 u 0.0R 0.0R 0.0R in
  lemma_vars u 0.0R 0.0R 0.0R;
  assert_norm (D.scoped rscope strict_clause /\ D.scoped rscope (neg (eq vx vy)) /\ D.scoped rscope (eq vx vy) /\
               D.scoped rscope (lt (diff vx vy) zero) /\ D.scoped rscope (diff vx vy));
  assert_norm (LIN.real_difference (diff vx vy) == Some (vx, vy) /\ LIN.real_numeral 0 zero);
  assert_norm (LA.comparison (lt (diff vx vy) zero) == Some (LA.Lt, diff vx vy, zero));
  lemma_diff u rho (diff vx vy) vx vy;
  lemma_num u rho 0 zero;
  lemma_atom u rho (lt (diff vx vy) zero) LA.Lt (diff vx vy) zero;
  lemma_triangle_false u rho vx vy (lt (diff vx vy) zero)

(* Wrong coefficient: x = y = 1 makes x + 1*y <= 0 (2 <= 0) and
   x + (-2)*y >= 0 (-1 >= 0) false. *)
let coefficient_one_clause : expr = or2 (neg (eq vx vy)) (le (plus vx (times r_one vy)) zero)
let coefficient_two_clause : expr = or2 (neg (eq vx vy)) (ge (plus vx (times (num (-2)) vy)) zero)

let o4_coefficient (u:TR.uninterpreted)
  : Lemma (not (tv u (env3 u 1.0R 1.0R 0.0R) coefficient_one_clause) /\
           not (tv u (env3 u 1.0R 1.0R 0.0R) coefficient_two_clause)) =
  let rho = env3 u 1.0R 1.0R 0.0R in
  lemma_vars u 1.0R 1.0R 0.0R;
  RL.lemma_classify_canonical ();
  assert_norm (RL.classify (TR.plus_decl real) == RL.Calculate LA.Add /\ RL.classify (TR.times_decl real) == RL.Calculate LA.Mul);
  assert_norm (D.scoped rscope coefficient_one_clause /\ D.scoped rscope (neg (eq vx vy)) /\ D.scoped rscope (eq vx vy) /\
               D.scoped rscope (le (plus vx (times r_one vy)) zero) /\ D.scoped rscope (plus vx (times r_one vy)) /\
               D.scoped rscope (times r_one vy));
  assert_norm (LIN.real_numeral 1 r_one /\ LIN.real_numeral 0 zero);
  assert_norm (LA.comparison (le (plus vx (times r_one vy)) zero) == Some (LA.Le, plus vx (times r_one vy), zero));
  lemma_num u rho 1 r_one;
  lemma_num u rho 0 zero;
  lemma_binary u rho (TR.times_decl real) r_one vy LA.Mul;
  lemma_binary u rho (TR.plus_decl real) vx (times r_one vy) LA.Add;
  lemma_atom u rho (le (plus vx (times r_one vy)) zero) LA.Le (plus vx (times r_one vy)) zero;
  lemma_triangle_false u rho vx vy (le (plus vx (times r_one vy)) zero);
  assert_norm (D.scoped rscope coefficient_two_clause /\ D.scoped rscope (ge (plus vx (times (num (-2)) vy)) zero) /\
               D.scoped rscope (plus vx (times (num (-2)) vy)) /\ D.scoped rscope (times (num (-2)) vy));
  assert_norm (LIN.real_numeral (-2) (num (-2)));
  assert_norm (LA.comparison (ge (plus vx (times (num (-2)) vy)) zero) ==
               Some (LA.Ge, plus vx (times (num (-2)) vy), zero));
  lemma_num u rho (-2) (num (-2));
  lemma_binary u rho (TR.times_decl real) (num (-2)) vy LA.Mul;
  lemma_binary u rho (TR.plus_decl real) vx (times (num (-2)) vy) LA.Add;
  lemma_atom u rho (ge (plus vx (times (num (-2)) vy)) zero) LA.Ge (plus vx (times (num (-2)) vy)) zero;
  lemma_triangle_false u rho vx vy (ge (plus vx (times (num (-2)) vy)) zero)

let minus_one : real = 0.0R -. 1.0R

(* Wrong target: x = y = 0 and z = -1 make x - z <= 0 (1 <= 0) false. *)
let target_clause : expr = or2 (neg (eq vx vy)) (le (diff vx vz) zero)

let o4_target (u:TR.uninterpreted)
  : Lemma (not (tv u (env3 u 0.0R 0.0R minus_one) target_clause)) =
  let rho = env3 u 0.0R 0.0R minus_one in
  lemma_vars u 0.0R 0.0R minus_one;
  assert_norm (D.scoped rscope target_clause /\ D.scoped rscope (neg (eq vx vy)) /\ D.scoped rscope (eq vx vy) /\
               D.scoped rscope (le (diff vx vz) zero) /\ D.scoped rscope (diff vx vz));
  assert_norm (LIN.real_difference (diff vx vz) == Some (vx, vz) /\ LIN.real_numeral 0 zero);
  assert_norm (LA.comparison (le (diff vx vz) zero) == Some (LA.Le, diff vx vz, zero));
  lemma_diff u rho (diff vx vz) vx vz;
  lemma_num u rho 0 zero;
  lemma_atom u rho (le (diff vx vz) zero) LA.Le (diff vx vz) zero;
  lemma_triangle_false u rho vx vy (le (diff vx vz) zero)

(* Same-orientation bounds: x - y <= 0 and y - x >= 0 both hold at x = 0,
   y = 1, where x = y does not. *)
let same_orientation_clause : expr =
  or3 (eq vx vy) (neg (le (diff vx vy) zero)) (neg (ge (diff vy vx) zero))

let o4_same_orientation (u:TR.uninterpreted)
  : Lemma (not (tv u (env3 u 0.0R 1.0R 0.0R) same_orientation_clause)) =
  let rho = env3 u 0.0R 1.0R 0.0R in
  lemma_vars u 0.0R 1.0R 0.0R;
  assert_norm (D.scoped rscope same_orientation_clause /\ D.scoped rscope (eq vx vy) /\
               D.scoped rscope (neg (le (diff vx vy) zero)) /\ D.scoped rscope (neg (ge (diff vy vx) zero)) /\
               D.scoped rscope (le (diff vx vy) zero) /\ D.scoped rscope (ge (diff vy vx) zero) /\
               D.scoped rscope (diff vx vy) /\ D.scoped rscope (diff vy vx));
  assert_norm (LIN.real_difference (diff vx vy) == Some (vx, vy) /\ LIN.real_difference (diff vy vx) == Some (vy, vx) /\
               LIN.real_numeral 0 zero);
  assert_norm (LA.comparison (le (diff vx vy) zero) == Some (LA.Le, diff vx vy, zero) /\
               LA.comparison (ge (diff vy vx) zero) == Some (LA.Ge, diff vy vx, zero));
  lemma_diff u rho (diff vx vy) vx vy;
  lemma_diff u rho (diff vy vx) vy vx;
  lemma_num u rho 0 zero;
  lemma_atom u rho (le (diff vx vy) zero) LA.Le (diff vx vy) zero;
  lemma_atom u rho (ge (diff vy vx) zero) LA.Ge (diff vy vx) zero;
  lemma_antisymmetric_false u rho vx vy (le (diff vx vy) zero) (ge (diff vy vx) zero)

(* The rewrite mutants: (x = y) = (x + y = 0) at x = y = 1, and
   (x = y) = (x - y = 1) at x = y = 0 (equation sides of different truth),
   and (2 = 0) = true (the constant 2 is not 0). *)
let o4_rewrite_sign (u:TR.uninterpreted)
  : Lemma (not (tv u (env3 u 1.0R 1.0R 0.0R) (eq (eq vx vy) (eq (plus vx vy) zero)))) =
  let rho = env3 u 1.0R 1.0R 0.0R in
  lemma_vars u 1.0R 1.0R 0.0R;
  RL.lemma_classify_canonical ();
  assert_norm (RL.classify (TR.plus_decl real) == RL.Calculate LA.Add);
  assert_norm (D.scoped rscope (eq (eq vx vy) (eq (plus vx vy) zero)) /\ D.scoped rscope (eq vx vy) /\
               D.scoped rscope (eq (plus vx vy) zero) /\ D.scoped rscope (plus vx vy));
  assert_norm (LIN.real_numeral 0 zero);
  assert_norm (LA.comparison (eq vx vy) == Some (LA.Eq, vx, vy) /\
               LA.comparison (eq (plus vx vy) zero) == Some (LA.Eq, plus vx vy, zero));
  lemma_num u rho 0 zero;
  lemma_binary u rho (TR.plus_decl real) vx vy LA.Add;
  lemma_atom u rho (eq vx vy) LA.Eq vx vy;
  lemma_atom u rho (eq (plus vx vy) zero) LA.Eq (plus vx vy) zero;
  lemma_iff_false u rho (eq vx vy) (eq (plus vx vy) zero)

let o4_rewrite_offset (u:TR.uninterpreted)
  : Lemma (not (tv u (env3 u 0.0R 0.0R 0.0R) (eq (eq vx vy) (eq (diff vx vy) r_one)))) =
  let rho = env3 u 0.0R 0.0R 0.0R in
  lemma_vars u 0.0R 0.0R 0.0R;
  assert_norm (D.scoped rscope (eq (eq vx vy) (eq (diff vx vy) r_one)) /\ D.scoped rscope (eq vx vy) /\
               D.scoped rscope (eq (diff vx vy) r_one) /\ D.scoped rscope (diff vx vy));
  assert_norm (LIN.real_difference (diff vx vy) == Some (vx, vy) /\ LIN.real_numeral 1 r_one);
  assert_norm (LA.comparison (eq vx vy) == Some (LA.Eq, vx, vy) /\
               LA.comparison (eq (diff vx vy) r_one) == Some (LA.Eq, diff vx vy, r_one));
  lemma_diff u rho (diff vx vy) vx vy;
  lemma_num u rho 1 r_one;
  lemma_atom u rho (eq vx vy) LA.Eq vx vy;
  lemma_atom u rho (eq (diff vx vy) r_one) LA.Eq (diff vx vy) r_one;
  lemma_iff_false u rho (eq vx vy) (eq (diff vx vy) r_one)

let o4_rewrite_constant (u:TR.uninterpreted)
  : Lemma (not (tv u (env3 u 0.0R 0.0R 0.0R) (eq (eq two zero) R.true_expr))) =
  let rho = env3 u 0.0R 0.0R 0.0R in
  assert_norm (D.scoped rscope (eq (eq two zero) R.true_expr) /\ D.scoped rscope (eq two zero) /\
               D.scoped rscope R.true_expr);
  assert_norm (LIN.real_numeral 2 two /\ LIN.real_numeral 0 zero);
  assert_norm (LA.comparison (eq two zero) == Some (LA.Eq, two, zero));
  assert_norm (NR.constant_of R.true_expr true);
  lemma_num u rho 2 two;
  lemma_num u rho 0 zero;
  lemma_atom u rho (eq two zero) LA.Eq two zero;
  lemma_cm u;
  NR.lemma_truth_constant esch (TR.booleans u) (SR.root_scalars u) (cm u) rscope rho R.true_expr true;
  lemma_iff_false u rho (eq two zero) R.true_expr

(* ---------------------------------------------------------------------- *)
(* O5. The laws in every Sorted model with the Real laws                    *)
(* ---------------------------------------------------------------------- *)

(* An accepted clause is true, and an accepted equation rewrite is an
   identity, in every root model over a schema whose Real gate is open: the
   Real laws are derived from R2 of the same model, never assumed. *)
let o5_clause_in_every_root (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (clause:expr)
  : Lemma (requires TR.root_model u sch i /\ RL.real_primitive sch /\ D.scoped [] clause /\
                    get_sort clause == bool_sort /\ SP.real_order_clause clause)
          (ensures T.truth sch (TR.booleans u) (SR.root_scalars u) i clause) =
  RR.lemma_root_real_laws u sch i;
  SP.lemma_real_order_clause sch (TR.booleans u) (SR.root_scalars u) i (RR.root_reals u) clause

let o5_equation_in_every_root (u:TR.uninterpreted) (sch:S.checked_schema) (i:TR.interp u sch) (a b:expr)
  : Lemma (requires TR.root_model u sch i /\ RL.real_primitive sch /\ D.scoped [] a /\ D.scoped [] b /\
                    LIN.real_equivalent a b)
          (ensures T.evaluate sch (TR.booleans u) (SR.root_scalars u) i a ==
                   T.evaluate sch (TR.booleans u) (SR.root_scalars u) i b) =
  RR.lemma_root_real_laws u sch i;
  LIN.lemma_real_equivalent sch (TR.booleans u) (SR.root_scalars u) i (RR.root_reals u) []
    (T.empty_environment (S.signature sch)) a b

let antisymmetric_instance : expr = or3 (eq c d) (neg (le (diff c d) zero)) (neg (ge (diff c d) zero))
let product_instance : expr = or2 (neg (eq c (times two d))) (ge (diff c (times two d)) zero)

let o5_instances (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures T.truth PT.core_schema (TR.booleans u) (SR.root_scalars u) i hosted_triangle /\
                   T.truth PT.core_schema (TR.booleans u) (SR.root_scalars u) i antisymmetric_instance /\
                   T.truth PT.core_schema (TR.booleans u) (SR.root_scalars u) i product_instance /\
                   T.same_value PT.core_schema (TR.booleans u) (SR.root_scalars u) i
                     (eq c (times two d)) (eq (plus c (times (num (-2)) d)) zero) /\
                   T.same_value PT.core_schema (TR.booleans u) (SR.root_scalars u) i (eq two zero) R.false_expr) =
  assert_norm (RL.real_primitive PT.core_schema);
  assert_norm (D.scoped [] hosted_triangle /\ SP.real_order_clause hosted_triangle);
  assert_norm (D.scoped [] antisymmetric_instance /\ SP.real_order_clause antisymmetric_instance);
  assert_norm (D.scoped [] product_instance /\ SP.real_order_clause product_instance);
  assert_norm (D.scoped [] (eq c (times two d)) /\ D.scoped [] (eq (plus c (times (num (-2)) d)) zero) /\
               LIN.real_equivalent (eq c (times two d)) (eq (plus c (times (num (-2)) d)) zero));
  assert_norm (D.scoped [] (eq two zero) /\ D.scoped [] R.false_expr /\ LIN.real_equivalent (eq two zero) R.false_expr);
  o5_clause_in_every_root u PT.core_schema i hosted_triangle;
  o5_clause_in_every_root u PT.core_schema i antisymmetric_instance;
  o5_clause_in_every_root u PT.core_schema i product_instance;
  o5_equation_in_every_root u PT.core_schema i (eq c (times two d)) (eq (plus c (times (num (-2)) d)) zero);
  o5_equation_in_every_root u PT.core_schema i (eq two zero) R.false_expr;
  T.lemma_same_value PT.core_schema (TR.booleans u) (SR.root_scalars u) i
    (eq c (times two d)) (eq (plus c (times (num (-2)) d)) zero);
  T.lemma_same_value PT.core_schema (TR.booleans u) (SR.root_scalars u) i (eq two zero) R.false_expr
