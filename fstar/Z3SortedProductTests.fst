module Z3SortedProductTests

(* Tests of the Int product factor permutation (Z3NnfReplay.product_permuted)
   on both Sorted paths: the rewrite leaves of quant-intro certificates
   (NR.rewrite_ok, replayed at every scope the guard assigns them) and the
   premise-free closed RewriteRule nodes (Z3SortedProof.product_rewrite).

   P1 the law's executable check (normalized): the captured
      FStar.Math.Euclid-1 node 320 leaf p1 * p0 ~ p0 * p1 with the
      native binary op_mul record, the n-ary op_arith_mul, nested and
      regrouped three-factor products, repeated factors, numeral
      coefficients and signs; and its refusals: x*y ~ x*x, a wrong
      repeated factor, coefficient and sign changes, a dropped factor,
      same-spelled twin constants, look-alike `*` declarations, Real and
      mixed sorts, and 65 factors (64 are accepted).
   P2 the law in every Sorted model at every scope and typed environment,
      instantiated in every root model (the Sorted layer over its root
      scalars) at the Int binder scope of the quant-intro certificate.
   P3 the quant-intro path: a certificate whose body leaf is the Euclid
      permutation under two Int binders is outside every other disjunct of
      check_node_cached and replays; leaf mutants stay pending; the
      refutation of the negated root equation is RootCertified, false in
      every root model, and its mutant document is pending.
   P4 the direct path: the closed node x * y = y * x is outside the old
      disjuncts and checked; its refutation is RootCertified on the plain and
      the epsilon route, false in every root model; mutant nodes and
      documents stay pending; open, premised and relabelled nodes are refused.
   P5 the false leaf x*y ~ x*x has opposite values in a standard root model:
      at x = 1, y = 2 its sides are 2 and 1.

   Every expected refusal is the checker's own verdict on a well-sorted
   input, computed by normalization; none is a parse, effect or refinement
   error. Deep, shared and wide inputs run natively (test_native_bridge.ml,
   Z3CherryTests.fst). *)

open Z3AstTheory
open Z3ValueTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3Definitions
module L = FStar.List.Tot
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module SP = Z3SortedProof
module P = Z3ProofDocument
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module NR = Z3NnfReplay
module RD = Z3SortedRootDocument
module PT = Z3SortedProofTests
module QT = Z3QuantIntroReplayTests
module QCM = Z3QuantIntroCounterModelTests
module LA = Z3LinearArithmeticAst

(* ---------------------------------------------------------------------- *)
(* Shapes                                                                   *)
(* ---------------------------------------------------------------------- *)

let integer : sort = TR.int_s
let real : sort = TR.real_s

let constant (name:string) (s:sort) (params:list int) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = params } []

let x : expr = constant "x" integer []
let y : expr = constant "y" integer []
let z : expr = constant "z" integer []
let num (n:int) : expr = App (TR.int_numeral n) []

(* The native binary Int product (op_mul, the captured leaf heads) and the
   n-ary canonical product (op_arith_mul). *)
let mul (a b:expr) : expr = App TR.native_times_int [a; b]

let rec int_sorts (n:nat) : list sort = if n = 0 then [] else integer :: int_sorts (n - 1)

let times (args:list expr) : expr =
  App { decl_name = "*"; domain = int_sorts (L.length args); range = integer;
        interp = Some op_arith_mul; int_params = [] } args

let i0 : expr = Var 0 integer
let i1 : expr = Var 1 integer

(* ---------------------------------------------------------------------- *)
(* P1. The executable check                                                 *)
(* ---------------------------------------------------------------------- *)

let euclid_l : expr = mul i1 i0
let euclid_r : expr = mul i0 i1

let positives : list (expr & expr) = [
  (euclid_l, euclid_r);
  (mul x y, mul y x);
  (times [x; y], times [y; x]);
  (mul (mul x y) z, mul z (mul y x));
  (times [x; y; z], mul (mul z x) y);
  (mul x (mul y z), mul (mul x y) z);
  (mul (mul x x) y, mul x (mul y x));
  (mul (num 2) (mul x y), mul y (mul x (num 2)));
  (mul (num (-1)) (mul x y), mul (mul y (num (-1))) x)
]

let p1_positives () : Lemma (L.for_all (fun (lr:expr & expr) -> NR.product_permuted (fst lr) (snd lr)) positives) =
  assert_norm (L.for_all (fun (lr:expr & expr) -> NR.product_permuted (fst lr) (snd lr)) positives)

(* Twins of x: the same name with an integer parameter, or with an
   interpretation tag. Look-alike `*`: an integer parameter, no
   interpretation, the binary op_mul tag at three arguments, and the n-ary
   tag over a Real domain at an Int range. None is opened: each is one
   factor, compared by exact identity. *)
let x_param : expr = constant "x" integer [7]
let x_tagged : expr = App { decl_name = "x"; domain = []; range = integer; interp = Some 99; int_params = [] } []
let mul_param (a b:expr) : expr = App ({ TR.native_times_int with int_params = [0] }) [a; b]
let mul_free (a b:expr) : expr = App ({ TR.native_times_int with interp = None }) [a; b]
let mul_ternary (a b c:expr) : expr =
  App ({ TR.native_times_int with domain = [integer; integer; integer] }) [a; b; c]
let c_real : expr = constant "c" real []
let d_real : expr = constant "d" real []
let x_real : expr = constant "x" real []
let mul_real_domain (a b:expr) : expr =
  App { decl_name = "*"; domain = [real; real]; range = integer; interp = Some op_arith_mul; int_params = [] } [a; b]
let rmul (a b:expr) : expr = App (TR.times_decl real) [a; b]

let mutants : list (expr & expr) = [
  (mul x y, mul x x);                                   (* the false x*y = x*x *)
  (mul (mul x x) y, mul (mul x y) y);                   (* wrong repeated factor *)
  (mul (num 2) (mul x y), mul (num 3) (mul y x));       (* coefficient changed *)
  (mul (num (-1)) (mul x y), mul y x);                  (* sign dropped *)
  (mul (num (-1)) (mul x y), mul (num 1) (mul y x));    (* sign changed *)
  (mul (mul x y) z, mul y x);                           (* factor dropped *)
  (mul x y, mul y x_param);                             (* twin constant (parameter) *)
  (mul x y, mul y x_tagged);                            (* twin constant (tag) *)
  (mul_param x y, mul_param y x);                       (* look-alike *, parameter *)
  (mul_free x y, mul_free y x);                         (* look-alike *, uninterpreted *)
  (mul_ternary x y z, mul_ternary z y x);               (* look-alike *, op_mul at arity 3 *)
  (mul_real_domain c_real d_real, mul_real_domain d_real c_real);  (* look-alike *, Real domain *)
  (rmul c_real d_real, rmul d_real c_real);             (* Real product: not this law *)
  (mul x y, rmul x_real (constant "y" real []))         (* mixed sorts *)
]

let p1_mutants () : Lemma (L.for_all (fun (lr:expr & expr) -> not (NR.product_permuted (fst lr) (snd lr))) mutants) =
  assert_norm (L.for_all (fun (lr:expr & expr) -> not (NR.product_permuted (fst lr) (snd lr))) mutants)

(* 64 distinct factors (twins distinguished by their parameter) are
   accepted in reverse order; 65 exceed the factor bound and are refused. *)
let rec factors (n:nat) : list expr = if n = 0 then [] else constant "v" integer [n] :: factors (n - 1)

let p1_factor_bound ()
  : Lemma (NR.product_permuted (times (factors 64)) (times (L.rev (factors 64))) /\
           not (NR.product_permuted (times (factors 65)) (times (L.rev (factors 65))))) =
  assert_norm (NR.product_permuted (times (factors 64)) (times (L.rev (factors 64))));
  assert_norm (not (NR.product_permuted (times (factors 65)) (times (L.rev (factors 65)))))

(* ---------------------------------------------------------------------- *)
(* P2. The law in every root model at the Int binder scope                  *)
(* ---------------------------------------------------------------------- *)

let scope2 : list sort = [integer; integer]

let p2_root_instance (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
                     (rho:V.environment (TR.carrier u) (S.signature PT.core_schema) scope2)
  : Lemma (NR.same_at PT.core_schema (TR.booleans u) (SR.root_scalars u) i scope2 rho euclid_l euclid_r) =
  assert_norm (NR.product_permuted euclid_l euclid_r);
  assert_norm (D.scoped scope2 euclid_l /\ D.scoped scope2 euclid_r);
  NR.lemma_product_permuted_at PT.core_schema (TR.booleans u) (SR.root_scalars u) i scope2 rho euclid_l euclid_r

(* ---------------------------------------------------------------------- *)
(* P3. The quant-intro path                                                 *)
(* ---------------------------------------------------------------------- *)

let body (l:expr) : expr = QT.le l (num 0)
let root (l:expr) : expr = QT.forall_ scope2 (body l)

let product_cert (l r:expr) : U.binder_certificate =
  QT.cert [QT.be "rewrite" (QT.eq l r) [];
           QT.be "monotonicity" (QT.eq (body l) (body r)) [0];
           QT.bq "quant-intro" scope2 (QT.eq (root l) (root r)) [1]] 2

let p3_replay ()
  : Lemma (not (QT.old_paths (QT.qi_node (product_cert euclid_l euclid_r) (root euclid_l) (root euclid_r))) /\
           QT.replays (product_cert euclid_l euclid_r) (root euclid_l) (root euclid_r) /\
           SP.check_node PT.core_schema [] (QT.qi_node (product_cert euclid_l euclid_r) (root euclid_l) (root euclid_r)) ==
             QT.checked (root euclid_l) (root euclid_r)) =
  assert_norm (not (QT.old_paths (QT.qi_node (product_cert euclid_l euclid_r) (root euclid_l) (root euclid_r))));
  assert_norm (QT.replays (product_cert euclid_l euclid_r) (root euclid_l) (root euclid_r));
  assert_norm (SP.check_node PT.core_schema [] (QT.qi_node (product_cert euclid_l euclid_r) (root euclid_l) (root euclid_r)) ==
               QT.checked (root euclid_l) (root euclid_r))

(* Leaf mutants under the same binders: x*y ~ x*x, a shifted index
   (Var 0 for Var 1), a sign change, and a look-alike `*`. *)
let leaf_pending (r:expr) : bool = QT.pending (product_cert euclid_l r) (root euclid_l) (root r)

let p3_mutants ()
  : Lemma (leaf_pending (mul i1 i1) /\ leaf_pending (mul i0 i0) /\
           leaf_pending (mul (num (-1)) (mul i0 i1)) /\ leaf_pending (mul_param i0 i1)) =
  assert_norm (leaf_pending (mul i1 i1));
  assert_norm (leaf_pending (mul i0 i0));
  assert_norm (leaf_pending (mul (num (-1)) (mul i0 i1)));
  assert_norm (leaf_pending (mul_param i0 i1))

let p3_documents ()
  : Lemma (RD.check_root_document PT.core_schema
             (QT.refutation (product_cert euclid_l euclid_r) (root euclid_l) (root euclid_r)) == RD.RootCertified /\
           RD.check_root_document PT.core_schema
             (QT.refutation (product_cert euclid_l (mul i1 i1)) (root euclid_l) (root (mul i1 i1))) == RD.RootPending 1) =
  assert_norm (RD.check_root_document PT.core_schema
                 (QT.refutation (product_cert euclid_l euclid_r) (root euclid_l) (root euclid_r)) == RD.RootCertified);
  assert_norm (RD.check_root_document PT.core_schema
                 (QT.refutation (product_cert euclid_l (mul i1 i1)) (root euclid_l) (root (mul i1 i1))) == RD.RootPending 1)

let p3_valid (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures RD.root_holds u PT.core_schema i (QT.eq (root euclid_l) (root euclid_r))) =
  p3_documents ();
  RD.lemma_root_certified u PT.core_schema (QT.refutation (product_cert euclid_l euclid_r) (root euclid_l) (root euclid_r)) i;
  assert_norm (D.scoped [] (QT.neg (QT.eq (root euclid_l) (root euclid_r))));
  QT.lemma_not_holds u i (QT.eq (root euclid_l) (root euclid_r))

let p3_standard (u:TR.uninterpreted) (uf:TR.symbols u PT.core_schema)
  : Lemma (RD.root_holds u PT.core_schema (TR.standard u PT.core_schema uf) (QT.eq (root euclid_l) (root euclid_r))) =
  TR.lemma_standard_root u PT.core_schema uf;
  p3_valid u (TR.standard u PT.core_schema uf)

(* ---------------------------------------------------------------------- *)
(* P4. The direct closed premise-free RewriteRule path                      *)
(* ---------------------------------------------------------------------- *)

let rewrite_node (a b:expr) : U.proof_node = { U.kind = U.RewriteRule; conclusion = U.Equal a b; premises = [] }

let rewrite_pending (a b:expr) : option nat =
  match SP.check_node_cached PT.core_schema [] (rewrite_node a b) with
  | Some (_, pending) -> Some pending
  | None -> None

(* not (lhs = rhs), the rewrite lhs = rhs, and unit resolution to false. *)
let rewrite_document (l r:expr) : P.document =
  let e = QT.eq l r in
  QT.doc [QT.neg e]
         [QT.entry U.Asserted (QT.neg e) []; QT.entry U.RewriteRule e []; QT.entry U.UnitResolution R.false_expr [0; 1]]
         2

let closed_positives : list (expr & expr) = L.tl positives

let node_checked (lr:expr & expr) : bool =
  SP.product_rewrite (rewrite_node (fst lr) (snd lr)) &&
  not (QT.old_paths (rewrite_node (fst lr) (snd lr))) &&
  rewrite_pending (fst lr) (snd lr) = Some 0

let p4_nodes () : Lemma (L.for_all node_checked closed_positives) =
  assert_norm (L.for_all node_checked closed_positives)

let p4_certified ()
  : Lemma (RD.check_root_document PT.core_schema (rewrite_document (mul x y) (mul y x)) == RD.RootCertified /\
           RD.check_root_document_epsilon PT.core_schema (rewrite_document (mul x y) (mul y x)) == RD.RootCertified /\
           RD.check_root_document PT.core_schema
             (rewrite_document (mul (num 2) (mul x y)) (mul y (mul x (num 2)))) == RD.RootCertified) =
  assert_norm (RD.check_root_document PT.core_schema (rewrite_document (mul x y) (mul y x)) == RD.RootCertified);
  assert_norm (RD.check_root_document_epsilon PT.core_schema (rewrite_document (mul x y) (mul y x)) == RD.RootCertified);
  assert_norm (RD.check_root_document PT.core_schema
                 (rewrite_document (mul (num 2) (mul x y)) (mul y (mul x (num 2)))) == RD.RootCertified)

let p4_valid (u:TR.uninterpreted) (i:TR.interp u PT.core_schema)
  : Lemma (requires TR.root_model u PT.core_schema i)
          (ensures RD.root_holds u PT.core_schema i (QT.eq (mul x y) (mul y x))) =
  p4_certified ();
  RD.lemma_root_certified u PT.core_schema (rewrite_document (mul x y) (mul y x)) i;
  assert_norm (D.scoped [] (QT.neg (QT.eq (mul x y) (mul y x))));
  QT.lemma_not_holds u i (QT.eq (mul x y) (mul y x))

let p4_standard (u:TR.uninterpreted) (uf:TR.symbols u PT.core_schema)
  : Lemma (RD.root_holds u PT.core_schema (TR.standard u PT.core_schema uf) (QT.eq (mul x y) (mul y x))) =
  TR.lemma_standard_root u PT.core_schema uf;
  p4_valid u (TR.standard u PT.core_schema uf)

let closed_mutants : list (expr & expr) = L.tl (L.tl (L.tl (L.tl mutants)))

let node_open (lr:expr & expr) : bool =
  not (SP.product_rewrite (rewrite_node (fst lr) (snd lr))) &&
  rewrite_pending (fst lr) (snd lr) = Some 1

let p4_mutants ()
  : Lemma (node_open (mul x y, mul x x) /\
           node_open (mul (mul x x) y, mul (mul x y) y) /\
           node_open (mul (num 2) (mul x y), mul (num 3) (mul y x)) /\
           node_open (mul x y, mul y x_param) /\
           node_open (mul_param x y, mul_param y x) /\
           RD.check_root_document PT.core_schema (rewrite_document (mul x y) (mul x x)) == RD.RootPending 1) =
  assert_norm (node_open (mul x y, mul x x));
  assert_norm (node_open (mul (mul x x) y, mul (mul x y) y));
  assert_norm (node_open (mul (num 2) (mul x y), mul (num 3) (mul y x)));
  assert_norm (node_open (mul x y, mul y x_param));
  assert_norm (node_open (mul_param x y, mul_param y x));
  assert_norm (RD.check_root_document PT.core_schema (rewrite_document (mul x y) (mul x x)) == RD.RootPending 1)

(* The direct path reads closed premise-free RewriteRule equations only. *)
let p4_shape_guards ()
  : Lemma (not (SP.product_rewrite (rewrite_node euclid_l euclid_r)) /\
           not (SP.product_rewrite ({ rewrite_node (mul x y) (mul y x) with
                                      U.premises = [{ U.conclusion = U.Holds R.true_expr; hypotheses = [] }] })) /\
           not (SP.product_rewrite ({ rewrite_node (mul x y) (mul y x) with U.kind = U.LemmaRule })) /\
           not (SP.product_rewrite ({ rewrite_node (mul x y) (mul y x) with U.conclusion = U.Holds (QT.eq (mul x y) (mul y x)) }))) =
  assert_norm (not (SP.product_rewrite (rewrite_node euclid_l euclid_r)));
  assert_norm (not (SP.product_rewrite ({ rewrite_node (mul x y) (mul y x) with
                                          U.premises = [{ U.conclusion = U.Holds R.true_expr; hypotheses = [] }] })));
  assert_norm (not (SP.product_rewrite ({ rewrite_node (mul x y) (mul y x) with U.kind = U.LemmaRule })));
  assert_norm (not (SP.product_rewrite ({ rewrite_node (mul x y) (mul y x) with U.conclusion = U.Holds (QT.eq (mul x y) (mul y x)) })))

(* ---------------------------------------------------------------------- *)
(* P5. The false leaf x*y ~ x*x has opposite values in a root model         *)
(* ---------------------------------------------------------------------- *)

(* At the binder scope [Int; Int] with x = Var 1 = 1 and y = Var 0 = 2, in
   the standard root model of every u: x*y is 2 and x*x is 1. *)
let p5_false_leaf (u:TR.uninterpreted)
  : Lemma (QCM.rint u QCM.none scope2 (QCM.int_env u 1 2) (mul i1 i0) == 2 /\
           QCM.rint u QCM.none scope2 (QCM.int_env u 1 2) (mul i1 i1) == 1) =
  let rho = QCM.int_env u 1 2 in
  QCM.lemma_model u QCM.none;
  TR.lemma_classify_native_times PT.core_schema;
  assert_norm (scope2 == [QT.integer; QT.integer] @ []);
  assert_norm (D.scoped scope2 (mul i1 i0) /\ D.scoped scope2 (mul i1 i1));
  QCM.lemma_int_vars u QCM.none 1 2;
  QCM.lemma_arith u QCM.none scope2 rho TR.native_times_int LA.Mul i1 i0;
  QCM.lemma_arith u QCM.none scope2 rho TR.native_times_int LA.Mul i1 i1;
  assert_norm (TR.icalculate LA.Mul [1; 2] == 2);
  assert_norm (TR.icalculate LA.Mul [1; 1] == 1)
