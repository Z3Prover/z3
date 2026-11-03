(* Tests for typed forall/exists introduction over checked binder
   certificates (`Z3BinderKernel`), on actual production certificates and
   `QuantifierIntroduction` nodes checked by `check_node_with_context`, in the
   classical standard model `Z3GhostStandardModel.ghost_standard`, a joint
   model of `Z3TypedQuantifier.quantifier_model`.

   * Positive: the fragment holds (computed), the node is checked with
     pending 0, and the node theorem gives the certified equation; with the
     known truth of one side, the other side's truth follows THROUGH the
     theorem (not proved separately): `forall x:Int. 0 + x = x` from
     `forall x:Int. x + 0 = x` (open-body commutativity and congruence), and
     `exists x:Int, p:Bool. x = -1 and p` from `exists ... p and x = -1`
     (mixed binders in reversed de Bruijn order).
   * A closed input inside a binder: the certified equation follows when the
     node's assertion holds.
   * The typed invariant is needed: the open body premise `x + 0 = x` is false
     under an environment that gives `x` a Boolean, so the old invariant
     "every cached judgment holds under every environment" fails in the
     standard model.
   * Mutations rejected by the checker (pending 1), several with false
     conclusions: a wrong body, a wrong outer quantifier, a reversed edge,
     a wrong binder count.
   * Accepted certificates outside the fragment stay explicitly uncovered:
     a non-reflexive QR wrapper, a `rewrite` leaf, a lambda introduction. *)
module Z3BinderKernelTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3UnifiedProof
module GS = Z3GhostStandardModel
module GT = Z3GhostStandardModelTests
module CO = Z3CoreModel
module C = Z3CanonicalOps
module BK = Z3BinderKernel
module ST = Z3BinderScopeTests
module L = FStar.List.Tot

type leaf = func_decl -> list value -> int
let g (base:leaf) : interpretation value = GS.ghost_standard base

let int_s : sort = GT.int_s
let num (n:int) : expr = GT.num n
let plus (a b:expr) : expr = GT.plus a b
let eq (a b:expr) : expr = GT.eq a b
let x0 : expr = GT.x0

let fact (j:judgment) : checked_fact = { conclusion = j; hypotheses = [] }

let cert_of (n:proof_node) : binder_certificate =
  match n.kind with QuantifierIntroduction c -> c | _ -> { binder_entries = []; binder_root = 0 }

(* The node theorem in the standard model. *)
let lemma_node (base:leaf) (rho:env value) (assertions:list judgment) (n:proof_node)
  : Lemma (requires QuantifierIntroduction? n.kind /\
                    BK.introduction_fragment [] assertions (cert_of n) /\
                    check_node_with_context [] false assertions n == Some (fact n.conclusion, 0) /\
                    judgments_hold (g base) rho assertions)
          (ensures judgment_holds (g base) rho n.conclusion)
  = GS.lemma_quantifier_model base;
    BK.lemma_introduction_node_sound [] (g base) GS.domains rho false assertions n

(* --- forall x:Int. x + 0 = x  ==  forall x:Int. 0 + x = x ------------------------------------ *)

let zero_body : expr = eq (plus x0 (num 0)) x0
let zero_body' : expr = eq (plus (num 0) x0) x0
let zero_rhs : expr = ST.all [int_s] zero_body'
let zero_cert : binder_certificate =
  ST.cert [ST.entry "commutativity" (mk_eq_expr (plus x0 (num 0)) (plus (num 0) x0)) [] None;
           ST.entry "monotonicity" (mk_eq_expr zero_body zero_body') [0] None;
           ST.entry "quant-intro" (mk_eq_expr GT.valid zero_rhs) [1] (Some [int_s])] 2
let zero_node : proof_node = ST.intro zero_cert (Equal GT.valid zero_rhs)

let zero_checked ()
  : Lemma (BK.introduction_fragment [] [] zero_cert /\
           check_node_with_context [] false [] zero_node == Some (fact zero_node.conclusion, 0))
  = assert_norm (BK.introduction_fragment [] [] zero_cert);
    assert_norm (check_node_with_context [] false [] zero_node == Some (fact zero_node.conclusion, 0))

(* The right-hand side is true, through the node theorem and the truth of
   the left-hand side; its instance at 7 follows. *)
let zero_sound (base:leaf) (rho:env value)
  : Lemma (eval (g base) zero_rhs rho == VBool true /\
           eval (g base) zero_body' (shift [VInt 7] rho) == VBool true)
  = zero_checked ();
    lemma_node base rho [] zero_node;
    GT.valid_true base rho;
    GT.lemma_forall_int base zero_body' rho

(* --- exists x:Int, p:Bool. p and x = -1  ==  exists x:Int, p:Bool. x = -1 and p ---------------- *)

let swap_body : expr = GT.conj (eq GT.x1 (num (-1))) GT.p0
let swap_rhs : expr = ST.some [int_s; bool_sort] swap_body
let swap_cert : binder_certificate =
  ST.cert [ST.entry "commutativity" (mk_eq_expr GT.witness_body swap_body) [] None;
           ST.entry "quant-intro" (mk_eq_expr GT.witnessed swap_rhs) [0] (Some [int_s; bool_sort])] 1
let swap_node : proof_node = ST.intro swap_cert (Equal GT.witnessed swap_rhs)

let swap_checked ()
  : Lemma (BK.introduction_fragment [] [] swap_cert /\
           check_node_with_context [] false [] swap_node == Some (fact swap_node.conclusion, 0))
  = assert_norm (BK.introduction_fragment [] [] swap_cert);
    assert_norm (check_node_with_context [] false [] swap_node == Some (fact swap_node.conclusion, 0))

let swap_sound (base:leaf) (rho:env value) : Lemma (eval (g base) swap_rhs rho == VBool true)
  = swap_checked ();
    lemma_node base rho [] swap_node;
    GT.witnessed_true base rho

(* --- The other accepted fixtures of `Z3BinderScopeTests` are in the fragment --------------- *)

let fixtures_in_fragment ()
  : Lemma (BK.introduction_fragment [] [] (cert_of ST.sum_node) /\
           BK.introduction_fragment [] [] (cert_of ST.nested_node) /\
           BK.introduction_fragment [] [] (cert_of ST.empty_node) /\
           BK.introduction_fragment [] [ST.input] (cert_of ST.input_node) /\
           BK.introduction_fragment [] [] (cert_of ST.shared_closed_node) /\
           BK.introduction_fragment [] [] (cert_of (ST.diamond_node 6)))
  = assert_norm (BK.introduction_fragment [] [] (cert_of ST.sum_node));
    assert_norm (BK.introduction_fragment [] [] (cert_of ST.nested_node));
    assert_norm (BK.introduction_fragment [] [] (cert_of ST.empty_node));
    assert_norm (BK.introduction_fragment [] [ST.input] (cert_of ST.input_node));
    assert_norm (BK.introduction_fragment [] [] (cert_of ST.shared_closed_node));
    assert_norm (BK.introduction_fragment [] [] (cert_of (ST.diamond_node 6)))

(* A closed input inside a binder: the equation holds wherever the input does. *)
let input_sound (base:leaf) (rho:env value)
  : Lemma (requires judgment_holds (g base) rho ST.input)
          (ensures judgment_holds (g base) rho ST.input_node.conclusion)
  = ST.accepted ();
    fixtures_in_fragment ();
    lemma_node base rho [ST.input] ST.input_node

(* --- The invariant must be typed ---------------------------------------------------------- *)

(* The open premise x + 0 = x of `zero_cert` fails when x is a Boolean: the
   legacy `binder_cache_sound` (every environment) does not hold here. *)
let untyped_premise_false (base:leaf) (rho:env value)
  : Lemma (~(judgment_holds (g base) (shift [VBool true] rho) (Equal (plus x0 (num 0)) x0)))
  = GT.lemma_num base 0 (shift [VBool true] rho);
    GS.lemma_arithmetic_app base GT.plus_decl x0 (num 0) (shift [VBool true] rho)

(* --- Mutations: rejected, some false --------------------------------------------------------- *)

let with_root_formula (c:binder_certificate) (f:expr) : binder_certificate =
  match c.binder_entries with
  | [e0; e1; e2] -> { c with binder_entries = [e0; e1; { e2 with binder_formula = f }] }
  | _ -> c

(* The body x + 0 = x paired with 0 + x = x + 1. *)
let bad_body : expr = eq (plus (num 0) x0) (plus x0 (num 1))
let bad_rhs : expr = ST.all [int_s] bad_body
let body_node : proof_node =
  ST.intro (with_root_formula zero_cert (mk_eq_expr GT.valid bad_rhs)) (Equal GT.valid bad_rhs)

(* forall on the left, exists on the right. *)
let ex_rhs : expr = ST.some [int_s] zero_body'
let outer_node : proof_node =
  ST.intro (with_root_formula zero_cert (mk_eq_expr GT.valid ex_rhs)) (Equal GT.valid ex_rhs)

(* The body edge reversed: (0 + x = x) = (x + 0 = x) used for the same conclusion. *)
let reversed_node : proof_node =
  ST.intro (ST.cert [ST.entry "commutativity" (mk_eq_expr (plus (num 0) x0) (plus x0 (num 0))) [] None;
                     ST.entry "monotonicity" (mk_eq_expr zero_body' zero_body) [0] None;
                     ST.entry "quant-intro" (mk_eq_expr GT.valid zero_rhs) [1] (Some [int_s])] 2)
           (Equal GT.valid zero_rhs)

(* Two binder sorts for one binder. *)
let count_node : proof_node =
  ST.intro ({ zero_cert with binder_entries =
              (match zero_cert.binder_entries with
               | [e0; e1; e2] -> [e0; e1; { e2 with binder_sorts = Some [int_s; int_s] }]
               | es -> es) })
           (Equal GT.valid zero_rhs)

let mutations_pending ()
  : Lemma (check_node_with_context [] false [] body_node == Some (fact body_node.conclusion, 1) /\
           check_node_with_context [] false [] outer_node == Some (fact outer_node.conclusion, 1) /\
           check_node_with_context [] false [] reversed_node == Some (fact reversed_node.conclusion, 1) /\
           check_node_with_context [] false [] count_node == Some (fact count_node.conclusion, 1))
  = assert_norm (check_node_with_context [] false [] body_node == Some (fact body_node.conclusion, 1));
    assert_norm (check_node_with_context [] false [] outer_node == Some (fact outer_node.conclusion, 1));
    assert_norm (check_node_with_context [] false [] reversed_node == Some (fact reversed_node.conclusion, 1));
    assert_norm (check_node_with_context [] false [] count_node == Some (fact count_node.conclusion, 1))

(* The wrong body gives a false equation: x + 0 = x holds, 0 + x = x + 1 never. *)
let body_false (base:leaf) (rho:env value)
  : Lemma (~(judgment_holds (g base) rho body_node.conclusion))
  = GT.valid_true base rho;
    GT.lemma_forall_int base bad_body rho;
    let r = shift [VInt 0] rho in
    GT.lemma_x_plus base rho 0 1;
    GT.lemma_num base 0 r;
    GT.lemma_plus base (num 0) x0 r 0 0;
    GT.lemma_eq base (plus (num 0) x0) (plus x0 (num 1)) r

(* --- Accepted but outside the fragment: explicitly uncovered ------------------------------- *)

(* The QR wrapper equates the body (or (x = x) (not (x = x))) with true. *)
let taut_x : expr = ST.taut (eq x0 x0)
let wrapper_node : proof_node =
  ST.intro (ST.cert [ST.refl_true;
                     ST.entry "quant-intro" (mk_eq_expr (ST.all [int_s] taut_x) ST.fa_rhs) [0] (Some [int_s])] 1)
           (Equal (ST.all [int_s] taut_x) ST.fa_rhs)

(* A `rewrite` leaf decided by the Boolean equivalence check. *)
let rewrite_node : proof_node =
  ST.intro (ST.cert [ST.entry "rewrite" (mk_eq_expr taut_x true_expr) [] None;
                     ST.entry "quant-intro" (mk_eq_expr (ST.all [int_s] taut_x) ST.fa_rhs) [0] (Some [int_s])] 1)
           (Equal (ST.all [int_s] taut_x) ST.fa_rhs)

let uncovered ()
  : Lemma (check_node_with_context [] false [] wrapper_node == Some (fact wrapper_node.conclusion, 0) /\
           ~(BK.introduction_fragment [] [] (cert_of wrapper_node)) /\
           check_node_with_context [] false [] rewrite_node == Some (fact rewrite_node.conclusion, 0) /\
           ~(BK.introduction_fragment [] [] (cert_of rewrite_node)) /\
           ~(BK.introduction_fragment [] [] (cert_of ST.lambda_node)))
  = assert_norm (check_node_with_context [] false [] wrapper_node == Some (fact wrapper_node.conclusion, 0));
    assert_norm (BK.introduction_fragment [] [] (cert_of wrapper_node) == false);
    assert_norm (check_node_with_context [] false [] rewrite_node == Some (fact rewrite_node.conclusion, 0));
    assert_norm (BK.introduction_fragment [] [] (cert_of rewrite_node) == false);
    assert_norm (BK.introduction_fragment [] [] (cert_of ST.lambda_node) == false)

(* --- Controls ----------------------------------------------------------------------------------- *)

[@@expect_failure [19]]
let body_checked () : Lemma (check_node_with_context [] false [] body_node == Some (fact body_node.conclusion, 0))
  = assert_norm (check_node_with_context [] false [] body_node == Some (fact body_node.conclusion, 0))

[@@expect_failure [19]]
let wrapper_in_fragment () : Lemma (BK.introduction_fragment [] [] (cert_of wrapper_node))
  = assert_norm (BK.introduction_fragment [] [] (cert_of wrapper_node))
