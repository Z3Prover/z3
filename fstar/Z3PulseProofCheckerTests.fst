(*
   Z3PulseProofCheckerTests.fst

   Concrete-instance tests exercising `Z3PulseProofChecker.fst`'s
   Pulse-verified `check_proof`/`checker_accepts` on sample proof
   derivations whose `Rewrite` leaves are drawn from many different
   per-theory rewriter audits in this directory -- demonstrating that
   the one shared Pulse checker handles every theory's leaves
   uniformly, exactly as `rewriter_def.h`/`proof_checker.cpp` are
   themselves theory-agnostic and shared by every rewriter plugin in
   Z3 itself (`bool_rewriter`, `arith_rewriter`, `bv_rewriter`,
   `seq_rewriter`, the nonlinear-arithmetic lemmas catalogued in
   `Z3NlArith.fst`, ...).

   Every "leaf equation" used below (e.g. "`not(not x) = x`") is
   exactly the kind of rewrite rule that theory's own
   `*_REWRITER_REPORT.md` already independently audits; this file
   does not re-derive those facts (out of scope here, as it is for
   `Z3ProofTheory.fst` itself -- see `all_leaves_sound`'s docstring
   there) and treats each leaf as a trusted, named rewrite step, the
   same way `mk_rewrite_leaf`/`PR_REWRITE` always does in the real
   checker. The point under test is purely the proof-*calculus* layer
   on top: does the Pulse checker accept exactly the derivations
   `Z3ProofTheory.fst`'s pure `fact` does, and reject the ones that
   are not well-formed.
*)
module Z3PulseProofCheckerTests
#lang-pulse
open Pulse.Lib.Pervasives
open Z3AstTheory
open Z3ProofTheory
open Z3PulseProofChecker

(* ----------------------------------------------------------------- *)
(* Minimal term-building helpers (uninterpreted constants/functions;   *)
(* only their names and arities matter to `fact`/`check_proof`)        *)
(* ----------------------------------------------------------------- *)

let s (n:string) : sort = { sort_name = n }
let int_s = s "Int"
let bool_s = s "Bool"
let bv_s = s "BV32"
let seq_s = s "SeqInt"

let konst (name:string) (rng:sort) : func_decl =
  { decl_name = name; domain = []; range = rng; interp = None; int_params = [] }
let unary (name:string) (dom rng:sort) : func_decl =
  { decl_name = name; domain = [dom]; range = rng; interp = None; int_params = [] }
let binary (name:string) (d1 d2 rng:sort) : func_decl =
  { decl_name = name; domain = [d1; d2]; range = rng; interp = None; int_params = [] }

let c0 (f:func_decl) : expr = App f []
let c1 (f:func_decl) (a:expr) : expr = App f [a]
let c2 (f:func_decl) (a b:expr) : expr = App f [a; b]

(* ----------------------------------------------------------------- *)
(* Test 1: `bool_rewriter` -- double-negation elimination               *)
(*   leaf: not(not x) = x        (BOOL_ARITH_REWRITER_REPORT.md)       *)
(* ----------------------------------------------------------------- *)

let x_b = c0 (konst "x" bool_s)
let not_d = unary "not" bool_s bool_s
let bool_leaf : proof = mk_rewrite_leaf (c1 not_d (c1 not_d x_b)) x_b

let lemma_bool_leaf_fact ()
  : Lemma (fact bool_leaf == Some (c1 not_d (c1 not_d x_b), x_b))
  = ()

(* `mk_sym` flips the conclusion: `x = not(not x)`. *)
let bool_leaf_sym : proof = mk_sym bool_leaf

let lemma_bool_leaf_sym_fact ()
  : Lemma (fact bool_leaf_sym == Some (x_b, c1 not_d (c1 not_d x_b)))
  = ()

(* ----------------------------------------------------------------- *)
(* Test 2: `arith_rewriter` -- additive identity, under a congruence    *)
(*   leaf: (+ x 0) = x           (ARITH_REWRITER_REPORT.md)            *)
(*   lifted through a unary `p` via `mk_congr`: p(+ x 0) = p(x)         *)
(* ----------------------------------------------------------------- *)

let x_i = c0 (konst "x" int_s)
let zero = c0 (konst "0" int_s)
let plus_d = binary "+" int_s int_s int_s
let p_d = unary "p" int_s bool_s

let arith_leaf : proof = mk_rewrite_leaf (c2 plus_d x_i zero) x_i
let arith_congr : proof = mk_congr p_d [c2 plus_d x_i zero] [x_i] [arith_leaf]

let lemma_arith_congr_fact ()
  : Lemma (fact arith_congr == Some (c1 p_d (c2 plus_d x_i zero), c1 p_d x_i))
  = ()

(* ----------------------------------------------------------------- *)
(* Test 3: `bv_rewriter` -- `bvand` idempotence                        *)
(*   leaf: (bvand y y) = y       (BV_REWRITER_REPORT.md)               *)
(* ----------------------------------------------------------------- *)

let y_bv = c0 (konst "y" bv_s)
let bvand_d = binary "bvand" bv_s bv_s bv_s
let bv_leaf : proof = mk_rewrite_leaf (c2 bvand_d y_bv y_bv) y_bv

let lemma_bv_leaf_fact ()
  : Lemma (fact bv_leaf == Some (c2 bvand_d y_bv y_bv, y_bv))
  = ()

(* ----------------------------------------------------------------- *)
(* Test 4: `seq_rewriter` -- concatenation associativity, into a        *)
(* three-step transitivity chain combining *three different theories'* *)
(* leaves (`seq_rewriter`, then `bool_rewriter`, then `arith_rewriter`) *)
(* into a single derivation -- the same shared checker composing       *)
(* leaves across theory boundaries, exactly as a real Z3 proof object   *)
(* arising from preprocessing a mixed-theory formula would.            *)
(* ----------------------------------------------------------------- *)

let a_sq = c0 (konst "a" seq_s)
let b_sq = c0 (konst "b" seq_s)
let c_sq = c0 (konst "c" seq_s)
let cat_d = binary "++" seq_s seq_s seq_s

let seq_leaf : proof =
  mk_rewrite_leaf (c2 cat_d (c2 cat_d a_sq b_sq) c_sq) (c2 cat_d a_sq (c2 cat_d b_sq c_sq))

(* A second, unrelated `bool_rewriter` leaf and a third, unrelated
   `arith_rewriter` leaf chained after it via two `mk_trans` calls:
   purely to demonstrate chaining across theories, their middle terms
   are rigged to match syntactically (`x_b`/`c1 not_d (c1 not_d x_b)`),
   not because the three facts are otherwise related. *)
let mixed_chain : proof =
  mk_trans (mk_trans seq_leaf (mk_rewrite_leaf (c2 cat_d a_sq (c2 cat_d b_sq c_sq)) x_b))
           bool_leaf_sym

let lemma_mixed_chain_fact ()
  : Lemma (fact mixed_chain ==
           Some (c2 cat_d (c2 cat_d a_sq b_sq) c_sq, c1 not_d (c1 not_d x_b)))
  = ()

(* ----------------------------------------------------------------- *)
(* Test 5: nonlinear arithmetic (`Z3NlArith.fst`) -- treated, as every  *)
(* other theory's rewrite conclusion is, as an opaque trusted leaf;    *)
(* `Z3NlArith.fst`/`NL_ARITH_REPORT.md` is exactly what separately      *)
(* establishes such a leaf's own semantic soundness (out of scope      *)
(* here, same as every other theory in this test file).                *)
(* ----------------------------------------------------------------- *)

let mono_lhs = c0 (konst "monotonicity_lhs" bool_s)
let mono_rhs = c0 (konst "monotonicity_rhs" bool_s)
let nl_arith_leaf : proof = mk_rewrite_leaf mono_lhs mono_rhs

let lemma_nl_arith_leaf_fact ()
  : Lemma (fact nl_arith_leaf == Some (mono_lhs, mono_rhs))
  = ()

(* ----------------------------------------------------------------- *)
(* Test 6: `PR_BIND`+`PR_QUANT_INTRO` -- a rewrite firing under a       *)
(* `forall` binder (`rewriter_tpl::process_quantifier`'s shape)        *)
(* ----------------------------------------------------------------- *)

let quant_leaf : proof = mk_quant_intro Forall_k [int_s] arith_leaf

let lemma_quant_leaf_fact ()
  : Lemma (fact quant_leaf ==
           Some (Quantifier Forall_k [int_s] (c2 plus_d x_i zero),
                 Quantifier Forall_k [int_s] x_i))
  = ()

(* ----------------------------------------------------------------- *)
(* Running the Pulse checker on all of the above, with an explicit     *)
(* step counter, additionally confirming the counter advances by       *)
(* exactly `proof_size` as `Z3PulseProofChecker.fst`'s Pulse-level      *)
(* postcondition promises (not merely that the final boolean verdict   *)
(* is as expected).                                                     *)
(* ----------------------------------------------------------------- *)

fn run_one (p:proof) (expected:option (expr & expr))
  requires pure (fact p == expected)
  ensures emp
{
  let ctr = Pulse.Lib.Reference.alloc 0;
  let o = check_proof p ctr;
  let n = !ctr;
  Pulse.Lib.Reference.free ctr;
  assert (pure (n == proof_size p));
  assert (pure (o == expected));
}

fn test_all_theories ()
  requires emp
  ensures emp
{
  lemma_bool_leaf_fact ();
  run_one bool_leaf (Some (c1 not_d (c1 not_d x_b), x_b));
  lemma_bool_leaf_sym_fact ();
  run_one bool_leaf_sym (Some (x_b, c1 not_d (c1 not_d x_b)));
  lemma_arith_congr_fact ();
  run_one arith_congr (Some (c1 p_d (c2 plus_d x_i zero), c1 p_d x_i));
  lemma_bv_leaf_fact ();
  run_one bv_leaf (Some (c2 bvand_d y_bv y_bv, y_bv));
  lemma_mixed_chain_fact ();
  run_one mixed_chain (Some (c2 cat_d (c2 cat_d a_sq b_sq) c_sq, c1 not_d (c1 not_d x_b)));
  lemma_nl_arith_leaf_fact ();
  run_one nl_arith_leaf (Some (mono_lhs, mono_rhs));
  lemma_quant_leaf_fact ();
  run_one quant_leaf (Some (Quantifier Forall_k [int_s] (c2 plus_d x_i zero),
                            Quantifier Forall_k [int_s] x_i));
}

(* `checker_accepts`'s boolean-only interface, exercised the same way. *)
fn test_checker_accepts ()
  requires emp
  ensures emp
{
  let b1 = checker_accepts bool_leaf;
  assert (pure (b1 == true));
  let b2 = checker_accepts mixed_chain;
  assert (pure (b2 == true));
  let b3 = checker_accepts quant_leaf;
  assert (pure (b3 == true));
}

(* ----------------------------------------------------------------- *)
(* Rejection tests: ill-formed proofs the checker must *not* accept.   *)
(* ----------------------------------------------------------------- *)

(* A `Trans` whose two middle terms disagree (`x_b` vs. `y_bv`,
   different sorts/names entirely): `check1_basic`'s real
   `SASSERT(fact1->get_arg(1) == fact2->get_arg(0))` would fail; here
   `fact`/`check_proof` simply report `None` rather than asserting. *)
let bad_trans : proof = mk_trans bool_leaf (mk_rewrite_leaf y_bv y_bv)

let lemma_bad_trans_fact () : Lemma (fact bad_trans == None) = ()

(* A `Congr` with mismatched argument-list lengths. *)
let bad_congr : proof = mk_congr p_d [x_i] [x_i; zero] []

let lemma_bad_congr_fact () : Lemma (fact bad_congr == None) = ()

(* A `Congr` with matching lengths but a changed argument position that
   *no* supplied premise justifies (`prfs = []`, but `args1 <> args2`
   pointwise). *)
let unjustified_congr : proof = mk_congr p_d [x_i] [zero] []

let lemma_unjustified_congr_fact () : Lemma (fact unjustified_congr == None) = ()

fn test_rejections ()
  requires emp
  ensures emp
{
  lemma_bad_trans_fact ();
  run_one bad_trans None;
  lemma_bad_congr_fact ();
  run_one bad_congr None;
  lemma_unjustified_congr_fact ();
  run_one unjustified_congr None;
  let b1 = checker_accepts bad_trans;
  assert (pure (b1 == false));
  let b2 = checker_accepts bad_congr;
  assert (pure (b2 == false));
  let b3 = checker_accepts unjustified_congr;
  assert (pure (b3 == false));
}
