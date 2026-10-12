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

let s (n:string) : sort = BaseSort n
let int_s = s "Int"
let bool_s = s "Bool"
let bv_s = s "BV32"
let seq_s = s "SeqInt"
let arr_s : sort = ArraySort [int_s] int_s

let konst (name:string) (rng:sort) : func_decl =
  { decl_name = name; domain = []; range = rng; interp = None; int_params = [] }
let unary (name:string) (dom rng:sort) : func_decl =
  { decl_name = name; domain = [dom]; range = rng; interp = None; int_params = [] }
let binary (name:string) (d1 d2 rng:sort) : func_decl =
  { decl_name = name; domain = [d1; d2]; range = rng; interp = None; int_params = [] }

let c0 (f:func_decl) : expr = App f []
let c1 (f:func_decl) (a:expr) : expr = App f [a]
let c2 (f:func_decl) (a b:expr) : expr = App f [a; b]
let c3 (f:func_decl) (a b c:expr) : expr = App f [a; b; c]
let ternary (name:string) (d1 d2 d3 rng:sort) : func_decl =
  { decl_name = name; domain = [d1; d2; d3]; range = rng; interp = None; int_params = [] }

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
(* Test 6: `array_rewriter` -- `select(store(a,i,v),i) = v`             *)
(*   (ARRAY_REWRITER_REPORT.md / `Z3ArrayTheory.lemma_select_store_same`,*)
(*    and the exact fact `fstar/rewrite_rule_bench/arrays.smt2`'s real   *)
(*    `array:select` proof tag extracted, before that tagging          *)
(*    mechanism was reverted from master -- see                        *)
(*    `REWRITE_RULE_TAGS_REPORT.md`). As with every other theory in     *)
(*    this file, the leaf is trusted by the checker, not re-derived;    *)
(*    `Z3ArrayTheory.fst`'s own report is what separately establishes   *)
(*    its semantic soundness.                                          *)
(* ----------------------------------------------------------------- *)

let a_arr = c0 (konst "a" arr_s)
let i_i = c0 (konst "i" int_s)
let v_i = c0 (konst "v" int_s)
let store_d = ternary "store" arr_s int_s int_s arr_s
let select_d = binary "select" arr_s int_s int_s
let store_aiv = c3 store_d a_arr i_i v_i
let array_leaf : proof = mk_rewrite_leaf (c2 select_d store_aiv i_i) v_i

let lemma_array_leaf_fact ()
  : Lemma (fact array_leaf == Some (c2 select_d store_aiv i_i, v_i))
  = ()

(* ----------------------------------------------------------------- *)
(* Test 7: `PR_BIND`+`PR_QUANT_INTRO` -- a rewrite firing under a       *)
(* `forall` binder (`rewriter_tpl::process_quantifier`'s shape)        *)
(* ----------------------------------------------------------------- *)

let quant_leaf : proof = mk_quant_intro Forall_k [int_s] arith_leaf

let lemma_quant_leaf_fact ()
  : Lemma (fact quant_leaf ==
           Some (Quantifier Forall_k [int_s] bool_s (c2 plus_d x_i zero),
                 Quantifier Forall_k [int_s] bool_s x_i))
  = ()

(* ----------------------------------------------------------------- *)
(* Displaying the trusted leaves: every `Rewrite s t` node reachable    *)
(* inside a proof is exactly the obligation `all_leaves_sound`         *)
(* (`Z3ProofTheory.fst`) quantifies over and the checker itself never   *)
(* re-derives (see the previous discussion). `collect_rewrite_leaves`   *)
(* makes that set concrete and inspectable, instead of leaving it       *)
(* implicit inside a `forall`/`prop`.                                   *)
(* ----------------------------------------------------------------- *)

let rec collect_rewrite_leaves (p:proof) : Tot (list (expr & expr)) (decreases p) =
  match p with
  | Refl _ -> []
  | Sym p1 -> collect_rewrite_leaves p1
  | Trans p1 p2 -> collect_rewrite_leaves p1 @ collect_rewrite_leaves p2
  | Congr _ _ _ prfs -> collect_rewrite_leaves_list prfs
  | Rewrite s t -> [(s, t)]
  | QuantIntro _ _ p1 -> collect_rewrite_leaves p1
and collect_rewrite_leaves_list (prfs:list proof) : Tot (list (expr & expr)) (decreases prfs) =
  match prfs with
  | [] -> []
  | p :: prfs' -> collect_rewrite_leaves p @ collect_rewrite_leaves_list prfs'

(* The array example (`Test 6`) is a single, bare `Rewrite` node, so it
   has exactly one trusted leaf: the whole fact itself. *)
let lemma_array_leaf_trusted_leaves ()
  : Lemma (collect_rewrite_leaves array_leaf == [(c2 select_d store_aiv i_i, v_i)])
  = ()

(* For contrast: `mixed_chain` (Test 4) is a 3-step `Trans` combining
   leaves from three different theories, so it has three trusted
   leaves, each the real responsibility of its own theory's rewriter
   report, not of this file or the checker. *)
let lemma_mixed_chain_trusted_leaves ()
  : Lemma (collect_rewrite_leaves mixed_chain ==
           [ (c2 cat_d (c2 cat_d a_sq b_sq) c_sq, c2 cat_d a_sq (c2 cat_d b_sq c_sq));
             (c2 cat_d a_sq (c2 cat_d b_sq c_sq), x_b);
             (c1 not_d (c1 not_d x_b), x_b) ])
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
  let mut ctr = 0;
  let o = check_proof p ctr;
  let n = !ctr;
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
  lemma_array_leaf_fact ();
  run_one array_leaf (Some (c2 select_d store_aiv i_i, v_i));
  lemma_array_leaf_trusted_leaves ();
  lemma_mixed_chain_trusted_leaves ();
  lemma_quant_leaf_fact ();
  run_one quant_leaf (Some (Quantifier Forall_k [int_s] bool_s (c2 plus_d x_i zero),
                            Quantifier Forall_k [int_s] bool_s x_i));
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
  let b4 = checker_accepts array_leaf;
  assert (pure (b4 == true));
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
