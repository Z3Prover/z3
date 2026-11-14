module HornProofRemoval
(* Model of horn_tactic (src/muz/fp/horn_tactic.cpp) at head dbb1590, base 1a1d88d.
   Base operator() lines 404-410 passes goals with proofs through unchanged; the PR deletes that guard.
   Abstract model: a goal carries input formulas; a proof leaf is either an input or an unjustified mk_asserted. *)
type path = | PassThrough | RunSimplify | RunVerify

let base_path (is_simplify proofs: bool) : path =
  if proofs then PassThrough else if is_simplify then RunSimplify else RunVerify
let head_path (is_simplify proofs: bool) : path =
  if is_simplify then RunSimplify else RunVerify

(* O1: the PR changes behaviour exactly on proof-enabled goals; other inputs are unchanged. *)
let o1_unchanged_without_proofs (s: bool) : Lemma (head_path s false == base_path s false) = ()
let o1_changed_with_proofs (s: bool) : Lemma (head_path s true =!= base_path s true) = ()

(* O2: horn-simplify with proofs: goal is reset, then each output formula is asserted via
   goal::assert_expr(f) which, with proofs enabled, attaches mk_asserted(f) (goal.cpp:266-267).
   Output formulas come from datalog rule transformation, not from the input set. *)
type formula = | Orig of nat | Transformed of nat
type leaf = | Input of nat | FreshAsserted of nat

let leaf_of (f: formula) : leaf = match f with | Orig n -> Input n | Transformed n -> FreshAsserted n

let simplify_leaves (out: list formula) : list leaf = List.Tot.map leaf_of out

let rec all_input (l: list leaf) : bool = match l with | [] -> true | Input _ :: t -> all_input t | _ :: _ -> false

(* The proof-leaf soundness requirement (every leaf is an original input) is not guaranteed by the model
   as soon as one output formula is a transformed rule. *)
let o2_leaf_not_input (n: nat) (rest: list formula)
  : Lemma (not (all_input (simplify_leaves (Transformed n :: rest)))) = ()

(* O3: verify branch with proofs, monotone + sat answer: asserts get_fact(proof) with the Datalog proof
   (justified by proof2proof_converter); non-monotone leaves goal unchanged (sound). Model only the dispatch. *)
type ans = | Reach | Unreach | Undef
let verify_effect (a: ans) (monotone proofs: bool) : string =
  match a with
  | Reach -> if monotone && proofs then "assert_fact_with_proof" else if monotone then "assert_false" else "unchanged"
  | Unreach -> "reset_goal"
  | Undef -> "unchanged"
let o3 (m:bool) : Lemma (verify_effect Reach m true == (if m then "assert_fact_with_proof" else "unchanged")) = ()
