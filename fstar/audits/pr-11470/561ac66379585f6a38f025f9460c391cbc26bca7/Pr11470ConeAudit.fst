module Pr11470ConeAudit
open FStar.List.Tot

(* Obligation 1: maximize_in_cone / maximize_objective_in_cone.
   A model is abstracted by the vector of its objective values (oriented for maximization).
   One step k replaces the model by one satisfying every f_i >= v_i (the 'hard' constraints),
   and later steps use the updated values. *)
type vals = list int

let rec all_ge (a b: vals) : Tot bool (decreases a) =
  match a, b with
  | x::xs, y::ys -> x >= y && all_ge xs ys
  | [], [] -> true
  | _ -> false

let rec ge_refl (a: vals) : Lemma (all_ge a a) = match a with [] -> () | _::t -> ge_refl t

let rec ge_trans (a b c: vals) : Lemma (requires all_ge a b /\ all_ge b c) (ensures all_ge a c) (decreases a) =
  match a, b, c with
  | _::xs, _::ys, _::zs -> ge_trans xs ys zs
  | _ -> ()

(* an engine result for step k: a candidate value vector satisfying the cone constraint
   candidate >= current in every coordinate (the hard constraints), or failure (None) => keep mdl *)
let step (cur: vals) (cand: option vals) : vals =
  match cand with
  | Some c -> if all_ge c cur then c else cur   (* c fails the cone check only if engine violated its contract *)
  | None -> cur

let step_dominates (cur: vals) (cand: option vals) : Lemma (all_ge (step cur cand) cur) =
  ge_refl cur

(* the whole loop; stops at the first failure like 'break' *)
let rec run (cur: vals) (cands: list (option vals)) : Tot vals (decreases cands) =
  match cands with
  | [] -> cur
  | None :: _ -> cur
  | Some c :: rest -> let c' = step cur (Some c) in run c' rest

let rec run_dominates (cur: vals) (cands: list (option vals))
  : Lemma (ensures all_ge (run cur cands) cur) (decreases cands) =
  match cands with
  | [] -> ge_refl cur
  | None :: _ -> ge_refl cur
  | Some c :: rest ->
    let c' = step cur (Some c) in
    step_dominates cur (Some c);
    run_dominates c' rest;
    ge_trans (run c' rest) c' cur

(* Pareto soundness: the final model dominates the starting model coordinatewise, so the
   original dominating-model invariant of the Pareto climb is preserved. *)
let final_dominates_start (v0: vals) (cands: list (option vals)) : Lemma (all_ge (run v0 cands) v0) =
  run_dominates v0 cands

(* Minimization is encoded as maximizing the negation: orientation preserves the order. *)
let neg (x:int) = -x
let min_orient (a b: int) : Lemma (neg a >= neg b <==> a <= b) = ()

(* Obligation 2: nlsat step loop. While the endpoint sup is known, step is halved until
   best + step < sup. Step = n/d, gap = p/q with p,q>0 (best < sup). Condition n*q < p*d. *)
let rec pow2 (t:nat) : Tot pos = if t = 0 then 1 else 2 * pow2 (t-1)

let rec pow2_gt (t:nat) : Lemma (pow2 t > t) = if t = 0 then () else pow2_gt (t-1)

(* halving t times: d_t = d * 2^t *)
let rec halve (n d p q: pos) (fuel: nat) : Tot (option nat) (decreases fuel) =
  if n * q < p * d then Some d
  else if fuel = 0 then None
  else halve n (2 * d) p q (fuel - 1)

let rec halve_terminates (n d p q: pos) (fuel: nat)
  : Lemma (requires pow2 fuel * d * p > n * q)
          (ensures Some? (halve n d p q fuel))
          (decreases fuel) =
  if n * q < p * d then ()
  else begin
    assert (fuel > 0 || (pow2 0 * d * p = d * p /\ True));
    if fuel = 0 then ()
    else begin
      assert (pow2 fuel * d * p == pow2 (fuel-1) * (2 * d) * p);
      halve_terminates n (2*d) p q (fuel-1)
    end
  end

let halve_total (n p q: pos) : Lemma (Some? (halve n 1 p q (n*q))) =
  pow2_gt (n*q);
  halve_terminates n 1 p q (n*q)

(* result satisfies the guard: best + step < sup *)
let halve_sound (n d p q: pos) (fuel: nat)
  : Lemma (match halve n d p q fuel with Some d' -> n * q < p * d' | None -> True) =
  let rec aux (d: pos) (fuel: nat) : Lemma (ensures (match halve n d p q fuel with Some d' -> n*q < p*d' | None -> True)) (decreases fuel) =
    if n * q < p * d then ()
    else if fuel = 0 then ()
    else aux (2*d) (fuel-1)
  in aux d fuel
