module Z3MaxsmtLpRelax
(* Weights are scaled to integers (lattice_step: weights*den are integers). *)

let rec sum_sat (w: list int) (b: list bool) : Tot int (decreases w) =
  match w, b with
  | x :: w', y :: b' -> (if y then x else 0) + sum_sat w' b'
  | _ -> 0

let rec tot_w (w: list int) : Tot int (decreases w) =
  match w with | x :: w' -> x + tot_w w' | [] -> 0

let rec all_nonneg (w: list int) : Tot bool (decreases w) =
  match w with | x :: w' -> x >= 0 && all_nonneg w' | [] -> true

(* cost of a Boolean assignment = tot_w weight - satisfied weight *)
let cost (w: list int) (b: list bool) : int = tot_w w - sum_sat w b

(* O1: if the relaxed maximum m bounds every integral satisfied weight
   (integral points are feasible points of the relaxation), then
   cost >= tot_w - m, i.e. the C++ `bound = literal_weight - value`. *)
let o1 (w: list int) (b: list bool) (m: int)
  : Lemma (requires sum_sat w b <= m) (ensures cost w b >= tot_w w - m) = ()

(* O2: lattice rounding. step>0 divides every cost; bound <= cost
   implies step*ceil(bound/step) <= cost; clamp at 0 is sound for cost>=0. *)
let ceil_div (a: int) (s: pos) : int = if a % s = 0 then a / s else a / s + 1

let o2 (bound: int) (s: pos) (k: int)
  : Lemma (requires bound <= s * k)
          (ensures s * ceil_div bound s <= s * k /\ s * ceil_div bound s >= bound)
  = FStar.Math.Lemmas.euclidean_division_definition bound s;
    FStar.Math.Lemmas.lemma_mult_le_left s (ceil_div bound s) k

let o2_clamp (bound: int) (cst: int)
  : Lemma (requires bound <= cst /\ cst >= 0)
          (ensures (if bound < 0 then 0 else bound) <= cst) = ()

(* O3: bounds_meet. Model with cost = upper exists; lower bound L<=cost of every
   assignment (core or relaxation); L>=upper => upper is optimal. *)
let o3 (upper: int) (lower: int) (c: int)
  : Lemma (requires lower >= upper /\ c >= lower) (ensures c >= upper) = ()
