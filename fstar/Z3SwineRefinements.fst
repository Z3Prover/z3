module Z3SwineRefinements

(* Checked by the parent WSL F* session. Source formulas, not current-model tests,
   quantify the live base and exponent. See ZWINE_NFV_REPORT.md. *)
module P = Z3SwinePower
#set-options "--fuel 2 --ifuel 0 --z3rlimit 10"

(* A sign bit means the corresponding negative observation selected a
   normalization branch. The emitted formula retains its sign guard. *)
let symmetry_clause (x y:int) (neg_x neg_y:bool) : prop =
  ((~neg_x \/ x < 0) /\ (~neg_y \/ y < 0)) ==>
  P.exp x y ==
    (if neg_x && y%2 = 1
     then -P.exp (if neg_x then -x else x) (if neg_y then -y else y)
     else P.exp (if neg_x then -x else x) (if neg_y then -y else y))

let symmetry_sound (x y:int) (neg_x neg_y:bool)
  : Lemma (symmetry_clause x y neg_x neg_y) =
  P.magnitude_neg y;
  P.magnitude_parity y;
  if neg_x then P.power_sign (-x) (P.magnitude y)

let monotonicity_clause (x y z w:int) : prop =
  (x > 1 /\ y > 0 /\ z >= x /\ w >= y /\ (z > x \/ w > y)) ==>
    P.exp z w > P.exp x y

let monotonicity_sound (x y z w:int)
  : Lemma (monotonicity_clause x y z w) =
  if x > 1 /\ y > 0 /\ z >= x /\ w >= y then begin
    P.base_monotone x z y;
    P.exponent_monotone z y w;
    if z > x then P.base_strict x z y
    else if w > y then P.exponent_strict z y w
  end

let zero_exponent_clause (x y:int) : prop =
  y == 0 ==> P.exp x y == 1
let one_exponent_clause (x y:int) : prop =
  y == 1 ==> P.exp x y == x
let zero_result_clause (x y:int) : prop =
  (x == 0 /\ y <> 0) <==> P.exp x y == 0
let one_base_clause (x y:int) : prop =
  x == 1 ==> P.exp x y == 1
let positive_base_clause (x y:int) : prop =
  x > 0 ==> P.exp x y >= 1
let growth_clause (x y:int) : prop =
  (x > 1 /\ y > 1 /\ x+y > 4) ==> P.exp x y > x*y+1

let bounding_sound (x y:int)
  : Lemma (zero_exponent_clause x y /\ one_exponent_clause x y /\
           zero_result_clause x y /\ one_base_clause x y /\
           positive_base_clause x y /\ growth_clause x y) =
  if x = 0 then begin
    if y <> 0 then P.power_zero_base (P.magnitude y)
  end
  else P.power_nonzero x (P.magnitude y);
  if x = 1 then P.power_one_base (P.magnitude y);
  if x > 0 then P.power_positive x (P.magnitude y);
  if x > 1 /\ y > 1 /\ x+y > 4 then P.growth x y

let induction_clause (x y z w:int) (delta:pos) : prop =
  (x == z /\ y >= 0 /\ w-y == delta) ==>
    P.exp z w == P.exp x y * P.power x delta

let induction_sound (x y z w:int) (delta:pos)
  : Lemma (induction_clause x y z w delta) =
  if x == z /\ y >= 0 /\ w-y == delta then
    P.power_add x y delta

let specialized_induction_clause (x y z w anchor:int) (delta:pos) : prop =
  (x == z /\ y >= 0 /\ w-y == delta /\ x == anchor) ==>
    P.exp z w == P.exp x y * P.power anchor delta

let specialized_induction_sound (x y z w anchor:int) (delta:pos)
  : Lemma (specialized_induction_clause x y z w anchor delta) =
  induction_sound x y z w delta

(* Prime family formula; its signed-power theorem is in Z3SwinePrime.
   The C++ witness-search invariant is a separate source obligation. *)
let prime_clause (x y:int) (d:int{d > 1}) : prop =
  (P.exp x y % d == 0) <==> (x % d == 0 /\ y <> 0)

(* An omitted y<>0 would make the biconditional false, even at base 0. *)
let prime_zero_exponent_guard_needed ()
  : Lemma (~((P.exp 0 0 % 2 == 0) <==> (0 % 2 == 0))) = ()

(* The n>=0 induction guard cannot be inferred from a current candidate.
   In the absolute-exponent semantics the raw recurrence fails across 0. *)
let induction_nonnegative_guard_needed ()
  : Lemma (P.exp 2 0 <> P.exp 2 (-1) * P.power 2 1) = ()
