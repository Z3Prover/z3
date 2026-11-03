module SwineAudit2

(* Integer power for non-negative exponent: model of a.mk_power with e >= 0. *)
let rec pow (b:int) (e:nat) : Tot int (decreases e) =
  if e = 0 then 1 else b * pow b (e - 1)

let even (e:nat) : bool = e % 2 = 0

(* Obligation 1: arith_swine::symmetry, x<0,y>=0 branch (L91-112).
   Guard b<0; lemma: b^e = ite(e mod 2 = 1, -((-b)^e), (-b)^e). *)
let rec neg_pow (b:int) (e:nat) : Lemma (ensures pow b e == (if even e then pow (-b) e else - (pow (-b) e)))
  (decreases e) =
  if e = 0 then () else neg_pow b (e - 1)

let symmetry_valid (b:int{b < 0}) (e:nat)
  : Lemma (pow b e == (if e % 2 = 1 then - (pow (-b) e) else pow (-b) e))
  = neg_pow b e

(* Obligation 2: arith_swine::induction (L232-273), symbolic-base branch:
   guards p.base=q.base, e>=0, q.exp - p.exp = d (d>0): b^(e+d) = b^e * b^d,
   with b^d emitted as the d-fold product b*...*b (d<=64) or as numeral. *)
let rec pow_add (b:int) (e:nat) (d:nat) : Lemma (ensures pow b (e + d) == pow b e * pow b d) (decreases e) =
  if e = 0 then () else pow_add b (e - 1) d

let rec product (b:int) (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else b * product b (n - 1)

let rec product_is_pow (b:int) (n:nat) : Lemma (ensures product b n == pow b n) (decreases n) =
  if n = 0 then () else product_is_pow b (n - 1)

let induction_valid (b:int) (e:nat) (d:nat{d > 0})
  : Lemma (pow b (e + d) == pow b e * product b d)
  = pow_add b e d; product_is_pow b d

(* Numeral-base branch / specialization branch: base = x, factor = x^d. *)
let induction_numeral_valid (x:int) (e:nat) (d:nat)
  : Lemma (pow x (e + d) == pow x e * pow x d)
  = pow_add x e d

(* Obligation 1b: symmetry lemma when the exponent is unconstrained (the C++ guard is only b<0).
   zpow follows compute_power / Z3 semantics for negative exponents. *)
let zpow (b:int) (e:int) : int =
  if e >= 0 then pow b e
  else if b = 1 then 1
  else if b = -1 then (if e % 2 = 0 then 1 else -1)
  else 0

let symmetry_valid_any (b:int{b < 0}) (e:int)
  : Lemma (zpow b e == (if e % 2 = 1 then - (zpow (-b) e) else zpow (-b) e))
  = if e >= 0 then neg_pow b e else ()
