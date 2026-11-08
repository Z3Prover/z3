module Z3AuditPr11612

open FStar.Real
module A = FStar.Math.Pow
module M = FStar.Math.Lemmas

#set-options "--fuel 2 --ifuel 2 --z3rlimit 10"

(* Source: fstar/Z3RealPower.fst `signed`, `power` at PR head. Self-contained model:
   the classifier outcome is an abstract parameter. *)
type cls = | Irrational | Rational : numerator:int -> denominator:pos -> cls

let signed (p:int) (a:real) : real = if p % 2 = 0 then a else zero -. a

(* Obligation 1: guard of negated_base_positive is reached on the negative-base branch. *)
let ob1 (x:real)
  : Lemma (requires ~(x == zero) /\ ~(x >. zero)) (ensures zero -. x >. zero) = ()

(* Obligation 2: signed on even numerator is identity. *)
let ob2 (p:int) (a:real)
  : Lemma (requires p % 2 = 0) (ensures signed p a == a) = ()

(* Obligation 3: the PR's rewritten `power` branch equals the old one (the added
   ghost lemma call changes no value); pow is abstract. *)
let power_old (pw:real -> real -> real) (c:real -> cls) (x y:real) : GTot real =
  if y == zero then one
  else if x == zero then zero
  else if x >. zero then pw x y
  else match c y with
       | Irrational -> zero
       | Rational n d -> if d % 2 = 0 then zero else signed n (pw (zero -. x) y)

let power_new (pw:real -> real -> real) (c:real -> cls) (x y:real) : GTot real =
  if y == zero then one
  else if x == zero then zero
  else if x >. zero then pw x y
  else match c y with
       | Irrational -> zero
       | Rational n d -> if d % 2 = 0 then zero else (ob1 x; signed n (pw (zero -. x) y))

let ob3 (pw:real -> real -> real) (c:real -> cls) (x y:real)
  : Lemma (power_old pw c x y == power_new pw c x y) = ()

(* Source: Z3BvFreshModel/Z3BvWord `lemma_concat_number` and `lemma_split_numeral`. *)
let ob4 (v l r v' l' r' p:int)
  : Lemma (requires v == l * p + r /\ v' == v /\ l' == l /\ r' == r)
          (ensures v' == l' * p + r') = ()

let ob5 (x y n p:int)
  : Lemma (requires p > 0 /\ 0 <= y /\ y < p)
          (ensures (x * p + y == n) <==> (x == n / p /\ y == n % p))
  = M.lemma_div_mod n p;
    M.lemma_div_plus y x p;
    M.small_div y p;
    M.lemma_mod_plus y x p;
    M.small_mod y p
