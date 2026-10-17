module Z3SwineInterpolation

(* Discrete, integer-only interpolation; verification status and commands
   are recorded in ZWINE_NFV_REPORT.md.
   No real-exponent convexity or analytic axiom is used. *)
module P = Z3SwinePower
#set-options "--fuel 2 --ifuel 0 --z3rlimit 10 --smtencoding.nl_arith_repr native"

let slope (f:int -> Tot int) (x:int) : int = f (x+1) - f x

let convex (f:int -> Tot int) (low:int) : prop =
  forall (i j:int). low <= i /\ i <= j ==> slope f i <= slope f j

let rec sum_upper (f:int -> Tot int) (a b s:int)
  : Lemma
      (requires a <= b /\
        (forall (i:int). a <= i /\ i < b ==> slope f i <= s))
      (ensures f b - f a <= (b-a)*s)
      (decreases b-a) =
  if a < b then begin
    sum_upper f a (b-1) s;
    assert (slope f (b-1) <= s)
  end

let rec sum_lower (f:int -> Tot int) (a b s:int)
  : Lemma
      (requires a <= b /\
        (forall (i:int). a <= i /\ i < b ==> slope f i >= s))
      (ensures f b - f a >= (b-a)*s)
      (decreases b-a) =
  if a < b then begin
    sum_lower f a (b-1) s;
    assert (slope f (b-1) >= s)
  end

let secant_upper (f:int -> Tot int) (low a b x:int)
  : Lemma
      (requires convex f low /\ low <= a /\ a < b /\ a <= x /\ x <= b)
      (ensures (b-a)*f x <= (b-x)*f a + (x-a)*f b) =
  let s = slope f x in
  assert (forall (i:int). a <= i /\ i < x ==> slope f i <= s);
  assert (forall (i:int). x <= i /\ i < b ==> slope f i >= s);
  sum_upper f a x s;
  sum_lower f x b s;
  assert ((b-x)*(f x-f a) <= (b-x)*(x-a)*s);
  assert ((x-a)*(b-x)*s <= (x-a)*(f b-f x))

(* For integer x there is no point strictly between a and a+1.
   Thus this unit secant is a lower bound on BOTH sides of the anchor.
   This is why the C++ lower guard is x>=1, NOT x>=lo.x. *)
let unit_secant_lower (f:int -> Tot int) (low a x:int)
  : Lemma
      (requires convex f low /\ low <= a /\ low <= x)
      (ensures f x >= f a + slope f a * (x-a)) =
  let s = slope f a in
  if x >= a then begin
    assert (forall (i:int). a <= i /\ i < x ==> slope f i >= s);
    sum_lower f a x s
  end
  else begin
    assert (forall (i:int). x <= i /\ i < a ==> slope f i <= s);
    sum_upper f x a s
  end

let base_slope (n:nat) (x:int) : int = P.power (x+1) n - P.power x n

let rec base_slope_monotone (n:nat) (x z:pos)
  : Lemma (requires x <= z)
          (ensures 0 <= base_slope n x /\ base_slope n x <= base_slope n z)
          (decreases n) =
  P.base_monotone x (x+1) n;
  if n > 0 then begin
    base_slope_monotone (n-1) x z;
    P.base_monotone (x+1) (z+1) (n-1);
    assert (base_slope n x ==
      x * base_slope (n-1) x + P.power (x+1) (n-1));
    assert (base_slope n z ==
      z * base_slope (n-1) z + P.power (z+1) (n-1));
    assert (x * base_slope (n-1) x <= z * base_slope (n-1) x);
    assert (z * base_slope (n-1) x <= z * base_slope (n-1) z)
  end

let base_convex (n:nat)
  : Lemma (convex (fun x -> P.power x n) 1) =
  let each_x (x:int)
    : Lemma (forall (z:int). 1 <= x /\ x <= z ==>
               slope (fun k -> P.power k n) x <=
               slope (fun k -> P.power k n) z) =
    let each_z (z:int)
      : Lemma (1 <= x /\ x <= z ==>
                 slope (fun k -> P.power k n) x <=
                 slope (fun k -> P.power k n) z) =
      if 1 <= x /\ x <= z then base_slope_monotone n x z
    in FStar.Classical.forall_intro each_z
  in FStar.Classical.forall_intro each_x

(* The extension below zero is immaterial: convexity is used only for
   nonnegative exponents. No negative exponent is silently reciprocal. *)
let exponent_function (x:pos) (n:int) : int =
  P.power x (if n < 0 then 0 else n)

let exponent_slope_monotone (x:pos) (m n:nat)
  : Lemma (requires m <= n)
          (ensures slope (exponent_function x) m <= slope (exponent_function x) n) =
  P.exponent_monotone x m n;
  assert (slope (exponent_function x) m == (x-1)*P.power x m);
  assert (slope (exponent_function x) n == (x-1)*P.power x n)

let exponent_convex (x:pos)
  : Lemma (convex (exponent_function x) 0) =
  let each_m (m:int)
    : Lemma (forall (n:int). 0 <= m /\ m <= n ==>
               slope (exponent_function x) m <= slope (exponent_function x) n) =
    let each_n (n:int)
      : Lemma (0 <= m /\ m <= n ==>
                 slope (exponent_function x) m <= slope (exponent_function x) n) =
      if 0 <= m /\ m <= n then exponent_slope_monotone x m n
    in FStar.Classical.forall_intro each_n
  in FStar.Classical.forall_intro each_m

(* Exact arithmetic expression built by arith_swine::interpolant.
   Degenerate widths use 1, but the corner values still use a,b,c,d. *)
let width (a b:int) : int = if a = b then 1 else b-a

let numerator (x y a b c d:int) : int =
  let dx = width a b in
  let dy = width c d in
  let lower = dx * P.exp a c + (P.exp b c - P.exp a c)*(x-a) in
  let upper = dx * P.exp a d + (P.exp b d - P.exp a d)*(x-a) in
  dy*lower + (upper-lower)*(y-c)

let upper_clause (x y a b c d:int) : prop =
  (a <= x /\ x <= b /\ c <= y /\ y <= d) ==>
    width a b * width c d * P.exp x y <= numerator x y a b c d

(* Pure polynomial identities are checked without recursive-power terms
   or convexity quantifiers in the solver context. *)
let linear_identity (x a b f0 f1:int)
  : Lemma ((b-a)*f0 + (f1-f0)*(x-a) ==
           (b-x)*f0 + (x-a)*f1) = ()

let weighted_identity (k u v f g:int)
  : Lemma (k*(u*f+v*g) == u*(k*f)+v*(k*g)) =
  calc (==) {
    k*(u*f+v*g);
    == { FStar.Math.Lemmas.distributivity_add_right k (u*f) (v*g) }
    k*(u*f)+k*(v*g);
    == { P.mul_assoc k u f; P.mul_assoc k v g }
    (k*u)*f+(k*v)*g;
    == { FStar.Math.Lemmas.swap_mul k u; FStar.Math.Lemmas.swap_mul k v }
    (u*k)*f+(v*k)*g;
    == { P.mul_assoc u k f; P.mul_assoc v k g }
    u*(k*f)+v*(k*g);
  }

let bilinear_identity (x y a b c d f00 f01 f10 f11:int)
  : Lemma (
    (d-c)*((b-a)*f00+(f10-f00)*(x-a)) +
    (((b-a)*f01+(f11-f01)*(x-a)) -
     ((b-a)*f00+(f10-f00)*(x-a)))*(y-c)
    ==
    (b-x)*((d-y)*f00+(y-c)*f01) +
    (x-a)*((d-y)*f10+(y-c)*f11)) =
  calc (==) {
    (d-c)*((b-a)*f00+(f10-f00)*(x-a)) +
    (((b-a)*f01+(f11-f01)*(x-a)) -
     ((b-a)*f00+(f10-f00)*(x-a)))*(y-c);
    == { _ by (FStar.Tactics.Canon.canon()) }
    (b-x)*((d-y)*f00+(y-c)*f01) +
    (x-a)*((d-y)*f10+(y-c)*f11);
  }

let degenerate_y_numerator (x a b:int) (c:nat)
  : Lemma (requires a < b)
          (ensures numerator x c a b c c ==
            (b-x)*P.power a c+(x-a)*P.power b c) =
  P.rewrite_nonnegative_numeral a c;
  P.rewrite_nonnegative_numeral b c;
  assert (width a b == b-a /\ width c c == 1);
  assert (numerator x c a b c c ==
    (b-a)*P.power a c+(P.power b c-P.power a c)*(x-a));
  linear_identity x a b (P.power a c) (P.power b c)

let upper_sound (x y:int) (a b:pos) (c d:pos)
  : Lemma (requires a <= b /\ c <= d)
          (ensures upper_clause x y a b c d) =
  if a <= x /\ x <= b /\ c <= y /\ y <= d then begin
    P.rewrite_nonnegative_numeral x y;
    P.rewrite_nonnegative_numeral a y;
    P.rewrite_nonnegative_numeral b y;
    P.rewrite_nonnegative_numeral a c;
    P.rewrite_nonnegative_numeral a d;
    P.rewrite_nonnegative_numeral b c;
    P.rewrite_nonnegative_numeral b d;
    base_convex y;
    exponent_convex a;
    exponent_convex b;
    if a = b then begin
      if c < d then secant_upper (exponent_function a) 0 c d y
    end
    else if c = d then begin
      assert (y == c);
      secant_upper (fun z -> P.power z y) 1 a b x;
      degenerate_y_numerator x a b c
    end
    else begin
      secant_upper (fun z -> P.power z y) 1 a b x;
      secant_upper (exponent_function a) 0 c d y;
      secant_upper (exponent_function b) 0 c d y;
      assert ((d-c)*(b-a)*P.power x y <=
        (d-c)*((b-x)*P.power a y + (x-a)*P.power b y));
      assert ((b-x)*((d-c)*P.power a y) <=
        (b-x)*((d-y)*P.power a c + (y-c)*P.power a d));
      assert ((x-a)*((d-c)*P.power b y) <=
        (x-a)*((d-y)*P.power b c + (y-c)*P.power b d));
      weighted_identity (d-c) (b-x) (x-a) (P.power a y) (P.power b y);
      assert ((d-c)*(b-a)*P.power x y <=
        (b-x)*((d-y)*P.power a c+(y-c)*P.power a d) +
        (x-a)*((d-y)*P.power b c+(y-c)*P.power b d));
      bilinear_identity x y a b c d
        (P.exp a c) (P.exp a d) (P.exp b c) (P.exp b d);
      assert (numerator x y a b c d ==
        (b-x)*((d-y)*P.power a c+(y-c)*P.power a d) +
        (x-a)*((d-y)*P.power b c+(y-c)*P.power b d))
    end
  end

(* At a fixed nonnegative exponent-offset t, the exponent unit secant is
   H(x)=x^c*(1+t*(x-1)). It is convex in x>=1, despite its equivalent
   (1-t)*x^c + t*x^(c+1) having a potentially negative coefficient.
   Applying separate lower bounds to those two terms would be invalid. *)
let lower_function (c t:nat) (x:int) : int =
  P.power x c * (1+t*(x-1))

let slope_polynomial (x t v w:int)
  : Lemma (w*(1+t*x)-v*(1+t*(x-1)) ==
           t*v+(1+t*x)*(w-v)) = ()

let lower_function_slope (c t:nat) (x:int)
  : Lemma (slope (lower_function c t) x ==
           t*P.power x c+(1+t*x)*base_slope c x) =
  assert (lower_function c t (x+1) ==
    P.power (x+1) c * (1+t*x));
  slope_polynomial x t (P.power x c) (P.power (x+1) c)

let lower_slope_monotone (c t:nat) (x z:pos)
  : Lemma (requires x <= z)
          (ensures slope (lower_function c t) x <=
                   slope (lower_function c t) z) =
  base_slope_monotone c x z;
  P.base_monotone x z c;
  lower_function_slope c t x;
  lower_function_slope c t z;
  assert (t*P.power x c <= t*P.power z c);
  assert ((1+t*x)*base_slope c x <= (1+t*z)*base_slope c x);
  assert ((1+t*z)*base_slope c x <= (1+t*z)*base_slope c z)

let lower_function_convex (c t:nat)
  : Lemma (convex (lower_function c t) 1) =
  let each_x (x:int)
    : Lemma (forall (z:int). 1 <= x /\ x <= z ==>
               slope (lower_function c t) x <= slope (lower_function c t) z) =
    let each_z (z:int)
      : Lemma (1 <= x /\ x <= z ==>
                 slope (lower_function c t) x <= slope (lower_function c t) z) =
      if 1 <= x /\ x <= z then lower_slope_monotone c t x z
    in FStar.Classical.forall_intro each_z
  in FStar.Classical.forall_intro each_x

let unit_polynomial (x a t v w:int)
  : Lemma (
    v+(w-v)*(x-a) +
    (a*v+((a+1)*w-a*v)*(x-a) - (v+(w-v)*(x-a)))*t
    ==
    v*(1+t*(a-1)) + (t*v+(1+t*a)*(w-v))*(x-a)) =
  calc (==) {
    v+(w-v)*(x-a) +
    (a*v+((a+1)*w-a*v)*(x-a) - (v+(w-v)*(x-a)))*t;
    == { _ by (FStar.Tactics.Canon.canon()) }
    v*(1+t*(a-1)) + (t*v+(1+t*a)*(w-v))*(x-a);
  }

(* Transfer only the unit-cell polynomial here, before importing any
   quantified convexity facts into the final lower-bound proof. *)
let lower_numerator_identity (x y:int) (a c:pos)
  : Lemma (requires y >= c)
          (ensures numerator x y a (a+1) c (c+1) ==
            lower_function c (y-c) a +
            slope (lower_function c (y-c)) a * (x-a)) =
  let t = y-c in
  let v = P.power a c in
  let w = P.power (a+1) c in
  P.rewrite_nonnegative_numeral a c;
  P.rewrite_nonnegative_numeral (a+1) c;
  P.rewrite_nonnegative_numeral a (c+1);
  P.rewrite_nonnegative_numeral (a+1) (c+1);
  P.power_succ a c;
  P.power_succ (a+1) c;
  lower_function_slope c t a;
  assert (width a (a+1) == 1 /\ width c (c+1) == 1);
  assert (numerator x y a (a+1) c (c+1) ==
    v+(w-v)*(x-a) +
    (a*v+((a+1)*w-a*v)*(x-a) - (v+(w-v)*(x-a)))*t);
  unit_polynomial x a t v w

let lower_clause (x y a c:int) : prop =
  (x >= 1 /\ y >= c) ==>
    P.exp x y >= numerator x y a (a+1) c (c+1)

let lower_sound (x y:int) (a c:pos)
  : Lemma (lower_clause x y a c) =
  if x >= 1 /\ y >= c then begin
    let t = y-c in
    exponent_convex x;
    unit_secant_lower (exponent_function x) 0 c y;
    assert (P.power x y >= lower_function c t x);
    lower_function_convex c t;
    unit_secant_lower (lower_function c t) 1 a x;
    lower_numerator_identity x y a c
  end
