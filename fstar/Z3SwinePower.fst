module Z3SwinePower

(* Checked by the parent WSL F* session with stock Z3 4.13.3.
   See ZWINE_NFV_REPORT.md for commands and audit boundaries.
   Integer power is not the reciprocal-based real power operation. *)

#set-options "--fuel 2 --ifuel 0 --z3rlimit 10"

let magnitude (y:int) : nat = if y < 0 then -y else y

let rec power (x:int) (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else x * power x (n - 1)

let exp (x y:int) : int = power x (magnitude y)

let power_succ (x:int) (n:nat)
  : Lemma (power x (n+1) == x*power x n) = ()

let power_zero (x:int) : Lemma (power x 0 == 1) = ()

let magnitude_neg (y:int) : Lemma (magnitude (-y) == magnitude y) =
  if y < 0 then () else ()

let magnitude_product (y z:int)
  : Lemma (magnitude (y*z) == magnitude y * magnitude z) =
  if y < 0 then (if z < 0 then () else ())
  else (if z < 0 then () else ())

let magnitude_parity (y:int)
  : Lemma (magnitude y % 2 == y % 2) =
  if y < 0 then () else ()

(* Keep polynomial normalization out of recursive-power VCs. *)
let mul_assoc (a b c:int)
  : Lemma ((a*b)*c == a*(b*c)) = ()

let mul_four (a b c d:int)
  : Lemma ((a*b)*(c*d) == (a*c)*(b*d)) = ()

let rec power_add (x:int) (m n:nat)
  : Lemma (ensures power x (m+n) == power x m * power x n)
          (decreases m) =
  if m > 0 then begin
    power_add x (m-1) n;
    assert (m+n-1 == (m-1)+n);
    assert (power x (m+n) == x * power x ((m-1)+n));
    assert (power x m == x * power x (m-1));
    mul_assoc x (power x (m-1)) (power x n);
    assert (x * (power x (m-1) * power x n) ==
      (x * power x (m-1)) * power x n)
  end

let rec power_product (x z:int) (n:nat)
  : Lemma (ensures power (x*z) n == power x n * power z n)
          (decreases n) =
  if n > 0 then begin
    power_product x z (n-1);
    assert (power (x*z) n == (x*z)*power (x*z) (n-1));
    assert (power x n == x*power x (n-1));
    assert (power z n == z*power z (n-1));
    mul_four x z (power x (n-1)) (power z (n-1))
  end

let rec power_merge (x:int) (m n:nat)
  : Lemma (ensures power (power x m) n == power x (m*n))
          (decreases n) =
  if n > 0 then begin
    power_merge x m (n-1);
    power_add x m (m*(n-1));
    assert (m*n == m + m*(n-1))
  end

let rec power_one_base (n:nat)
  : Lemma (ensures power 1 n == 1) (decreases n) =
  if n > 0 then power_one_base (n-1)

let rec power_nonzero (x:int) (n:nat)
  : Lemma (requires x <> 0) (ensures power x n <> 0)
          (decreases n) =
  if n > 0 then power_nonzero x (n-1)

let power_zero_base (n:pos) : Lemma (power 0 n == 0) = ()

let rec power_positive (x:pos) (n:nat)
  : Lemma (ensures power x n >= 1) (decreases n) =
  if n > 0 then power_positive x (n-1)

let rec power_nonnegative (x:nat) (n:nat)
  : Lemma (ensures power x n >= 0) (decreases n) =
  if n > 0 then power_nonnegative x (n-1)

let rec power_sign (x:int) (n:nat)
  : Lemma (ensures power (-x) n ==
            (if n % 2 = 0 then power x n else -power x n))
          (decreases n) =
  if n > 0 then begin
    power_sign x (n-1);
    assert (n % 2 == 0 \/ n % 2 == 1);
    assert ((n-1) % 2 == (if n % 2 == 0 then 1 else 0))
  end

let rec base_monotone (x z:nat) (n:nat)
  : Lemma (requires x <= z) (ensures power x n <= power z n)
          (decreases n) =
  if n > 0 then begin
    base_monotone x z (n-1);
    power_nonnegative x (n-1);
    power_nonnegative z (n-1);
    assert (x * power x (n-1) <= z * power x (n-1))
  end

let rec base_strict (x z:pos) (n:pos)
  : Lemma (requires x < z) (ensures power x n < power z n)
          (decreases n) =
  if n = 1 then ()
  else begin
    base_strict x z (n-1);
    power_positive x (n-1);
    power_positive z (n-1);
    assert (x * power x (n-1) < z * power x (n-1))
  end

let rec exponent_monotone (x:pos) (m n:nat)
  : Lemma (requires m <= n) (ensures power x m <= power x n)
          (decreases n) =
  if m < n then begin
    exponent_monotone x m (n-1);
    power_positive x (n-1)
  end

let rec exponent_strict (x:int{x > 1}) (m n:nat)
  : Lemma (requires m < n) (ensures power x m < power x n)
          (decreases n) =
  power_positive x (n-1);
  if m < n-1 then exponent_strict x m (n-1)

(* The exceptional (2,2) is excluded by the emitted x+y>4 guard. *)
let rec growth (x:int{x > 1}) (n:int{n > 1})
  : Lemma (requires x+n > 4)
          (ensures power x n > x*n+1)
          (decreases n) =
  if n = 2 then begin
    assert (x >= 3);
    power_zero x;
    power_succ x 0;
    power_succ x 1;
    assert (power x 2 == x*x);
    assert ((x-1)*(x-1) >= 4)
  end
  else if n = 3 then begin
    power_zero x;
    power_succ x 0;
    power_succ x 1;
    power_succ x 2;
    assert (power x 3 == x*x*x);
    assert (x*x >= 2*x);
    assert (x*x*x >= 4*x)
  end
  else begin
    growth x (n-1);
    assert (power x (n-1) >= x*(n-1)+2);
    assert (x*x*(n-1) >= 2*x*(n-1));
    assert (2*x*(n-1)+2*x > x*n+1)
  end

(* Integer rewriter laws, all signs and 0^0 included. *)
let rewrite_zero (x:int) : Lemma (exp x 0 == 1) = ()
let rewrite_one (x:int) : Lemma (exp x 1 == x) = ()
let rewrite_one_base (y:int) : Lemma (exp 1 y == 1) =
  power_one_base (magnitude y)
let rewrite_neg_exponent (x y:int) : Lemma (exp x (-y) == exp x y) =
  magnitude_neg y
let rewrite_minus_one_base (y:int)
  : Lemma (exp (-1) y == (if y%2 = 0 then 1 else -1)) =
  magnitude_parity y;
  power_one_base (magnitude y);
  power_sign 1 (magnitude y)
let rewrite_zero_base (y:int)
  : Lemma (exp 0 y == (if y = 0 then 1 else 0)) =
  if y <> 0 then power_zero_base (magnitude y)

(* power is defined above as precisely the product of n copies of x.
   This identity covers all nonnegative numeral expansion limits, not
   only the implementation's eager n<=10 threshold. *)
let rewrite_nonnegative_numeral (x:int) (n:nat)
  : Lemma (exp x n == power x n) = ()
let rewrite_nested (x y z:int)
  : Lemma (exp (exp x y) z == exp x (y*z)) =
  magnitude_product y z;
  power_merge x (magnitude y) (magnitude z)
let rewrite_common_exponent (x z y:int)
  : Lemma (exp x y * exp z y == exp (x*z) y) =
  power_product x z (magnitude y)

(* Mathematical repeated-squaring kernel with explicit resource exhaustion.
   Neither None nor exhaustion is an accepted candidate. This is not an
   extraction/refinement proof of rational::bitsize or ast_manager::inc. *)
let halve (x:int) (n:nat)
  : Lemma (power x n ==
      (if n % 2 = 0 then 1 else x) * power (x*x) (n/2)) =
  assert (n == 2*(n/2) + n%2);
  assert (n%2 == 0 \/ n%2 == 1);
  power_merge x 2 (n/2);
  power_add x (2*(n/2)) (n%2)

let rec square_budget (budget:nat) (x:int) (n:nat)
  : Tot (r:option int{
      match r with | None -> True | Some v -> v == power x n})
      (decreases budget) =
  if n = 0 then Some 1
  else if budget = 0 then None
  else
    let tail = square_budget (budget-1) (x*x) (n/2) in
    halve x n;
    match tail with
    | None -> None
    | Some v -> Some (if n%2 = 0 then v else x*v)

let checked_acceptance (x y candidate:int) (budget:nat)
  : Lemma (requires square_budget budget x (magnitude y) == Some candidate)
          (ensures candidate == exp x y) = ()
