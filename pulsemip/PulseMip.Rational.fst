module PulseMip.Rational

open FStar.Real

#set-options "--z3rlimit 10 --smtencoding.nl_arith_repr native"

type rational = { num:int; den:pos }

let zero : rational = { num = 0; den = 1 }
let one : rational = { num = 1; den = 1 }
let integer (n:int) : rational = { num = n; den = 1 }
let neg (x:rational) : rational = { x with num = -x.num }
let add (x y:rational) : rational =
  if x.den = y.den then { num = x.num + y.num; den = x.den }
  else { num = x.num * y.den + y.num * x.den; den = x.den * y.den }
let mul_int (n:int) (x:rational) : rational = { x with num = n * x.num }
let div_pos (x:rational) (n:pos) : rational = { x with den = x.den * n }
let le (x y:rational) : bool = x.num * y.den <= y.num * x.den
let equal (x y:rational) : bool = x.num * y.den = y.num * x.den
let integral (x:rational) : bool = x.num % x.den = 0
let floor (x:rational) : int = x.num / x.den

let value (x:rational) : real = of_int x.num /. of_int x.den

#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0"

let lemma_fraction (n:int) (d:pos)
  : Lemma (of_int d *. (of_int n /. of_int d) == of_int n) = ()

let lemma_int_product (n m:int)
  : Lemma (of_int (n * m) == of_int n *. of_int m) = ()

let lemma_int_sum (n m:int)
  : Lemma (of_int (n + m) == of_int n +. of_int m) = ()

let lemma_cancel (d:pos) (x y:real)
  : Lemma (requires of_int d *. x == of_int d *. y) (ensures x == y) = ()

let lemma_cross_order (a b:int) (d e:pos)
  : Lemma ((a * e <= b * d) <==>
           (of_int a /. of_int d <=. of_int b /. of_int e)) =
  lemma_int_product a e;
  lemma_int_product b d

let lemma_add_cross (a b n m x y z:real)
  : Lemma (requires a >. 0.0R /\ b >. 0.0R /\
                    a *. x == n /\ b *. y == m /\
                    (a *. b) *. z == n *. b +. m *. a)
          (ensures z == x +. y) = ()

#pop-options

let lemma_integer (n:int) : Lemma (value (integer n) == of_int n) = ()

let lemma_add (x y:rational)
  : Lemma (value (add x y) == value x +. value y) =
  lemma_fraction x.num x.den;
  lemma_fraction y.num y.den;
  lemma_int_sum x.num y.num;
  lemma_int_product x.num y.den;
  lemma_int_product y.num x.den;
  lemma_int_product x.den y.den;
  lemma_int_sum (x.num * y.den) (y.num * x.den);
  lemma_fraction (add x y).num (add x y).den;
  if x.den = y.den then lemma_cancel x.den (value (add x y)) (value x +. value y)
  else (
    assert ((add x y).den == x.den * y.den);
    assert ((add x y).num == x.num * y.den + y.num * x.den);
    lemma_add_cross (of_int x.den) (of_int y.den) (of_int x.num) (of_int y.num)
      (value x) (value y) (value (add x y)))

let lemma_mul_int (n:int) (x:rational)
  : Lemma (value (mul_int n x) == of_int n *. value x) =
  lemma_fraction x.num x.den;
  lemma_int_product n x.num;
  lemma_fraction (n * x.num) x.den;
  lemma_cancel x.den (value (mul_int n x)) (of_int n *. value x)

let lemma_le (x y:rational) : Lemma (le x y <==> value x <=. value y) =
  lemma_cross_order x.num y.num x.den y.den

let lemma_integral (x:rational)
  : Lemma (requires integral x) (ensures value x == of_int (floor x)) =
  assert (x.num == (x.num / x.den) * x.den + x.num % x.den);
  lemma_fraction x.num x.den;
  lemma_int_product (floor x) x.den;
  lemma_cancel x.den (value x) (of_int (floor x))
