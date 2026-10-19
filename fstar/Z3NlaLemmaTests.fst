module Z3NlaLemmaTests

open Z3NlaLemma
module N = Z3NlaLemma
module P = Z3LinearArithmeticTheory

let x : N.poly = P.variable [0]
let y : N.poly = P.variable [1]
let xy : N.poly = N.multiply x y
let negative (p:N.poly) : N.poly = P.scale (-1) 1 p
let minus (p q:N.poly) : N.poly = P.add p (negative q)

let plane_inputs : list N.fact = [
  { poly = minus x (P.constant 2 1); relation = N.Positive };
  { poly = minus y (P.constant 3 1); relation = N.Positive };
  { poly = P.add (negative xy)
      (P.add (P.scale 3 1 x) (P.add (P.scale 2 1 y) (P.constant (-6) 1)));
    relation = N.Nonnegative }
]

let plane_steps : list N.step = [
  N.Input 0; N.Input 1; N.Input 2; N.Product 0 1;
  N.Linear 0 [(2, 1); (3, 1)]
]

let tangent_plane () : Lemma (N.check plane_inputs plane_steps 4) =
  assert_norm (N.check plane_inputs plane_steps 4)

let line_inputs : list N.fact = [
  { poly = minus x (P.constant 2 1); relation = N.Equal };
  { poly = minus xy (P.scale 2 1 y); relation = N.Nonzero }
]

let line_steps : list N.step = [
  N.Input 0; N.Input 1; N.ZeroProduct 0 y;
  N.Linear 0 [(1, 1); (2, -1)]
]

let tangent_line () : Lemma (N.check line_inputs line_steps 3) =
  assert_norm (N.check line_inputs line_steps 3)

let square_inputs : list N.fact = [
  { poly = negative (N.multiply x x); relation = N.Positive }
]

let square_steps : list N.step = [
  N.Input 0; N.Square x; N.Linear 0 [(0, 1); (1, 1)]
]

let square_nonnegative () : Lemma (N.check square_inputs square_steps 2) =
  assert_norm (N.check square_inputs square_steps 2)

let malformed () : Lemma (
  not (N.check plane_inputs [N.Input 3] 0) /\
  not (N.check plane_inputs [N.Product 0 0] 0) /\
  not (N.check plane_inputs [N.Input 0; N.Linear 0 [(0, -1)]] 1) /\
  not (N.check [
    { poly = x; relation = N.Nonzero };
    { poly = x; relation = N.Nonzero }]
    [N.Input 0; N.Input 1; N.Linear 0 [(0, 1); (1, -1)]] 2)) =
  assert_norm (
    not (N.check plane_inputs [N.Input 3] 0) /\
    not (N.check plane_inputs [N.Product 0 0] 0) /\
    not (N.check plane_inputs [N.Input 0; N.Linear 0 [(0, -1)]] 1) /\
    not (N.check [
      { poly = x; relation = N.Nonzero };
      { poly = x; relation = N.Nonzero }]
      [N.Input 0; N.Input 1; N.Linear 0 [(0, 1); (1, -1)]] 2))
