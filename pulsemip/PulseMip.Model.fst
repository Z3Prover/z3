module PulseMip.Model

open FStar.Real
module L = FStar.List.Tot
module P = Z3LinearArithmeticTheory
module Q = PulseMip.Rational

type polynomial = P.polynomial nat
type point = list Q.rational
type problem = {
  variables:nat;
  integers:list nat;
  constraints:list polynomial;
  objective:polynomial;
}

let rec at (xs:point) (v:nat) : Tot Q.rational (decreases xs) =
  match xs with [] -> Q.zero | x :: rest -> if v = 0 then x else at rest (v - 1)

let rec put (xs:point) (v:nat) (x:Q.rational) : Tot point (decreases xs) =
  match xs with [] -> [] | y :: rest -> if v = 0 then x :: rest else y :: put rest (v - 1) x

let rec coefficients_valid (n:nat) (ms:list (int & nat)) : Tot bool (decreases ms) =
  match ms with [] -> true | (_, v) :: rest -> v >= 0 && v < n && coefficients_valid n rest

let polynomial_valid (n:nat) (p:polynomial) : bool =
  p.denom = 1 && coefficients_valid n p.mono

let rec rows_valid (n:nat) (rows:list polynomial) : Tot bool (decreases rows) =
  match rows with [] -> true | p :: rest -> polynomial_valid n p && rows_valid n rest

let rec indices_valid (n:nat) (vs:list nat) : Tot bool (decreases vs) =
  match vs with [] -> true | v :: rest -> v >= 0 && v < n && indices_valid n rest

let valid (p:problem) : bool =
  p.variables >= 0 && indices_valid p.variables p.integers && rows_valid p.variables p.constraints &&
  polynomial_valid p.variables p.objective

let rec eval_terms (ms:list (int & nat)) (x:point) : Tot Q.rational (decreases ms) =
  match ms with [] -> Q.zero | (c, v) :: rest -> Q.add (Q.mul_int c (at x v)) (eval_terms rest x)

let eval (p:polynomial) (x:point) : Q.rational = Q.add (Q.integer p.cst) (eval_terms p.mono x)

let rec feasible_rows (rows:list polynomial) (x:point) : Tot bool (decreases rows) =
  match rows with [] -> true | p :: rest -> Q.le (eval p x) Q.zero && feasible_rows rest x

let rec integral_on (vs:list nat) (x:point) : Tot bool (decreases vs) =
  match vs with [] -> true | v :: rest -> Q.integral (at x v) && integral_on rest x

let rec point_valid (x:point) : Tot bool (decreases x) =
  match x with [] -> true | q :: rest -> q.den > 0 && point_valid rest

let feasible (p:problem) (x:point) : bool =
  point_valid x && L.length x = p.variables && feasible_rows p.constraints x && integral_on p.integers x

let valuation (x:point) : nat -> real = fun v -> Q.value (at x v)

let rec rows_hold (rows:list polynomial) (rho:nat -> real) : Tot prop (decreases rows) =
  match rows with [] -> True | p :: rest -> P.value p rho <=. 0.0R /\ rows_hold rest rho

let mixed (p:problem) (rho:nat -> real) (ints:nat -> int) : prop =
  rows_hold p.constraints rho /\
  (forall (v:nat). L.mem v p.integers ==> rho v == of_int (ints v))

let rec lemma_eval_terms (ms:list (int & nat)) (x:point)
  : Lemma (Q.value (eval_terms ms x) == P.monomial_value ms (valuation x)) (decreases ms) =
  match ms with
  | [] -> ()
  | (c, v) :: rest ->
    lemma_eval_terms rest x;
    Q.lemma_mul_int c (at x v);
    Q.lemma_add (Q.mul_int c (at x v)) (eval_terms rest x)

let lemma_eval (p:polynomial) (x:point)
  : Lemma (Q.value (eval p x) == P.value p (valuation x)) =
  lemma_eval_terms p.mono x;
  Q.lemma_integer p.cst;
  Q.lemma_add (Q.integer p.cst) (eval_terms p.mono x)

let rec lemma_feasible_rows (rows:list polynomial) (x:point)
  : Lemma (requires feasible_rows rows x) (ensures rows_hold rows (valuation x)) (decreases rows) =
  match rows with
  | [] -> ()
  | p :: rest ->
    lemma_eval p x;
    Q.lemma_le (eval p x) Q.zero;
    lemma_feasible_rows rest x

let rec lemma_integral_on (vs:list nat) (x:point) (v:nat)
  : Lemma (requires integral_on vs x /\ L.mem v vs)
          (ensures Q.value (at x v) == of_int (Q.floor (at x v))) (decreases vs) =
  match vs with
  | [] -> ()
  | w :: rest -> if v = w then Q.lemma_integral (at x v) else lemma_integral_on rest x v

let lemma_feasible (p:problem) (x:point)
  : Lemma (requires feasible p x)
          (ensures mixed p (valuation x) (fun v -> Q.floor (at x v))) =
  lemma_feasible_rows p.constraints x;
  let each (v:nat)
    : Lemma (L.mem v p.integers ==> Q.value (at x v) == of_int (Q.floor (at x v))) =
    if L.mem v p.integers then lemma_integral_on p.integers x v in
  FStar.Classical.forall_intro each

let lower_branch (v:nat) (k:int) : polynomial = { mono = [(1, v)]; cst = -k; denom = 1 }
let upper_branch (v:nat) (k:int) : polynomial = { mono = [(-1, v)]; cst = k + 1; denom = 1 }
