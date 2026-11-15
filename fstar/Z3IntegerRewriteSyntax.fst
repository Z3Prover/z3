module Z3IntegerRewriteSyntax

open Z3AstTheory
open Z3ClauseSyntax
open Z3ProofIndex
module A = Z3LinearArithmeticAst
module P = Z3LinearArithmeticTheory
module R = Z3ArithmeticSyntax

let absolute (n:int) : nat = if n < 0 then -n else n

let implication_coefficients (premise conclusion:expr) : option (list A.coefficient) =
  A.prepare_literal (1, 1) true premise >>= (fun p ->
  A.prepare_literal (1, 1) false conclusion >>= (fun q ->
  R.first_nonzero (P.collect p.poly.mono []) >>= (fun (a, e) ->
  let b = R.coefficient e (P.collect q.poly.mono []) in
  if a = 0 || b = 0 || (a > 0) = (b > 0) then None
  else
    let cs:list A.coefficient =
      [(absolute b * p.poly.denom, 1); (absolute a * q.poly.denom, 1)] in
    Some cs)))

let implication (premise conclusion:expr) : bool =
  match implication_coefficients premise conclusion with
  | Some cs -> A.check cs conclusion [premise]
  | None -> false

let rounded_equivalent (s t:expr) : bool =
  get_sort s = bool_sort && get_sort t = bool_sort &&
  implication s t && implication t s

let gcd = P.gcd

let rec divisor (ms:list (int & expr)) : Tot nat (decreases ms) =
  match ms with [] -> 0 | (n, _) :: rest -> gcd (absolute n) (divisor rest)

let rec divisible_terms (d:pos) (ms:list (int & expr))
  : Tot bool (decreases ms) =
  match ms with
  | [] -> true
  | (n, e) :: rest -> n % d = 0 && get_sort e = A.int_s && divisible_terms d rest

let indivisible_equation (e:expr) : bool =
  match R.equation_of e with
  | None -> false
  | Some p ->
    let ms = P.collect p.mono [] in
    let d = divisor ms in
    d > 1 && p.cst % d <> 0 && divisible_terms d ms

let equivalent (s t:expr) : bool =
  rounded_equivalent s t ||
  (t = false_expr && indivisible_equation s) ||
  (s = false_expr && indivisible_equation t)

