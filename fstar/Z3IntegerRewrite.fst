module Z3IntegerRewrite

open FStar.Real
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3ProofIndex
module A = Z3LinearArithmeticAst
module E = Z3LinearArithmeticEmbed
module P = Z3LinearArithmeticTheory
module R = Z3ArithmeticRewrite

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

let lemma_implication_sound (i:interpretation value) (rho:env value)
                            (s t:expr)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    implication s t /\ lit_true i rho s)
          (ensures lit_true i rho t) =
  match implication_coefficients s t with
  | Some cs -> E.lemma_check_with_numeric_model cs t [s] i rho
  | None -> ()

let lemma_rounded_equivalent_sound (i:interpretation value) (rho:env value) (s t:expr)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\
                    rounded_equivalent s t)
          (ensures eval i s rho == eval i t rho) =
  FStar.Classical.impl_intro #(lit_true i rho s) #(lit_true i rho t)
    (fun _ -> lemma_implication_sound i rho s t);
  FStar.Classical.impl_intro #(lit_true i rho t) #(lit_true i rho s)
    (fun _ -> lemma_implication_sound i rho t s);
  match eval i s rho, eval i t rho with VBool _, VBool _ -> () | _, _ -> ()

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

let rec quotient_value (d:pos) (ms:list (int & expr))
                       (i:interpretation value) (rho:env value)
  : GTot int (decreases ms) =
  match ms with
  | [] -> 0
  | (n, e) :: rest -> (n / d) * E.integer_value (eval i e rho) + quotient_value d rest i rho

#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0 --smtencoding.nl_arith_repr native"

let lemma_quotient_step (d:pos) (q k tail:int)
  : Lemma (of_int (d * q) *. of_int k +. of_int (d * tail) ==
           of_int (d * (q * k + tail))) =
  P.lemma_of_int_product (d * q) k;
  P.lemma_of_int_sum ((d * q) * k) (d * tail);
  assert ((d * q) * k + d * tail == d * (q * k + tail))

#pop-options

let rec lemma_quotient_value (d:pos) (ms:list (int & expr))
                             (i:interpretation value) (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ divisible_terms d ms)
          (ensures P.monomial_value ms (E.valuation i nu rho) ==
                   of_int (d * quotient_value d ms i rho))
          (decreases ms) =
  match ms with
  | [] -> ()
  | (n, e) :: rest ->
    lemma_quotient_value d rest i nu rho;
    FStar.Math.Lemmas.lemma_div_mod n d;
    assert (n % d = 0 /\ n = d * (n / d));
    (match eval i e rho with
     | VInt k ->
       let tail = quotient_value d rest i rho in
       lemma_quotient_step d (n / d) k tail;
       assert (P.monomial_value ms (E.valuation i nu rho) ==
               of_int n *. of_int k +. of_int (d * tail));
       assert (quotient_value d ms i rho == (n / d) * k + tail)
     | _ -> ())

let lemma_indivisible_equation (e:expr) (i:interpretation value)
                               (nu:value -> real) (rho:env value)
  : Lemma (requires E.numeric_model i nu /\ eq_sound i /\ indivisible_equation e)
          (ensures ~(lit_true i rho e)) =
  let p = Some?.v (R.equation_of e) in
  let ms = P.collect p.mono [] in
  let d = divisor ms in
  assert (d > 1 /\ p.cst % d <> 0 /\ divisible_terms d ms);
  R.lemma_equation_of e p i nu rho;
  P.lemma_collect p.mono [] (E.valuation i nu rho);
  lemma_quotient_value d ms i nu rho;
  let q = quotient_value d ms i rho in
  FStar.Math.Lemmas.lemma_mod_plus p.cst q d;
  assert (p.cst + d * q <> 0)

let equivalent (s t:expr) : bool =
  rounded_equivalent s t ||
  (t = false_expr && indivisible_equation s) ||
  (s = false_expr && indivisible_equation t)

let lemma_equation_sort (e:expr)
  : Lemma (requires Some? (R.equation_of e))
          (ensures get_sort e == bool_sort) =
  match e with App _ [_; _] -> () | _ -> ()

let lemma_equivalent_sound (i:interpretation value) (rho:env value) (s t:expr)
  : Lemma (requires (exists (nu:value -> real). E.numeric_model i nu) /\
                    boolean_model i /\ not_sound i /\ eq_sound i /\ or_sound i /\ false_sound i /\
                    equivalent s t)
          (ensures eval i s rho == eval i t rho) =
  if rounded_equivalent s t then lemma_rounded_equivalent_sound i rho s t
  else
    let e = if t = false_expr then s else t in
    let aux (nu:value -> real)
      : Lemma (requires E.numeric_model i nu) (ensures eval i s rho == eval i t rho) =
      lemma_indivisible_equation e i nu rho;
      lemma_equation_sort e;
      (match eval i e rho with VBool _ -> () | _ -> ())
    in
    FStar.Classical.exists_elim (eval i s rho == eval i t rho)
      #(value -> real) #(fun nu -> E.numeric_model i nu) () (fun nu -> aux nu)
