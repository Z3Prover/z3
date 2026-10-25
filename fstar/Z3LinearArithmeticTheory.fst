module Z3LinearArithmeticTheory

open FStar.Real
open FStar.List.Tot
module L = FStar.List.Tot

let rec gcd (a b:nat) : Tot nat (decreases b) =
  if b = 0 then a else gcd b (a % b)

type polynomial (a:eqtype) = {
  mono: list (int & a);
  cst: int;
  denom: pos;
}

let zero (#a:eqtype) : polynomial a = { mono = []; cst = 0; denom = 1 }

let constant (#a:eqtype) (n:int) (d:pos) : polynomial a =
  { mono = []; cst = n; denom = d }

let variable (#a:eqtype) (v:a) : polynomial a =
  { mono = [(1, v)]; cst = 0; denom = 1 }

let scale (#a:eqtype) (n:int) (d:pos) (p:polynomial a) : polynomial a =
  { mono = L.map (fun (c, v) -> (n * c, v)) p.mono;
    cst = n * p.cst; denom = d * p.denom }

let add (#a:eqtype) (p q:polynomial a) : polynomial a =
  { mono = L.map (fun (c, v) -> (q.denom * c, v)) p.mono @
           L.map (fun (c, v) -> (p.denom * c, v)) q.mono;
    cst = q.denom * p.cst + p.denom * q.cst;
    denom = p.denom * q.denom }

let rec insert (#a:eqtype) (c:int) (v:a) (ms:list (int & a))
  : Tot (list (int & a)) (decreases ms) =
  match ms with
  | [] -> [(c, v)]
  | (k, w) :: rest ->
    if v = w then (c + k, w) :: rest else (k, w) :: insert c v rest

let rec collect (#a:eqtype) (ms acc:list (int & a))
  : Tot (list (int & a)) (decreases ms) =
  match ms with
  | [] -> acc
  | (c, v) :: rest -> collect rest (insert c v acc)

let rec all_zero (#a:eqtype) (ms:list (int & a)) : Tot bool (decreases ms) =
  match ms with [] -> true | (c, _) :: rest -> c = 0 && all_zero rest

let multiply (#a:eqtype) (p q:polynomial a) : option (polynomial a) =
  if all_zero p.mono then Some (scale p.cst p.denom q)
  else if all_zero q.mono then Some (scale q.cst q.denom p)
  else None

let rec sum (#a:eqtype) (ps:list (polynomial a)) : Tot (polynomial a) (decreases ps) =
  match ps with [] -> zero | p :: rest -> add p (sum rest)

let rec product (#a:eqtype) (ps:list (polynomial a))
  : Tot (option (polynomial a)) (decreases ps) =
  match ps with
  | [] -> Some (constant 1 1)
  | p :: rest ->
    (match product rest with Some q -> multiply p q | None -> None)

let rec monomial_value (#a:eqtype) (ms:list (int & a)) (rho:a -> real)
  : Tot real (decreases ms) =
  match ms with
  | [] -> 0.0R
  | (c, v) :: rest -> of_int c *. rho v +. monomial_value rest rho

let value (#a:eqtype) (p:polynomial a) (rho:a -> real) : real =
  of_int p.cst +. monomial_value p.mono rho

let rec lemma_append (#a:eqtype) (xs ys:list (int & a)) (rho:a -> real)
  : Lemma (monomial_value (xs @ ys) rho == monomial_value xs rho +. monomial_value ys rho)
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_append rest ys rho

#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0 --smtencoding.nl_arith_repr native"

let lemma_of_int_product (n m:int)
  : Lemma (of_int (n * m) == of_int n *. of_int m) = ()

let lemma_of_int_sum (n m:int)
  : Lemma (of_int (n + m) == of_int n +. of_int m) = ()

let lemma_scale_step (n c x tail:real)
  : Lemma ((n *. c) *. x +. n *. tail == n *. (c *. x +. tail)) = ()

let lemma_add_step (a b c d x y:real)
  : Lemma ((a *. c +. b *. d) +. (a *. x +. b *. y) ==
           a *. (c +. x) +. b *. (d +. y)) =
  // Separate nonlinear distributivity from the final linear regrouping.
  assert (a *. (c +. x) == a *. c +. a *. x);
  assert (b *. (d +. y) == b *. d +. b *. y)

#pop-options

let rec lemma_scale_monomials (#a:eqtype) (n:int) (ms:list (int & a)) (rho:a -> real)
  : Lemma (monomial_value (L.map (fun (c, v) -> (n * c, v)) ms) rho ==
           of_int n *. monomial_value ms rho)
          (decreases ms) =
  match ms with
  | [] -> ()
  | (c, v) :: rest ->
    lemma_scale_monomials n rest rho;
    lemma_of_int_product n c;
    assert (monomial_value (L.map (fun (k, w) -> (n * k, w)) ms) rho ==
            of_int (n * c) *. rho v +.
            monomial_value (L.map (fun (k, w) -> (n * k, w)) rest) rho);
    lemma_scale_step (of_int n) (of_int c) (rho v) (monomial_value rest rho)

let lemma_add (#a:eqtype) (p q:polynomial a) (rho:a -> real)
  : Lemma (value (add p q) rho ==
           of_int q.denom *. value p rho +. of_int p.denom *. value q rho) =
  lemma_append (L.map (fun (c, v) -> (q.denom * c, v)) p.mono)
               (L.map (fun (c, v) -> (p.denom * c, v)) q.mono) rho;
  lemma_scale_monomials q.denom p.mono rho;
  lemma_scale_monomials p.denom q.mono rho;
  lemma_of_int_product q.denom p.cst;
  lemma_of_int_product p.denom q.cst;
  lemma_of_int_sum (q.denom * p.cst) (p.denom * q.cst);
  lemma_add_step (of_int q.denom) (of_int p.denom) (of_int p.cst) (of_int q.cst)
    (monomial_value p.mono rho) (monomial_value q.mono rho)

let lemma_scale (#a:eqtype) (n:int) (d:pos) (p:polynomial a) (rho:a -> real)
  : Lemma (value (scale n d p) rho == of_int n *. value p rho) =
  lemma_scale_monomials n p.mono rho;
  lemma_of_int_product n p.cst

let rec lemma_insert (#a:eqtype) (c:int) (v:a) (ms:list (int & a)) (rho:a -> real)
  : Lemma (monomial_value (insert c v ms) rho ==
           of_int c *. rho v +. monomial_value ms rho)
          (decreases ms) =
  match ms with
  | [] -> ()
  | (_, w) :: rest -> if v = w then () else lemma_insert c v rest rho

let rec lemma_collect (#a:eqtype) (ms acc:list (int & a)) (rho:a -> real)
  : Lemma (monomial_value (collect ms acc) rho ==
           monomial_value ms rho +. monomial_value acc rho)
          (decreases ms) =
  match ms with
  | [] -> ()
  | (c, v) :: rest ->
    lemma_insert c v acc rho;
    lemma_collect rest (insert c v acc) rho

let rec lemma_all_zero (#a:eqtype) (ms:list (int & a)) (rho:a -> real)
  : Lemma (requires all_zero ms) (ensures monomial_value ms rho == 0.0R)
          (decreases ms) =
  match ms with [] -> () | _ :: rest -> lemma_all_zero rest rho

let lemma_multiply_denominator (#a:eqtype) (p q r:polynomial a)
  : Lemma (requires multiply p q == Some r)
          (ensures r.denom == p.denom * q.denom) =
  if all_zero p.mono then () else ()

let lemma_multiply (#a:eqtype) (p q r:polynomial a) (rho:a -> real)
  : Lemma (requires multiply p q == Some r)
          (ensures value r rho == value p rho *. value q rho) =
  if all_zero p.mono then (
    lemma_all_zero p.mono rho;
    lemma_scale p.cst p.denom q rho)
  else (
    lemma_all_zero q.mono rho;
    lemma_scale q.cst q.denom p rho)

type contribution (a:eqtype) = {
  poly: polynomial a;
  strict: bool;
}

let holds (#a:eqtype) (p:contribution a) (rho:a -> real) : prop =
  if p.strict then value p.poly rho <. 0.0R else value p.poly rho <=. 0.0R

let rec all_hold (#a:eqtype) (ps:list (contribution a)) (rho:a -> real)
  : Tot prop (decreases ps) =
  match ps with [] -> True | p :: rest -> holds p rho /\ all_hold rest rho

let rec combined (#a:eqtype) (ps:list (contribution a))
  : Tot (polynomial a & bool) (decreases ps) =
  match ps with
  | [] -> (zero, false)
  | p :: rest ->
    let q, strict = combined rest in
    (add p.poly q, p.strict || strict)

let accepts (#a:eqtype) (ps:list (contribution a)) : bool =
  let p, strict = combined ps in
  all_zero (collect p.mono []) && (if strict then p.cst >= 0 else p.cst > 0)

let rec lemma_combined (#a:eqtype) (ps:list (contribution a)) (rho:a -> real)
  : Lemma (requires all_hold ps rho)
          (ensures holds { poly = fst (combined ps); strict = snd (combined ps) } rho)
          (decreases ps) =
  match ps with
  | [] -> ()
  | p :: rest ->
    lemma_combined rest rho;
    lemma_add p.poly (fst (combined rest)) rho

let lemma_accepts_sound (#a:eqtype) (ps:list (contribution a)) (rho:a -> real)
  : Lemma (requires accepts ps /\ all_hold ps rho) (ensures False) =
  lemma_combined ps rho;
  let p, _ = combined ps in
  lemma_collect p.mono [] rho;
  lemma_all_zero (collect p.mono []) rho
