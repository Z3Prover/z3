(*
   Z3FiniteFieldLemma.fst

   Checks finite-field (`FF<p>`) rewrites of the native proof checker by
   normalizing both sides to sparse polynomials over Z/pZ whose variables
   are the maximal non-field subterms ("atoms"). Only the commutative-ring
   laws are used, so nothing here assumes that `p` is prime: if `p` is
   composite the same identities still hold in Z/pZ. Rewrites that need the
   field equation `x^p = x` or inverses are not decided; they stay unmet.
   Theory lemmas (`th-lemma` clauses) are decided by evaluating the clause
   under every assignment of residues to its leaves, at most
   `max_assignments` of them (see the last section); this also uses only
   arithmetic modulo p.

   Trust statement. `ff_model i project` is the semantic contract of the
   interpretation `i` for finite-field sorts, in the same position and with
   the same status as `Z3BvLemma.bv_model`:
     * closed terms of sort `FF<p>` are identified with their residues
       `project p v` in [0, p), and equal values have equal residues;
     * a numeral `ff` with parameters `[p; n]` denotes `n`;
     * `ff.add`/`ff.mul`/`ff.neg`/`ff.bitsum` over `FF<p>` denote the
       corresponding operation modulo `p`.
   It is a hypothesis on `i` (not an axiom or an `assume`); it is satisfied
   by the standard model where `FF<p>` values are residues modulo `p`.
*)
module Z3FiniteFieldLemma

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module D = Z3Definitions
module L = FStar.List.Tot
module M = FStar.Math.Lemmas
module C = Z3CanonicalOps

let op_ff_num : decl_kind = 300
let op_ff_add : decl_kind = 301
let op_ff_mul : decl_kind = 302
let op_ff_neg : decl_kind = 303
let op_ff_bitsum : decl_kind = 304

(* The native bridge names the sort of a finite field by its decimal modulus. *)
let ff_sort (p:int) : sort = BaseSort ("FF" ^ Prims.string_of_int p)

(* `ff` numeral with parameters [p; n]: a canonical residue 0 <= n < p. *)
let numeral (e:expr) : option (int & int) =
  match e with
  | App f [] ->
    (match f.int_params with
     | [p; n] ->
       if p >= 2 && f.interp = Some op_ff_num && f.domain = [] && f.range = ff_sort p &&
          0 <= n && n < p
       then Some (p, n) else None
     | _ -> None)
  | _ -> None

let ff_domain (p:int) (args:list expr) : list sort = L.map (fun _ -> ff_sort p) args

(* Field operations: the declaration carries the modulus and every argument
   has the matching `FF<p>` sort. *)
let operation (f:func_decl) (args:list expr) : option (int & decl_kind) =
  match f.int_params, f.interp with
  | [p], Some op ->
    if p >= 2 && f.range = ff_sort p && f.domain = ff_domain p args &&
       sorts_match args (ff_domain p args) &&
       ((op = op_ff_neg && L.length args = 1) ||
        ((op = op_ff_add || op = op_ff_mul || op = op_ff_bitsum) && L.length args >= 2))
    then Some (p, op) else None
  | _, _ -> None

let rec sum_mod (p:pos) (xs:list int) : Tot int (decreases xs) =
  match xs with
  | [] -> 0
  | x :: rest -> (x + sum_mod p rest) % p

let rec prod_mod (p:pos) (xs:list int) : Tot int (decreases xs) =
  match xs with
  | [] -> 1 % p
  | x :: rest -> (x * prod_mod p rest) % p

(* bitsum(a0, ..., an) = sum 2^i * ai; `w` is the weight 2^i of the head. *)
let rec bitsum_mod (p:pos) (w:int) (xs:list int) : Tot int (decreases xs) =
  match xs with
  | [] -> 0
  | x :: rest -> (x * w + bitsum_mod p (2 * w) rest) % p

let calculate (p:pos) (op:decl_kind) (xs:list int) : int =
  if op = op_ff_add then sum_mod p xs
  else if op = op_ff_mul then prod_mod p xs
  else if op = op_ff_bitsum then bitsum_mod p 1 xs
  else (match xs with [x] -> (0 - x) % p | _ -> 0)

let projections (i:interpretation value) (rho:env value) (project:int -> value -> int)
                (p:int) (args:list expr) : list int =
  L.map (fun a -> project p (eval i a rho)) args

(* Closed terms avoid imposing finite-field typing on arbitrary binder environments. *)
let ff_model (i:interpretation value) (project:int -> value -> int) : prop =
  (forall (p:int) (a b:expr) (rho:env value).
    p >= 2 /\ D.scoped [] a /\ D.scoped [] b /\ get_sort a == ff_sort p /\ get_sort b == ff_sort p ==>
    ((eval i a rho == eval i b rho <==> project p (eval i a rho) == project p (eval i b rho)) /\
     0 <= project p (eval i a rho) /\ project p (eval i a rho) < p)) /\
  (forall (e:expr) (rho:env value) (p n:int).
    numeral e == Some (p, n) ==> project p (eval i e rho) == n) /\
  (forall (f:func_decl) (args:list expr) (rho:env value) (p:pos) (op:decl_kind).
    D.scoped [] (App f args) /\ operation f args == Some (p, op) ==>
    project p (eval i (App f args) rho) == calculate p op (projections i rho project p args))

(* ----------------------------------------------------------------- *)
(* Sparse polynomials over Z (reduced modulo p only when compared)     *)
(* ----------------------------------------------------------------- *)

(* A monomial is a sorted multiset of variable indices. Only evaluation is
   trusted: `mval`/`peval` give the meaning, and the laws below prove that
   the arithmetic respects it. Sortedness merely makes equal polynomials
   compare equal and is never needed for soundness. *)
type mono = list nat
type poly = list (mono & int)

let rec mval (v:nat -> int) (m:mono) : Tot int (decreases m) =
  match m with
  | [] -> 1
  | k :: rest -> v k * mval v rest

let rec peval (v:nat -> int) (q:poly) : Tot int (decreases q) =
  match q with
  | [] -> 0
  | (m, c) :: rest -> c * mval v m + peval v rest

let rec mono_mul (a b:mono) : Tot mono (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> b
  | _, [] -> a
  | x :: a', y :: b' -> if x <= y then x :: mono_mul a' b else y :: mono_mul a b'

let rec mono_lt (a b:mono) : Tot bool (decreases a) =
  match a, b with
  | [], [] -> false
  | [], _ -> true
  | _, [] -> false
  | x :: a', y :: b' -> if x < y then true else if x > y then false else mono_lt a' b'

let rec padd (a b:poly) : Tot poly (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> b
  | _, [] -> a
  | (m1, c1) :: a', (m2, c2) :: b' ->
    if m1 = m2 then (m1, c1 + c2) :: padd a' b'
    else if mono_lt m1 m2 then (m1, c1) :: padd a' b
    else (m2, c2) :: padd a b'

let rec pscale (k:int) (q:poly) : Tot poly (decreases q) =
  match q with
  | [] -> []
  | (m, c) :: rest -> (m, k * c) :: pscale k rest

let rec pmul_term (m:mono) (c:int) (b:poly) : Tot poly (decreases b) =
  match b with
  | [] -> []
  | (m2, c2) :: rest -> padd [(mono_mul m m2, c * c2)] (pmul_term m c rest)

let rec pmul (a b:poly) : Tot poly (decreases a) =
  match a with
  | [] -> []
  | (m, c) :: rest -> padd (pmul_term m c b) (pmul rest b)

(* Ring identities are stated explicitly so that no query needs nonlinear reasoning. *)
let lemma_mul_swap3 (a x b:int) : Lemma (a * (x * b) == x * (a * b)) =
  M.paren_mul_right a x b;
  M.swap_mul a x;
  M.paren_mul_right x a b

let lemma_mul4 (a b c d:int) : Lemma ((a * b) * (c * d) == (a * c) * (b * d)) =
  M.paren_mul_right a b (c * d);
  lemma_mul_swap3 b c d;
  M.paren_mul_right a c (b * d)

let rec lemma_mval_mul (v:nat -> int) (a b:mono)
  : Lemma (ensures mval v (mono_mul a b) == mval v a * mval v b)
          (decreases (L.length a + L.length b))
  = match a, b with
    | [], _ -> ()
    | _, [] -> ()
    | x :: a', y :: b' ->
      if x <= y then (
        lemma_mval_mul v a' b;
        M.paren_mul_right (v x) (mval v a') (mval v b))
      else (
        lemma_mval_mul v a b';
        lemma_mul_swap3 (mval v a) (v y) (mval v b'))

let rec lemma_padd (v:nat -> int) (a b:poly)
  : Lemma (ensures peval v (padd a b) == peval v a + peval v b)
          (decreases (L.length a + L.length b))
  = match a, b with
    | [], _ -> ()
    | _, [] -> ()
    | (m1, c1) :: a', (m2, c2) :: b' ->
      if m1 = m2 then (
        lemma_padd v a' b';
        M.distributivity_add_left c1 c2 (mval v m1))
      else if mono_lt m1 m2 then lemma_padd v a' b
      else lemma_padd v a b'

let rec lemma_pscale (v:nat -> int) (k:int) (q:poly)
  : Lemma (ensures peval v (pscale k q) == k * peval v q) (decreases q)
  = match q with
    | [] -> ()
    | (m, c) :: rest ->
      lemma_pscale v k rest;
      M.paren_mul_right k c (mval v m);
      M.distributivity_add_right k (c * mval v m) (peval v rest)

#push-options "--fuel 2"
let rec lemma_pmul_term (v:nat -> int) (m:mono) (c:int) (b:poly)
  : Lemma (ensures peval v (pmul_term m c b) == (c * mval v m) * peval v b) (decreases b)
  = match b with
    | [] -> ()
    | (m2, c2) :: rest ->
      lemma_pmul_term v m c rest;
      lemma_mval_mul v m m2;
      lemma_padd v [(mono_mul m m2, c * c2)] (pmul_term m c rest);
      lemma_mul4 c c2 (mval v m) (mval v m2);
      M.distributivity_add_right (c * mval v m) (c2 * mval v m2) (peval v rest)
#pop-options

let rec lemma_pmul (v:nat -> int) (a b:poly)
  : Lemma (ensures peval v (pmul a b) == peval v a * peval v b) (decreases a)
  = match a with
    | [] -> ()
    | (m, c) :: rest ->
      lemma_pmul v rest b;
      lemma_pmul_term v m c b;
      lemma_padd v (pmul_term m c b) (pmul rest b);
      M.distributivity_add_left (c * mval v m) (peval v rest) (peval v b)

(* ----------------------------------------------------------------- *)
(* Terms to polynomials                                                *)
(* ----------------------------------------------------------------- *)

(* Atoms are the maximal subterms that are not field operations or numerals.
   They are indexed by position in an atom table. The table is built by the
   untrusted `collect` pass: a missing atom just makes `to_poly` fail. *)
let rec index_of (e:expr) (tbl:list expr) : Tot (option nat) (decreases tbl) =
  match tbl with
  | [] -> None
  | x :: rest ->
    if x = e then Some 0
    else (match index_of e rest with Some k -> Some (k + 1) | None -> None)

let rec lemma_index_of (e:expr) (tbl:list expr) (k:nat)
  : Lemma (requires index_of e tbl == Some k)
          (ensures k < L.length tbl /\ L.index tbl k == e)
          (decreases tbl)
  = match tbl with
    | x :: rest ->
      if x = e then ()
      else (match index_of e rest with
            | Some j -> lemma_index_of e rest j
            | None -> ())

let valuation (i:interpretation value) (rho:env value) (project:int -> value -> int)
              (p:int) (tbl:list expr) : nat -> int =
  fun k -> if k < L.length tbl then project p (eval i (L.index tbl k) rho) else 0

let atom_poly (tbl:list expr) (e:expr) : option poly =
  match index_of e tbl with
  | Some k -> Some [([k], 1)]
  | None -> None

let rec psum (qs:list poly) : Tot poly (decreases qs) =
  match qs with
  | [] -> []
  | q :: rest -> padd q (psum rest)

(* Bounded so that a product of long sums cannot be expanded without limit. *)
let max_product_terms : nat = 256

let rec pprod (qs:list poly) : Tot (option poly) (decreases qs) =
  match qs with
  | [] -> Some [([], 1)]
  | q :: rest ->
    (match pprod rest with
     | None -> None
     | Some r -> if L.length q * L.length r > max_product_terms then None else Some (pmul q r))

let rec pbitsum (w:int) (qs:list poly) : Tot poly (decreases qs) =
  match qs with
  | [] -> []
  | q :: rest -> padd (pscale w q) (pbitsum (2 * w) rest)

let combine (op:decl_kind) (qs:list poly) : option poly =
  if op = op_ff_add then Some (psum qs)
  else if op = op_ff_mul then pprod qs
  else if op = op_ff_bitsum then Some (pbitsum 1 qs)
  else (match qs with [q] -> Some (pscale (-1) q) | _ -> None)

let rec to_poly (p:int) (tbl:list expr) (e:expr) : Tot (option poly) (decreases e) =
  match numeral e with
  | Some (q, n) -> if q = p then Some [([], n)] else None
  | None ->
    (match e with
     | App f args ->
       (match operation f args with
        | Some (q, op) ->
          if q <> p then None
          else (match to_polys p tbl args with
                | Some qs -> combine op qs
                | None -> None)
        | None -> if get_sort e = ff_sort p then atom_poly tbl e else None)
     | _ -> if get_sort e = ff_sort p then atom_poly tbl e else None)

and to_polys (p:int) (tbl:list expr) (args:list expr) : Tot (option (list poly)) (decreases args) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match to_poly p tbl a, to_polys p tbl rest with
     | Some q, Some qs -> Some (q :: qs)
     | _, _ -> None)

(* ----------------------------------------------------------------- *)
(* Modular congruence helpers                                          *)
(* ----------------------------------------------------------------- *)

let lemma_add_cong (p:pos) (a b a' b':int)
  : Lemma (requires a % p == a' % p /\ b % p == b' % p)
          (ensures (a + b) % p == (a' + b') % p)
  = M.lemma_mod_plus_distr_l a b p;
    M.lemma_mod_plus_distr_r (a % p) b p;
    M.lemma_mod_plus_distr_l a' b' p;
    M.lemma_mod_plus_distr_r (a' % p) b' p

let lemma_mul_cong (p:pos) (a b a' b':int)
  : Lemma (requires a % p == a' % p /\ b % p == b' % p)
          (ensures (a * b) % p == (a' * b') % p)
  = M.lemma_mod_mul_distr_l a b p;
    M.lemma_mod_mul_distr_r (a % p) b p;
    M.lemma_mod_mul_distr_l a' b' p;
    M.lemma_mod_mul_distr_r (a' % p) b' p

let rec match_list (v:nat -> int) (p:pos) (qs:list poly) (xs:list int)
  : Tot prop (decreases qs) =
  match qs, xs with
  | [], [] -> True
  | q :: qs', x :: xs' -> peval v q % p == x /\ match_list v p qs' xs'
  | _, _ -> False

let rec lemma_psum (v:nat -> int) (p:pos) (qs:list poly) (xs:list int)
  : Lemma (requires match_list v p qs xs)
          (ensures peval v (psum qs) % p == sum_mod p xs)
          (decreases qs)
  = match qs, xs with
    | q :: qs', x :: xs' ->
      lemma_psum v p qs' xs';
      lemma_padd v q (psum qs');
      lemma_add_cong p (peval v q) (peval v (psum qs')) x (sum_mod p xs')
    | _, _ -> ()

#push-options "--fuel 2"
let rec lemma_pprod (v:nat -> int) (p:pos) (qs:list poly) (xs:list int) (r:poly)
  : Lemma (requires match_list v p qs xs /\ pprod qs == Some r)
          (ensures peval v r % p == prod_mod p xs)
          (decreases qs)
  = match qs, xs with
    | q :: qs', x :: xs' ->
      let r' = Some?.v (pprod qs') in
      lemma_pprod v p qs' xs' r';
      lemma_pmul v q r';
      lemma_mul_cong p (peval v q) (peval v r') x (prod_mod p xs')
    | _, _ -> ()
#pop-options

let rec lemma_pbitsum (v:nat -> int) (p:pos) (w:int) (qs:list poly) (xs:list int)
  : Lemma (requires match_list v p qs xs)
          (ensures peval v (pbitsum w qs) % p == bitsum_mod p w xs)
          (decreases qs)
  = match qs, xs with
    | q :: qs', x :: xs' ->
      lemma_pbitsum v p (2 * w) qs' xs';
      lemma_pscale v w q;
      lemma_padd v (pscale w q) (pbitsum (2 * w) qs');
      lemma_mul_cong p w (peval v q) w x;
      lemma_add_cong p (w * peval v q) (peval v (pbitsum (2 * w) qs'))
                       (x * w) (bitsum_mod p (2 * w) xs')
    | _, _ -> ()

#push-options "--fuel 2"
let lemma_combine (v:nat -> int) (p:pos) (op:decl_kind) (qs:list poly) (xs:list int) (r:poly)
  : Lemma (requires match_list v p qs xs /\ combine op qs == Some r /\
                    (op = op_ff_neg ==> L.length xs = 1))
          (ensures peval v r % p == calculate p op xs)
  = if op = op_ff_add then lemma_psum v p qs xs
    else if op = op_ff_mul then lemma_pprod v p qs xs r
    else if op = op_ff_bitsum then lemma_pbitsum v p 1 qs xs
    else (match qs with
          | [q] ->
            (match xs with
             | [x] ->
               lemma_pscale v (-1) q;
               M.lemma_mod_sub_distr 0 (peval v q) p
             | _ -> ())
          | _ -> ())
#pop-options

(* ----------------------------------------------------------------- *)
(* Soundness of the translation                                        *)
(* ----------------------------------------------------------------- *)

let lemma_sort_eq_base (x:sort) (n:string)
  : Lemma (requires sort_eq x (BaseSort n)) (ensures x == BaseSort n)
  = match x with
    | BaseSort m -> ()
    | ArraySort _ _ -> ()

let rec lemma_args_sort (args:list expr) (p:int)
  : Lemma (requires sorts_match args (ff_domain p args))
          (ensures L.for_all (fun a -> get_sort a = ff_sort p) args)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_sort_eq_base (get_sort a) ("FF" ^ Prims.string_of_int p);
      lemma_args_sort rest p

let rec lemma_map_length (#a #b:Type) (f:a -> Tot b) (xs:list a)
  : Lemma (ensures L.length (L.map f xs) == L.length xs) (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: rest -> lemma_map_length f rest

let lemma_range (i:interpretation value) (rho:env value) (project:int -> value -> int)
                (p:int) (e:expr)
  : Lemma (requires ff_model i project /\ p >= 2 /\ D.scoped [] e /\ get_sort e == ff_sort p)
          (ensures 0 <= project p (eval i e rho) /\ project p (eval i e rho) < p)
  = assert (0 <= project p (eval i e rho) /\ project p (eval i e rho) < p)

#push-options "--fuel 2"
let lemma_atom_poly (i:interpretation value) (rho:env value) (project:int -> value -> int)
                    (p:int) (tbl:list expr) (e:expr) (q:poly)
  : Lemma (requires ff_model i project /\ p >= 2 /\ D.scoped [] e /\ get_sort e == ff_sort p /\
                    atom_poly tbl e == Some q)
          (ensures peval (valuation i rho project p tbl) q % p == project p (eval i e rho))
  = let k = Some?.v (index_of e tbl) in
    lemma_index_of e tbl k;
    lemma_range i rho project p e;
    let v = valuation i rho project p tbl in
    assert (v k == project p (eval i e rho));
    assert (peval v [([k], 1)] == v k);
    M.small_mod (project p (eval i e rho)) p
#pop-options

let lemma_operation_shape (f:func_decl) (args:list expr) (p:int) (op:decl_kind)
  : Lemma (requires operation f args == Some (p, op))
          (ensures p >= 2 /\ f.range == ff_sort p /\
                   sorts_match args (ff_domain p args) /\
                   (op = op_ff_neg ==> L.length args = 1))
  = ()

#push-options "--fuel 2"
let rec lemma_to_poly (i:interpretation value) (rho:env value) (project:int -> value -> int)
                      (p:int) (tbl:list expr) (e:expr) (q:poly)
  : Lemma (requires ff_model i project /\ p >= 2 /\ D.scoped [] e /\ get_sort e == ff_sort p /\
                    to_poly p tbl e == Some q)
          (ensures peval (valuation i rho project p tbl) q % p == project p (eval i e rho))
          (decreases e)
  = match numeral e with
    | Some (q', n) ->
      assert (project p (eval i e rho) == n);
      assert (peval (valuation i rho project p tbl) [([], n)] == n);
      M.small_mod n p
    | None ->
      (match e with
       | App f args ->
         (match operation f args with
          | Some (q', op) ->
            (match to_polys p tbl args with
             | Some qs ->
               lemma_operation_shape f args p op;
               lemma_args_sort args p;
               lemma_to_polys i rho project p tbl args qs;
               lemma_map_length (fun a -> project p (eval i a rho)) args;
               assert (project p (eval i e rho) == calculate p op (projections i rho project p args));
               lemma_combine (valuation i rho project p tbl) p op qs
                 (projections i rho project p args) q
             | None -> ())
          | None -> lemma_atom_poly i rho project p tbl e q)
       | _ -> lemma_atom_poly i rho project p tbl e q)

and lemma_to_polys (i:interpretation value) (rho:env value) (project:int -> value -> int)
                   (p:int) (tbl:list expr) (args:list expr) (qs:list poly)
  : Lemma (requires ff_model i project /\ p >= 2 /\ D.scoped_args [] args /\
                    L.for_all (fun a -> get_sort a = ff_sort p) args /\
                    to_polys p tbl args == Some qs)
          (ensures match_list (valuation i rho project p tbl) p qs
                              (projections i rho project p args))
          (decreases args)
  = match args, qs with
    | a :: rest, q :: qs' ->
      lemma_to_poly i rho project p tbl a q;
      lemma_to_polys i rho project p tbl rest qs'
    | _, _ -> ()
#pop-options

(* ----------------------------------------------------------------- *)
(* Deciding equalities                                                 *)
(* ----------------------------------------------------------------- *)

let rec zero_mod (p:pos) (q:poly) : Tot bool (decreases q) =
  match q with
  | [] -> true
  | (_, c) :: rest -> c % p = 0 && zero_mod p rest

let rec lemma_zero_mod (v:nat -> int) (p:pos) (q:poly)
  : Lemma (requires zero_mod p q) (ensures peval v q % p == 0) (decreases q)
  = match q with
    | [] -> ()
    | (m, c) :: rest ->
      lemma_zero_mod v p rest;
      M.lemma_mod_mul_distr_l c (mval v m) p;
      lemma_add_cong p (c * mval v m) (peval v rest) 0 0

let lemma_diff_mod (p:pos) (x y:int)
  : Lemma (requires (x - y) % p == 0) (ensures x % p == y % p)
  = M.euclidean_division_definition (x - y) p;
    M.lemma_mod_plus y ((x - y) / p) p

let lemma_same_mod_diff (p:pos) (x y:int)
  : Lemma (requires x % p == y % p) (ensures (x - y) % p == 0)
  = M.euclidean_division_definition x p;
    M.euclidean_division_definition y p;
    M.distributivity_sub_left (x / p) (y / p) p;
    M.cancel_mul_mod (x / p - y / p) p

(* Untrusted search for the atoms of a term; a missing atom only makes `to_poly` fail. *)
let rec collect (p:int) (tbl:list expr) (e:expr) : Tot (list expr) (decreases e) =
  match numeral e with
  | Some _ -> tbl
  | None ->
    (match e with
     | App f args ->
       (match operation f args with
        | Some (q, _) -> if q <> p then tbl else collect_args p tbl args
        | None -> if L.mem e tbl then tbl else L.append tbl [e])
     | _ -> if L.mem e tbl then tbl else L.append tbl [e])

and collect_args (p:int) (tbl:list expr) (args:list expr) : Tot (list expr) (decreases args) =
  match args with
  | [] -> tbl
  | a :: rest -> collect_args p (collect p tbl a) rest

let modulus_of (e:expr) : option int =
  match numeral e with
  | Some (p, _) -> Some p
  | None ->
    (match e with
     | App f args -> (match operation f args with Some (p, _) -> Some p | None -> None)
     | _ -> None)

let shared_modulus (a b:expr) : option int =
  match modulus_of a with
  | Some p -> Some p
  | None -> modulus_of b

let closed_ff (p:int) (e:expr) : bool = D.scoped [] e && get_sort e = ff_sort p

let difference (p:int) (tbl:list expr) (a b:expr) : option poly =
  match to_poly p tbl a, to_poly p tbl b with
  | Some qa, Some qb -> Some (padd qa (pscale (-1) qb))
  | _, _ -> None

(* Two closed `FF<p>` terms are equal when their difference polynomial is 0 mod p. *)
let term_equivalent (a b:expr) : bool =
  match shared_modulus a b with
  | None -> false
  | Some p ->
    if p >= 2 && closed_ff p a && closed_ff p b
    then (match difference p (collect p (collect p [] a) b) a b with
          | Some d -> zero_mod p d
          | None -> false)
    else false

let lemma_difference (i:interpretation value) (rho:env value) (project:int -> value -> int)
                     (p:int) (tbl:list expr) (a b:expr) (d:poly)
  : Lemma (requires ff_model i project /\ p >= 2 /\ closed_ff p a /\ closed_ff p b /\
                    difference p tbl a b == Some d)
          (ensures peval (valuation i rho project p tbl) d % p ==
                   (project p (eval i a rho) - project p (eval i b rho)) % p)
  = let qa = Some?.v (to_poly p tbl a) in
    let qb = Some?.v (to_poly p tbl b) in
    let v = valuation i rho project p tbl in
    lemma_to_poly i rho project p tbl a qa;
    lemma_to_poly i rho project p tbl b qb;
    lemma_pscale v (-1) qb;
    lemma_padd v qa (pscale (-1) qb);
    M.lemma_mod_sub_distr 0 (peval v qb) p;
    lemma_add_cong p (peval v qa) (peval v (pscale (-1) qb))
                     (project p (eval i a rho)) (0 - project p (eval i b rho))

let lemma_term_equivalent (i:interpretation value) (rho:env value) (project:int -> value -> int)
                          (a b:expr)
  : Lemma (requires ff_model i project /\ term_equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = let p = Some?.v (shared_modulus a b) in
    let tbl = collect p (collect p [] a) b in
    let d = Some?.v (difference p tbl a b) in
    let v = valuation i rho project p tbl in
    lemma_zero_mod v p d;
    lemma_difference i rho project p tbl a b d;
    lemma_diff_mod p (project p (eval i a rho)) (project p (eval i b rho))

(* ----------------------------------------------------------------- *)
(* Deciding equality atoms                                             *)
(* ----------------------------------------------------------------- *)

let eq_parts (e:expr) : option (expr & expr) =
  match e with
  | App f [s; t] ->
    if f = eq_decl (get_sort s) && get_sort s = get_sort t then Some (s, t) else None
  | _ -> None

let atom_modulus (e:expr) : option int =
  match eq_parts e with
  | Some (s, t) -> shared_modulus s t
  | None -> None

let eq_collect (p:int) (tbl:list expr) (e:expr) : list expr =
  match eq_parts e with
  | Some (s, t) -> collect p (collect p tbl s) t
  | None -> tbl

(* The polynomial s - t of the finite-field equality `(= s t)`. *)
let eq_diff (p:int) (tbl:list expr) (e:expr) : option poly =
  match eq_parts e with
  | Some (s, t) -> if closed_ff p s && closed_ff p t then difference p tbl s t else None
  | None -> None

(* Dropping terms whose coefficient vanishes modulo p does not change the value modulo p. *)
let rec prune (p:pos) (q:poly) : Tot poly (decreases q) =
  match q with
  | [] -> []
  | (m, c) :: rest -> if c % p = 0 then prune p rest else (m, c) :: prune p rest

let rec lemma_prune (v:nat -> int) (p:pos) (q:poly)
  : Lemma (ensures peval v (prune p q) % p == peval v q % p) (decreases q)
  = match q with
    | [] -> ()
    | (m, c) :: rest ->
      lemma_prune v p rest;
      M.lemma_mod_mul_distr_l c (mval v m) p;
      if c % p = 0
      then lemma_add_cong p (c * mval v m) (peval v rest) 0 (peval v rest)
      else lemma_add_cong p (c * mval v m) (peval v (prune p rest)) (c * mval v m) (peval v rest)

let nonzero_constant (p:pos) (d:poly) : bool =
  match prune p d with
  | [([], c)] -> c % p <> 0
  | _ -> false

let lemma_residues (p:pos) (x y:int)
  : Lemma (requires 0 <= x /\ x < p /\ 0 <= y /\ y < p)
          (ensures ((x - y) % p == 0) <==> x == y)
  = if (x - y) % p = 0 then (
      lemma_diff_mod p x y;
      M.small_mod x p;
      M.small_mod y p)

let lemma_eq_diff (i:interpretation value) (rho:env value) (project:int -> value -> int)
                  (p:int) (tbl:list expr) (e:expr) (d:poly)
  : Lemma (requires ff_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\ p >= 2 /\
                    eq_diff p tbl e == Some d)
          (ensures get_sort e == bool_sort /\
                   (lit_true i rho e <==> peval (valuation i rho project p tbl) d % p == 0))
  = let (s, t) = Some?.v (eq_parts e) in
    lemma_difference i rho project p tbl s t d;
    lemma_range i rho project p s;
    lemma_range i rho project p t;
    lemma_residues p (project p (eval i s rho)) (project p (eval i t rho));
    match e with
    | App f [_; _] ->
      assert (f.decl_name == "=");
      assert (lit_true i rho e <==> eval i s rho == eval i t rho)
    | _ -> ()

(* `(= s t)` is true for every valuation exactly when s - t is 0 mod p, and
   false for every valuation when s - t is a nonzero constant. *)
let eq_truth_equivalent (a b:expr) : bool =
  match atom_modulus a with
  | None -> false
  | Some p ->
    if p >= 2
    then (match eq_diff p (eq_collect p [] a) a with
          | Some d -> (b = true_expr && zero_mod p d) || (b = false_expr && nonzero_constant p d)
          | None -> false)
    else false

let lemma_bool_iff (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires Z3BooleanRewrite.boolean_rewrite_model i /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\
                    (lit_true i rho a <==> lit_true i rho b))
          (ensures eval i a rho == eval i b rho)
  = match eval i a rho, eval i b rho with
    | VBool _, VBool _ -> ()
    | _, _ -> ()

#push-options "--fuel 2"
let lemma_eq_truth_equivalent (i:interpretation value) (rho:env value) (project:int -> value -> int)
                              (a b:expr)
  : Lemma (requires ff_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    eq_truth_equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = let p = Some?.v (atom_modulus a) in
    let tbl = eq_collect p [] a in
    let d = Some?.v (eq_diff p tbl a) in
    let v = valuation i rho project p tbl in
    lemma_eq_diff i rho project p tbl a d;
    assert (eval i true_expr rho == VBool true);
    assert (eval i false_expr rho == VBool false);
    if b = true_expr then (
      lemma_zero_mod v p d;
      lemma_bool_iff i rho a b)
    else (
      lemma_prune v p d;
      match prune p d with
      | [([], c)] ->
        assert (peval v (prune p d) == c);
        lemma_bool_iff i rho a b
      | _ -> ())
#pop-options

(* ----------------------------------------------------------------- *)
(* Rescaled equalities                                                 *)
(* ----------------------------------------------------------------- *)

(* Untrusted search for a modular inverse; every factor it proposes is
   re-checked by polynomial identities below, so a wrong answer is rejected. *)
let rec egcd (a b:nat) : Tot (int & int & int) (decreases b) =
  if b = 0 then (a, 1, 0)
  else (let (g, x, y) = egcd b (a % b) in (g, y, x - (a / b) * y))

let inverse_mod (p:pos) (c:int) : option int =
  let (g, x, _) = egcd (c % p) p in
  if g = 1 then Some (x % p) else None

let rec coeff_of (m:mono) (q:poly) : Tot int (decreases q) =
  match q with
  | [] -> 0
  | (m', c) :: rest -> if m' = m then c + coeff_of m rest else coeff_of m rest

let rec first_nonzero (p:pos) (q:poly) : Tot (option mono) (decreases q) =
  match q with
  | [] -> None
  | (m, c) :: rest -> if c % p <> 0 then Some m else first_nonzero p rest

(* Candidate factors k, w with d1 = k*d2 and d2 = w*d1. *)
let scale_witness (p:pos) (d1 d2:poly) : option (int & int) =
  match first_nonzero p d2 with
  | None -> None
  | Some m ->
    let c1 = coeff_of m d1 in
    let c2 = coeff_of m d2 in
    (match inverse_mod p c1, inverse_mod p c2 with
     | Some i1, Some i2 -> Some ((c1 * i2) % p, (c2 * i1) % p)
     | _, _ -> None)

(* d1 and d2 vanish together: both are 0 mod p, or each is a multiple of the
   other modulo p (so a unit multiple, which is witnessed rather than assumed). *)
let same_zero_set (p:pos) (d1 d2:poly) : bool =
  (zero_mod p d1 && zero_mod p d2) ||
  (match scale_witness p d1 d2 with
   | Some (k, w) ->
     zero_mod p (padd d1 (pscale (-k) d2)) && zero_mod p (padd d2 (pscale (-w) d1))
   | None -> false)

let lemma_scaled_zero (p:pos) (y x k:int)
  : Lemma (requires (y - k * x) % p == 0)
          (ensures x % p == 0 ==> y % p == 0)
  = lemma_diff_mod p y (k * x);
    M.lemma_mod_mul_distr_r k x p

let lemma_same_zero_set (v:nat -> int) (p:pos) (d1 d2:poly)
  : Lemma (requires same_zero_set p d1 d2)
          (ensures (peval v d1 % p == 0 <==> peval v d2 % p == 0))
  = if zero_mod p d1 && zero_mod p d2 then (
      lemma_zero_mod v p d1;
      lemma_zero_mod v p d2)
    else (
      match scale_witness p d1 d2 with
      | Some (k, w) ->
        lemma_pscale v (-k) d2;
        lemma_padd v d1 (pscale (-k) d2);
        lemma_zero_mod v p (padd d1 (pscale (-k) d2));
        lemma_pscale v (-w) d1;
        lemma_padd v d2 (pscale (-w) d1);
        lemma_zero_mod v p (padd d2 (pscale (-w) d1));
        M.neg_mul_left k (peval v d2);
        M.neg_mul_left w (peval v d1);
        lemma_scaled_zero p (peval v d1) (peval v d2) k;
        lemma_scaled_zero p (peval v d2) (peval v d1) w
      | None -> ())

(* Two finite-field equalities with unit-proportional difference polynomials. *)
let eq_eq_equivalent (a b:expr) : bool =
  match (match atom_modulus a with Some p -> Some p | None -> atom_modulus b) with
  | None -> false
  | Some p ->
    if p >= 2
    then (let tbl = eq_collect p (eq_collect p [] a) b in
          match eq_diff p tbl a, eq_diff p tbl b with
          | Some d1, Some d2 -> same_zero_set p d1 d2
          | _, _ -> false)
    else false

let lemma_eq_eq_equivalent (i:interpretation value) (rho:env value) (project:int -> value -> int)
                           (a b:expr)
  : Lemma (requires ff_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    eq_eq_equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = let p = Some?.v (match atom_modulus a with Some p -> Some p | None -> atom_modulus b) in
    let tbl = eq_collect p (eq_collect p [] a) b in
    let d1 = Some?.v (eq_diff p tbl a) in
    let d2 = Some?.v (eq_diff p tbl b) in
    lemma_eq_diff i rho project p tbl a d1;
    lemma_eq_diff i rho project p tbl b d2;
    lemma_same_zero_set (valuation i rho project p tbl) p d1 d2;
    lemma_bool_iff i rho a b

(* ----------------------------------------------------------------- *)
(* A conditional term compared with a numeral                          *)
(* ----------------------------------------------------------------- *)

(* The Boolean `x` has the truth value of the finite-field equality `atom`:
   it is that equality, a constant it is decided to equal, or another
   finite-field equality with a unit-proportional difference. *)
let atom_equivalent (atom x:expr) : bool =
  x = atom || eq_truth_equivalent atom x || eq_eq_equivalent atom x

let lemma_atom_equivalent (i:interpretation value) (rho:env value) (project:int -> value -> int)
                          (atom x:expr)
  : Lemma (requires ff_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    atom_equivalent atom x)
          (ensures eval i atom rho == eval i x rho)
  = if x = atom then ()
    else if eq_truth_equivalent atom x then lemma_eq_truth_equivalent i rho project atom x
    else lemma_eq_eq_equivalent i rho project atom x

(* The parts of `(= (ite c t u) k)` and of the binary conjunction `(and x y)`. *)
let ite_eq_parts (a:expr) : option (expr & expr & expr & expr) =
  match eq_parts a with
  | Some (l, k) ->
    (match Z3ArrayRewrite.ite_parts l with
     | Some (c, t, u) -> Some (c, t, u, k)
     | None -> None)
  | None -> None

let conjunction_parts (b:expr) : option (expr & expr) =
  match b with
  | App f [x; y] ->
    if Z3BooleanRewrite.connective_app Z3BooleanRewrite.Conjunction f [x; y]
    then Some (x, y) else None
  | _ -> None

(* `(= (ite c t u) k)` equals `(and x (not c))` when the equality `t = k` is
   decided false and `x` is the equality `u = k`, and `(and x c)` when `u = k`
   is decided false and `x` is the equality `t = k`. A branch is decided
   false by a nonzero constant difference, so no inverse is needed. *)
let ite_eq_equivalent (a b:expr) : bool =
  match ite_eq_parts a, conjunction_parts b with
  | Some (c, t, u, k), Some (x, y) ->
    let at = mk_eq_expr t k in
    let au = mk_eq_expr u k in
    (y = mk_not_expr c && eq_truth_equivalent at false_expr && atom_equivalent au x) ||
    (y = c && eq_truth_equivalent au false_expr && atom_equivalent at x)
  | _, _ -> false

let lemma_eq_lit (i:interpretation value) (rho:env value) (e s t:expr)
  : Lemma (requires Z3BooleanRewrite.boolean_rewrite_model i /\ eq_parts e == Some (s, t))
          (ensures lit_true i rho e <==> eval i s rho == eval i t rho)
  = match e with
    | App f [_; _] -> assert (f.decl_name == "=")
    | _ -> ()

let lemma_false_atom (i:interpretation value) (rho:env value) (project:int -> value -> int)
                     (atom:expr)
  : Lemma (requires ff_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    eq_truth_equivalent atom false_expr)
          (ensures ~(lit_true i rho atom))
  = lemma_eq_truth_equivalent i rho project atom false_expr;
    assert (eval i false_expr rho == VBool false)

let lemma_not_lit (i:interpretation value) (rho:env value) (c:expr)
  : Lemma (requires Z3BooleanRewrite.boolean_rewrite_model i /\ get_sort c == bool_sort)
          (ensures lit_true i rho (mk_not_expr c) <==> ~(lit_true i rho c))
  = match eval i c rho with
    | VBool _ -> ()
    | _ -> ()

let lemma_conjunction_lit (i:interpretation value) (rho:env value) (b x y:expr)
  : Lemma (requires Z3BooleanRewrite.boolean_rewrite_model i /\ conjunction_parts b == Some (x, y))
          (ensures lit_true i rho b <==> (lit_true i rho x /\ lit_true i rho y))
  = assert_norm (conj_holds i rho [x; y] <==> (lit_true i rho x /\ lit_true i rho y));
    match b with
    | App f [_; _] -> assert (f.decl_name == "and")
    | _ -> ()

let lemma_ite_eq_equivalent (i:interpretation value) (rho:env value) (project:int -> value -> int)
                            (a b:expr)
  : Lemma (requires ff_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    Z3ArrayRewrite.term_ite_sound i /\ ite_eq_equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = let (l, k) = Some?.v (eq_parts a) in
    let (c, t, u) = Some?.v (Z3ArrayRewrite.ite_parts l) in
    let (x, y) = Some?.v (conjunction_parts b) in
    let at = mk_eq_expr t k in
    let au = mk_eq_expr u k in
    lemma_eq_lit i rho a l k;
    Z3ArrayRewrite.lemma_ite_parts i rho l c t u;
    assert (get_sort t == get_sort k);
    lemma_eq_lit i rho at t k;
    lemma_eq_lit i rho au u k;
    lemma_conjunction_lit i rho b x y;
    if y = mk_not_expr c then (
      lemma_false_atom i rho project at;
      lemma_atom_equivalent i rho project au x;
      lemma_not_lit i rho c)
    else (
      lemma_false_atom i rho project au;
      lemma_atom_equivalent i rho project at x);
    lemma_bool_iff i rho a b

(* ----------------------------------------------------------------- *)
(* Entry point                                                         *)
(* ----------------------------------------------------------------- *)

let equivalent (a b:expr) : bool =
  term_equivalent a b || eq_eq_equivalent a b ||
  eq_truth_equivalent a b || eq_truth_equivalent b a || ite_eq_equivalent a b

let lemma_equivalent (i:interpretation value) (rho:env value) (project:int -> value -> int)
                     (a b:expr)
  : Lemma (requires ff_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    Z3ArrayRewrite.term_ite_sound i /\ equivalent a b)
          (ensures eval i a rho == eval i b rho)
  = if term_equivalent a b then lemma_term_equivalent i rho project a b
    else if eq_eq_equivalent a b then lemma_eq_eq_equivalent i rho project a b
    else if eq_truth_equivalent a b then lemma_eq_truth_equivalent i rho project a b
    else if eq_truth_equivalent b a then lemma_eq_truth_equivalent i rho project b a
    else lemma_ite_eq_equivalent i rho project a b

(* ----------------------------------------------------------------- *)
(* Theory lemmas: exhaustive evaluation over the residues of Z/pZ      *)
(* ----------------------------------------------------------------- *)

(* A finite-field `th-lemma` is a clause whose literals compare `FF<p>` terms.
   It is checked by evaluating it under every assignment of residues in
   [0, p) to its leaves, the closed `FF<p>` subterms that are not numerals,
   field operations or conditional terms. Under `ff_model` the leaves of any
   model take residues in [0, p) and every field operation is the matching
   operation modulo p, so the enumeration covers every model: a clause that
   evaluates to true under every assignment holds. Only evaluation in the
   ring Z/pZ is used, so `p` need not be prime, and the producer's
   certificate parameters are not read. The number p^n of assignments is
   bounded by `max_assignments` before anything is enumerated; a larger
   clause, or one with a connective or term outside this fragment, stays
   unchecked. *)

let max_assignments : nat = 4096

let leaf (p:pos) (tbl:list expr) (v:nat -> int) (e:expr) : option int =
  if get_sort e = ff_sort p
  then (match index_of e tbl with Some k -> Some (v k) | None -> None)
  else None

(* The residue of an `FF<p>` term and the truth value of a Boolean term when
   the k-th leaf of `tbl` has residue `v k`; `None` outside the fragment. *)
let rec eval_ff (p:pos) (tbl:list expr) (v:nat -> int) (e:expr) : Tot (option int) (decreases e) =
  match numeral e with
  | Some (q, n) -> if q = p then Some n else None
  | None ->
    (match e with
     | App f args ->
       (match operation f args with
        | Some (q, op) ->
          if q <> p then None
          else (match eval_ffs p tbl v args with
                | Some xs -> Some (calculate p op xs)
                | None -> None)
        | None ->
          (match args with
           | [c; t; u] ->
             if f = Z3ArrayRewrite.term_ite_decl (ff_sort p) && get_sort c = bool_sort &&
                get_sort t = ff_sort p && get_sort u = ff_sort p
             then (match eval_bool p tbl v c with
                   | Some true -> eval_ff p tbl v t
                   | Some false -> eval_ff p tbl v u
                   | None -> None)
             else leaf p tbl v e
           | _ -> leaf p tbl v e))
     | _ -> leaf p tbl v e)

and eval_ffs (p:pos) (tbl:list expr) (v:nat -> int) (args:list expr)
  : Tot (option (list int)) (decreases args) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match eval_ff p tbl v a, eval_ffs p tbl v rest with
     | Some x, Some xs -> Some (x :: xs)
     | _, _ -> None)

and eval_bool (p:pos) (tbl:list expr) (v:nat -> int) (e:expr) : Tot (option bool) (decreases e) =
  match e with
  | App f args ->
    if get_sort e <> bool_sort then None
    else if C.canonical_true f && args = [] then Some true
    else if C.canonical_false f && args = [] then Some false
    else if C.canonical_not f then
      (match args with
       | [a] -> (match eval_bool p tbl v a with Some b -> Some (not b) | None -> None)
       | _ -> None)
    else if C.canonical_or f then eval_or p tbl v args
    else if C.canonical_and f then eval_and p tbl v args
    else if C.canonical_eq f then
      (match args with
       | [a; b] ->
         if get_sort a = ff_sort p && get_sort b = ff_sort p then
           (match eval_ff p tbl v a, eval_ff p tbl v b with
            | Some x, Some y -> Some (x = y)
            | _, _ -> None)
         else if get_sort a = bool_sort && get_sort b = bool_sort then
           (match eval_bool p tbl v a, eval_bool p tbl v b with
            | Some x, Some y -> Some (x = y)
            | _, _ -> None)
         else None
       | _ -> None)
    else None
  | _ -> None

and eval_or (p:pos) (tbl:list expr) (v:nat -> int) (args:list expr)
  : Tot (option bool) (decreases args) =
  match args with
  | [] -> Some false
  | a :: rest ->
    (match eval_bool p tbl v a, eval_or p tbl v rest with
     | Some x, Some y -> Some (x || y)
     | _, _ -> None)

and eval_and (p:pos) (tbl:list expr) (v:nat -> int) (args:list expr)
  : Tot (option bool) (decreases args) =
  match args with
  | [] -> Some true
  | a :: rest ->
    (match eval_bool p tbl v a, eval_and p tbl v rest with
     | Some x, Some y -> Some (x && y)
     | _, _ -> None)

(* Untrusted search for the leaves and the modulus; a missing leaf or a wrong
   modulus only makes the evaluation fail. Leaves are identified by structural
   equality and each is recorded once (`lemma_leaves_unique`). *)
let add_leaf (tbl:list expr) (e:expr) : list expr =
  if L.mem e tbl then tbl else L.append tbl [e]

let rec leaves (p:int) (tbl:list expr) (e:expr) : Tot (list expr) (decreases e) =
  match numeral e with
  | Some _ -> tbl
  | None ->
    (match e with
     | App f args ->
       if Some? (operation f args) || get_sort e <> ff_sort p || Some? (Z3ArrayRewrite.ite_parts e)
       then leaves_args p tbl args
       else add_leaf tbl e
     | _ -> if get_sort e = ff_sort p then add_leaf tbl e else tbl)

and leaves_args (p:int) (tbl:list expr) (args:list expr) : Tot (list expr) (decreases args) =
  match args with
  | [] -> tbl
  | a :: rest -> leaves_args p (leaves p tbl a) rest

let rec find_modulus (e:expr) : Tot (option int) (decreases e) =
  match modulus_of e with
  | Some p -> Some p
  | None -> (match e with App _ args -> find_modulus_args args | _ -> None)

and find_modulus_args (args:list expr) : Tot (option int) (decreases args) =
  match args with
  | [] -> None
  | a :: rest -> (match find_modulus a with Some p -> Some p | None -> find_modulus_args rest)

(* `within_budget p n 1` decides p^n <= max_assignments by multiplying one
   factor at a time and stopping as soon as the product exceeds the bound, so
   p^n is never formed for a large modulus or many leaves. *)
let rec within_budget (p:int) (n:nat) (acc:int) : Tot bool (decreases n) =
  if acc > max_assignments then false
  else if n = 0 then true
  else within_budget p (n - 1) (acc * p)

(* `for_all_vectors p n f` evaluates `f` on every list of n residues in [0, p). *)
let with_head (f:list int -> bool) (x:int) (r:list int) : bool = f (x :: r)

let rec for_all_vectors (p:nat) (n:nat) (f:list int -> bool) : Tot bool (decreases %[n; 0; 0]) =
  if n = 0 then f [] else for_all_heads p p (n - 1) f

and for_all_heads (p:nat) (k:nat) (n:nat) (f:list int -> bool) : Tot bool (decreases %[n; 1; k]) =
  if k = 0 then true
  else for_all_vectors p n (with_head f (k - 1)) && for_all_heads p (k - 1) n f

let vector_value (r:list int) : nat -> int =
  fun k -> if k < L.length r then L.index r k else 0

let clause_true (p:pos) (tbl:list expr) (e:expr) (r:list int) : bool =
  eval_bool p tbl (vector_value r) e = Some true

(* The side conditions are tested in order and each guards the next, so no
   assignment is enumerated unless the clause is closed, Boolean, over a
   single modulus p >= 2 and within the bound. *)
let exhaustive_clause (e:expr) : bool =
  match find_modulus e with
  | None -> false
  | Some p ->
    if p >= 2 && D.scoped [] e && get_sort e = bool_sort then
      let tbl = leaves p [] e in
      if within_budget p (L.length tbl) 1 && L.for_all (closed_ff p) tbl
      then for_all_vectors p (L.length tbl) (clause_true p tbl e)
      else false
    else false

(* --- The leaf table and the bound ----------------------------------- *)

let rec lemma_append_fresh (tbl:list expr) (e:expr)
  : Lemma (requires L.noRepeats tbl /\ not (L.mem e tbl))
          (ensures L.noRepeats (L.append tbl [e]))
          (decreases tbl)
  = match tbl with
    | [] -> ()
    | x :: rest ->
      FStar.List.Tot.Properties.append_mem rest [e] x;
      assert_norm (L.mem x [e] == (x = e));
      lemma_append_fresh rest e

let lemma_add_leaf_unique (tbl:list expr) (e:expr)
  : Lemma (requires L.noRepeats tbl) (ensures L.noRepeats (add_leaf tbl e))
  = if L.mem e tbl then () else lemma_append_fresh tbl e

let rec lemma_leaves_unique (p:int) (tbl:list expr) (e:expr)
  : Lemma (requires L.noRepeats tbl) (ensures L.noRepeats (leaves p tbl e)) (decreases e)
  = match numeral e with
    | Some _ -> ()
    | None ->
      (match e with
       | App f args ->
         if Some? (operation f args) || get_sort e <> ff_sort p || Some? (Z3ArrayRewrite.ite_parts e)
         then lemma_leaves_args_unique p tbl args
         else lemma_add_leaf_unique tbl e
       | _ -> if get_sort e = ff_sort p then lemma_add_leaf_unique tbl e else ())

and lemma_leaves_args_unique (p:int) (tbl:list expr) (args:list expr)
  : Lemma (requires L.noRepeats tbl) (ensures L.noRepeats (leaves_args p tbl args)) (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_leaves_unique p tbl a;
      lemma_leaves_args_unique p (leaves p tbl a) rest

let rec power (p:int) (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else p * power p (n - 1)

(* The enumeration is entered only when p^n <= max_assignments. *)
let rec lemma_within_budget (p:pos) (n:nat) (acc:pos)
  : Lemma (requires within_budget p n acc) (ensures acc * power p n <= max_assignments) (decreases n)
  = if n = 0 then ()
    else (
      lemma_within_budget p (n - 1) (acc * p);
      M.paren_mul_right acc p (power p (n - 1)))

let lemma_exhaustive_clause_bound (e:expr)
  : Lemma (requires exhaustive_clause e)
          (ensures (let p = Some?.v (find_modulus e) in
                    p >= 2 /\ L.noRepeats (leaves p [] e) /\
                    power p (L.length (leaves p [] e)) <= max_assignments))
  = let p = Some?.v (find_modulus e) in
    lemma_leaves_unique p [] e;
    lemma_within_budget p (L.length (leaves p [] e)) 1

(* --- Soundness ------------------------------------------------------ *)

let rec in_range (p:int) (r:list int) : Tot bool (decreases r) =
  match r with
  | [] -> true
  | x :: rest -> 0 <= x && x < p && in_range p rest

(* Coverage: every vector of n residues in [0, p) is enumerated. *)
let rec lemma_for_all_vectors (p:nat) (n:nat) (f:list int -> bool) (r:list int)
  : Lemma (requires for_all_vectors p n f /\ L.length r == n /\ in_range p r)
          (ensures f r)
          (decreases %[n; 0; 0])
  = match r with
    | [] -> ()
    | x :: rest -> lemma_for_all_heads p p (n - 1) f x rest

and lemma_for_all_heads (p:nat) (k:nat) (n:nat) (f:list int -> bool) (x:int) (rest:list int)
  : Lemma (requires for_all_heads p k n f /\ 0 <= x /\ x < k /\ L.length rest == n /\ in_range p rest)
          (ensures f (x :: rest))
          (decreases %[n; 1; k])
  = if x = k - 1 then lemma_for_all_vectors p n (with_head f (k - 1)) rest
    else lemma_for_all_heads p (k - 1) n f x rest

(* The assignment `v` gives every leaf its residue in the model. *)
let agrees (i:interpretation value) (rho:env value) (project:int -> value -> int)
           (p:int) (tbl:list expr) (v:nat -> int) : prop =
  forall (k:nat). k < L.length tbl ==> v k == project p (eval i (L.index tbl k) rho)

let eval_model (i:interpretation value) (project:int -> value -> int) : prop =
  ff_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\ Z3ArrayRewrite.term_ite_sound i

let lemma_scoped_app (f:func_decl) (args:list expr)
  : Lemma (requires D.scoped [] (App f args)) (ensures D.scoped_args [] args)
  = ()

let lemma_scoped_cons (a:expr) (rest:list expr)
  : Lemma (requires D.scoped_args [] (a :: rest)) (ensures D.scoped [] a /\ D.scoped_args [] rest)
  = ()

let lemma_leaf (i:interpretation value) (rho:env value) (project:int -> value -> int)
               (p:pos) (tbl:list expr) (v:nat -> int) (e:expr)
  : Lemma (requires agrees i rho project p tbl v /\ Some? (leaf p tbl v e))
          (ensures project p (eval i e rho) == Some?.v (leaf p tbl v e))
  = let k = Some?.v (index_of e tbl) in
    lemma_index_of e tbl k

let lemma_bool_value (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires Z3BooleanRewrite.boolean_rewrite_model i /\ get_sort e == bool_sort)
          (ensures VBool? (eval i e rho))
  = ()

let rec lemma_eval_ff (i:interpretation value) (rho:env value) (project:int -> value -> int)
                      (p:pos) (tbl:list expr) (v:nat -> int) (e:expr)
  : Lemma (requires eval_model i project /\ p >= 2 /\ D.scoped [] e /\
                    agrees i rho project p tbl v /\ Some? (eval_ff p tbl v e))
          (ensures project p (eval i e rho) == Some?.v (eval_ff p tbl v e))
          (decreases e)
  = match numeral e with
    | Some (q, n) -> assert (project q (eval i e rho) == n)
    | None ->
      (match e with
       | App f args ->
         (match operation f args with
          | Some (q, op) ->
            lemma_scoped_app f args;
            lemma_eval_ffs i rho project p tbl v args;
            assert (project p (eval i e rho) == calculate p op (projections i rho project p args))
          | None ->
            (match args with
             | [c; t; u] ->
               if f = Z3ArrayRewrite.term_ite_decl (ff_sort p) && get_sort c = bool_sort &&
                  get_sort t = ff_sort p && get_sort u = ff_sort p
               then (
                 lemma_scoped_app f args;
                 lemma_scoped_cons c [t; u];
                 lemma_scoped_cons t [u];
                 lemma_scoped_cons u [];
                 lemma_eval_bool i rho project p tbl v c;
                 Z3ArrayRewrite.lemma_ite_parts i rho e c t u;
                 match eval_bool p tbl v c with
                 | Some true -> lemma_eval_ff i rho project p tbl v t
                 | Some false -> lemma_eval_ff i rho project p tbl v u)
               else lemma_leaf i rho project p tbl v e
             | _ -> lemma_leaf i rho project p tbl v e))
       | _ -> lemma_leaf i rho project p tbl v e)

and lemma_eval_ffs (i:interpretation value) (rho:env value) (project:int -> value -> int)
                   (p:pos) (tbl:list expr) (v:nat -> int) (args:list expr)
  : Lemma (requires eval_model i project /\ p >= 2 /\ D.scoped_args [] args /\
                    agrees i rho project p tbl v /\ Some? (eval_ffs p tbl v args))
          (ensures Some?.v (eval_ffs p tbl v args) == projections i rho project p args)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_scoped_cons a rest;
      lemma_eval_ff i rho project p tbl v a;
      lemma_eval_ffs i rho project p tbl v rest

and lemma_eval_bool (i:interpretation value) (rho:env value) (project:int -> value -> int)
                    (p:pos) (tbl:list expr) (v:nat -> int) (e:expr)
  : Lemma (requires eval_model i project /\ p >= 2 /\ D.scoped [] e /\
                    agrees i rho project p tbl v /\ Some? (eval_bool p tbl v e))
          (ensures eval i e rho == VBool (Some?.v (eval_bool p tbl v e)))
          (decreases e)
  = match e with
    | App f args ->
      lemma_bool_value i rho e;
      lemma_scoped_app f args;
      if C.canonical_true f && args = [] then ()
      else if C.canonical_false f && args = [] then ()
      else if C.canonical_not f then
        (match args with
         | [a] ->
           lemma_scoped_cons a [];
           lemma_eval_bool i rho project p tbl v a)
      else if C.canonical_or f then lemma_eval_or i rho project p tbl v args
      else if C.canonical_and f then lemma_eval_and i rho project p tbl v args
      else
        (match args with
         | [a; b] ->
           lemma_scoped_cons a [b];
           lemma_scoped_cons b [];
           if get_sort a = ff_sort p && get_sort b = ff_sort p then (
             lemma_eval_ff i rho project p tbl v a;
             lemma_eval_ff i rho project p tbl v b;
             assert (eval i a rho == eval i b rho <==>
                     project p (eval i a rho) == project p (eval i b rho)))
           else (
             lemma_eval_bool i rho project p tbl v a;
             lemma_eval_bool i rho project p tbl v b))

and lemma_eval_or (i:interpretation value) (rho:env value) (project:int -> value -> int)
                  (p:pos) (tbl:list expr) (v:nat -> int) (args:list expr)
  : Lemma (requires eval_model i project /\ p >= 2 /\ D.scoped_args [] args /\
                    agrees i rho project p tbl v /\ Some? (eval_or p tbl v args))
          (ensures Some?.v (eval_or p tbl v args) == true <==> clause_holds i rho args)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_scoped_cons a rest;
      lemma_eval_bool i rho project p tbl v a;
      lemma_eval_or i rho project p tbl v rest

and lemma_eval_and (i:interpretation value) (rho:env value) (project:int -> value -> int)
                   (p:pos) (tbl:list expr) (v:nat -> int) (args:list expr)
  : Lemma (requires eval_model i project /\ p >= 2 /\ D.scoped_args [] args /\
                    agrees i rho project p tbl v /\ Some? (eval_and p tbl v args))
          (ensures Some?.v (eval_and p tbl v args) == true <==> conj_holds i rho args)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_scoped_cons a rest;
      lemma_eval_bool i rho project p tbl v a;
      lemma_eval_and i rho project p tbl v rest

(* The residues of the leaves in the model form one of the enumerated vectors. *)
let rec lemma_projections_index (i:interpretation value) (rho:env value) (project:int -> value -> int)
                                (p:int) (tbl:list expr) (k:nat)
  : Lemma (requires k < L.length tbl)
          (ensures L.length (projections i rho project p tbl) == L.length tbl /\
                   L.index (projections i rho project p tbl) k == project p (eval i (L.index tbl k) rho))
          (decreases tbl)
  = match tbl with
    | _ :: rest -> if k = 0 then () else lemma_projections_index i rho project p rest (k - 1)

let rec lemma_projections_range (i:interpretation value) (rho:env value) (project:int -> value -> int)
                                (p:int) (tbl:list expr)
  : Lemma (requires ff_model i project /\ p >= 2 /\ L.for_all (closed_ff p) tbl)
          (ensures L.length (projections i rho project p tbl) == L.length tbl /\
                   in_range p (projections i rho project p tbl))
          (decreases tbl)
  = match tbl with
    | [] -> ()
    | a :: rest ->
      lemma_range i rho project p a;
      lemma_projections_range i rho project p rest

let lemma_projections_agree (i:interpretation value) (rho:env value) (project:int -> value -> int)
                            (p:int) (tbl:list expr)
  : Lemma (agrees i rho project p tbl (vector_value (projections i rho project p tbl)))
  = let aux (k:nat)
      : Lemma (k < L.length tbl ==>
               vector_value (projections i rho project p tbl) k ==
               project p (eval i (L.index tbl k) rho))
      = if k < L.length tbl then lemma_projections_index i rho project p tbl k in
    FStar.Classical.forall_intro aux

let lemma_exhaustive_clause (i:interpretation value) (rho:env value) (project:int -> value -> int)
                            (e:expr)
  : Lemma (requires eval_model i project /\ exhaustive_clause e)
          (ensures lit_true i rho e)
  = let p : pos = Some?.v (find_modulus e) in
    let tbl = leaves p [] e in
    let r = projections i rho project p tbl in
    lemma_projections_range i rho project p tbl;
    lemma_for_all_vectors p (L.length tbl) (clause_true p tbl e) r;
    lemma_projections_agree i rho project p tbl;
    lemma_eval_bool i rho project p tbl (vector_value r) e

let lemma_exhaustive_clause_sound (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires (exists (project:int -> value -> int). ff_model i project) /\
                    Z3BooleanRewrite.boolean_rewrite_model i /\ Z3ArrayRewrite.term_ite_sound i /\
                    exhaustive_clause e)
          (ensures lit_true i rho e)
  = let aux (project:int -> value -> int)
      : Lemma (requires ff_model i project) (ensures lit_true i rho e)
      = lemma_exhaustive_clause i rho project e in
    FStar.Classical.exists_elim (lit_true i rho e)
      #(int -> value -> int) #(fun project -> ff_model i project) () (fun project -> aux project)
