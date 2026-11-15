module Z3SortedFiniteField

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

open Z3AstTheory
open Z3OperatorTags
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module DT = Z3DatatypeSyntax
module SS = Z3SortedSemantics
module D = Z3ExprScope
module R = Z3ClauseSyntax
module B = Z3BoundedBoolEquiv
module PT = Z3ProofTheory
module C = Z3CanonicalOps
module IX = Z3ProofIndex
module A = Z3ArraySyntax
module SArray = Z3SortedArray
module SBR = Z3SortedBooleanRewrite
module L = FStar.List.Tot
module M = FStar.Math.Lemmas

(* This module deliberately owns the finite-field syntax and semantic
   interface: importing either legacy checker here would reintroduce the
   untyped value model through the dependency closure. *)

let op_ff_num : decl_kind = 300
let op_ff_add : decl_kind = 301
let op_ff_mul : decl_kind = 302
let op_ff_neg : decl_kind = 303
let op_ff_bitsum : decl_kind = 304

let ff_sort (p:int) : sort = SortApp (FiniteFieldSymbol p) []

let numeral (e:expr) : option (int & int) =
  match e with
  | App f [] ->
    (match f.int_params with
     | [p; n] ->
       if p >= 2 && f.interp = Some op_ff_num && f.domain = [] &&
          f.range = ff_sort p && 0 <= n && n < p
       then Some (p, n)
       else None
     | _ -> None)
  | _ -> None

let rec repeat_sort (p:int) (n:nat) : Tot (list sort) (decreases n) =
  if n = 0 then [] else ff_sort p :: repeat_sort p (n - 1)

let rec args_have_sort (p:int) (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> sort_eq (get_sort a) (ff_sort p) && args_have_sort p rest

let operation_of (f:func_decl) : Tot (option (int & decl_kind)) =
  match f.int_params, f.interp with
  | [p], Some tag ->
    if p < 2 || not (sort_eq f.range (ff_sort p)) then None
    else if tag = op_ff_neg && sort_list_eq f.domain [ff_sort p] then Some (p, op_ff_neg)
    else if tag = op_ff_add && sort_list_eq f.domain (repeat_sort p (L.length f.domain)) &&
            L.length f.domain >= 2 then Some (p, op_ff_add)
    else if tag = op_ff_mul && sort_list_eq f.domain (repeat_sort p (L.length f.domain)) &&
            L.length f.domain >= 2 then Some (p, op_ff_mul)
    else if tag = op_ff_bitsum && sort_list_eq f.domain (repeat_sort p (L.length f.domain)) &&
            L.length f.domain >= 2 then Some (p, op_ff_bitsum)
    else None
  | _, _ -> None

let operation_at (f:func_decl) (args:list expr) : Tot (option (int & decl_kind)) =
  match operation_of f with
  | Some (p, op) ->
    if args_have_sort p args &&
       L.length args = L.length f.domain
    then Some (p, op)
    else None
  | None -> None

let rec sum_mod (p:pos) (xs:list int) : Tot int (decreases xs) =
  match xs with
  | [] -> 0
  | x :: rest -> (x + sum_mod p rest) % p

let rec product_mod (p:pos) (xs:list int) : Tot int (decreases xs) =
  match xs with
  | [] -> 1 % p
  | x :: rest -> (x * product_mod p rest) % p

let rec bitsum_mod (p:pos) (weight:int) (xs:list int) : Tot int (decreases xs) =
  match xs with
  | [] -> 0
  | x :: rest -> (x * weight + bitsum_mod p (2 * weight) rest) % p

let calculate (p:pos) (op:decl_kind) (xs:list int) : int =
  if op = op_ff_add then sum_mod p xs
  else if op = op_ff_mul then product_mod p xs
  else if op = op_ff_bitsum then bitsum_mod p 1 xs
  else match xs with [x] -> (0 - x) % p | _ -> 0

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
  | (m2, c2) :: rest ->
    padd [(mono_mul m m2, c * c2)] (pmul_term m c rest)

let rec pmul (a b:poly) : Tot poly (decreases a) =
  match a with
  | [] -> []
  | (m, c) :: rest -> padd (pmul_term m c b) (pmul rest b)

let rec psum (qs:list poly) : Tot poly (decreases qs) =
  match qs with
  | [] -> []
  | q :: rest -> padd q (psum rest)

let max_product_terms : nat = 256

let rec pprod (qs:list poly) : Tot (option poly) (decreases qs) =
  match qs with
  | [] -> Some [([], 1)]
  | q :: rest ->
    (match pprod rest with
     | None -> None
     | Some r ->
       if L.length q * L.length r > max_product_terms then None
       else Some (pmul q r))

let rec pbitsum (weight:int) (qs:list poly) : Tot poly (decreases qs) =
  match qs with
  | [] -> []
  | q :: rest -> padd (pscale weight q) (pbitsum (2 * weight) rest)

let combine (op:decl_kind) (qs:list poly) : option poly =
  if op = op_ff_add then Some (psum qs)
  else if op = op_ff_mul then pprod qs
  else if op = op_ff_bitsum then Some (pbitsum 1 qs)
  else match qs with [q] -> Some (pscale (-1) q) | _ -> None

let lemma_mul_swap3 (a x b:int) : Lemma (a * (x * b) == x * (a * b)) =
  M.paren_mul_right a x b;
  M.swap_mul a x;
  M.paren_mul_right x a b

let lemma_mul4 (a b c d:int)
  : Lemma ((a * b) * (c * d) == (a * c) * (b * d)) =
  M.paren_mul_right a b (c * d);
  lemma_mul_swap3 b c d;
  M.paren_mul_right a c (b * d)

let rec lemma_mval_mul (v:nat -> int) (a b:mono)
  : Lemma (ensures mval v (mono_mul a b) == mval v a * mval v b)
          (decreases (L.length a + L.length b)) =
  match a, b with
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
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | (m1, c1) :: a', (m2, c2) :: b' ->
    if m1 = m2 then (
      lemma_padd v a' b';
      M.distributivity_add_left c1 c2 (mval v m1))
    else if mono_lt m1 m2 then lemma_padd v a' b
    else lemma_padd v a b'

let rec lemma_pscale (v:nat -> int) (k:int) (q:poly)
  : Lemma (ensures peval v (pscale k q) == k * peval v q) (decreases q) =
  match q with
  | [] -> ()
  | (m, c) :: rest ->
    lemma_pscale v k rest;
    M.paren_mul_right k c (mval v m);
    M.distributivity_add_right k (c * mval v m) (peval v rest)

#push-options "--fuel 2"
let rec lemma_pmul_term (v:nat -> int) (m:mono) (c:int) (b:poly)
  : Lemma (ensures peval v (pmul_term m c b) == (c * mval v m) * peval v b)
          (decreases b) =
  match b with
  | [] -> ()
  | (m2, c2) :: rest ->
    lemma_pmul_term v m c rest;
    lemma_mval_mul v m m2;
    lemma_padd v [(mono_mul m m2, c * c2)] (pmul_term m c rest);
    lemma_mul4 c c2 (mval v m) (mval v m2);
    M.distributivity_add_right (c * mval v m) (c2 * mval v m2) (peval v rest)
#pop-options

let rec lemma_pmul (v:nat -> int) (a b:poly)
  : Lemma (ensures peval v (pmul a b) == peval v a * peval v b) (decreases a) =
  match a with
  | [] -> ()
  | (m, c) :: rest ->
    lemma_pmul v rest b;
    lemma_pmul_term v m c b;
    lemma_padd v (pmul_term m c b) (pmul rest b);
    M.distributivity_add_left (c * mval v m) (peval v rest) (peval v b)

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
          (decreases qs) =
  match qs, xs with
  | q :: qs', x :: xs' ->
    lemma_psum v p qs' xs';
    lemma_padd v q (psum qs');
    lemma_add_cong p (peval v q) (peval v (psum qs')) x (sum_mod p xs')
  | _, _ -> ()

#push-options "--fuel 2"
let rec lemma_pprod (v:nat -> int) (p:pos) (qs:list poly) (xs:list int) (r:poly)
  : Lemma (requires match_list v p qs xs /\ pprod qs == Some r)
          (ensures peval v r % p == product_mod p xs)
          (decreases qs) =
  match qs, xs with
  | q :: qs', x :: xs' ->
    let r' = Some?.v (pprod qs') in
    lemma_pprod v p qs' xs' r';
    lemma_pmul v q r';
    lemma_mul_cong p (peval v q) (peval v r') x (product_mod p xs')
  | _, _ -> ()
#pop-options

let rec lemma_pbitsum (v:nat -> int) (p:pos) (weight:int)
                      (qs:list poly) (xs:list int)
  : Lemma (requires match_list v p qs xs)
          (ensures peval v (pbitsum weight qs) % p == bitsum_mod p weight xs)
          (decreases qs) =
  match qs, xs with
  | q :: qs', x :: xs' ->
    lemma_pbitsum v p (2 * weight) qs' xs';
    lemma_pscale v weight q;
    lemma_padd v (pscale weight q) (pbitsum (2 * weight) qs');
    lemma_mul_cong p weight (peval v q) weight x;
    lemma_add_cong p (weight * peval v q) (peval v (pbitsum (2 * weight) qs'))
                     (x * weight) (bitsum_mod p (2 * weight) xs')
  | _, _ -> ()

#push-options "--fuel 2"
let lemma_combine (v:nat -> int) (p:pos) (op:decl_kind) (qs:list poly)
                  (xs:list int) (r:poly)
  : Lemma (requires match_list v p qs xs /\ combine op qs == Some r)
          (ensures peval v r % p == calculate p op xs)
  = if op = op_ff_add then lemma_psum v p qs xs
    else if op = op_ff_mul then lemma_pprod v p qs xs r
    else if op = op_ff_bitsum then lemma_pbitsum v p 1 qs xs
    else
      match qs, xs with
      | [q], [x] ->
        lemma_pscale v (-1) q;
        M.lemma_mod_sub_distr 0 (peval v q) p
      | _, _ -> ()
#pop-options

(* PAC certificate format and the original production replay limits. *)
include Z3FiniteFieldCertificate

let max_premises : nat = 4096
let max_variables : nat = 4096
let max_equations : nat = 8192
let max_nodes : nat = 100000
let max_poly_size : nat = 16384
let max_work : nat = 4000000

type origin =
  | Definition
  | Premise : index:nat -> literal:expr -> origin
  | Witness

type equation = poly & origin

type encoding = {
  terms: list expr;
  equations: list equation;
  count: nat;
}

let empty_encoding : encoding = { terms = []; equations = []; count = 0 }

let rec index_of (e:expr) (tbl:list expr) : Tot (option nat) (decreases tbl) =
  match tbl with
  | [] -> None
  | x :: rest ->
    if x = e then Some 0
    else (match index_of e rest with Some k -> Some (k + 1) | None -> None)

let term_poly (p:int) (tbl:list expr) (t:expr) : option poly =
  match numeral t with
  | Some (q, n) -> if q = p then Some [([], n)] else None
  | None ->
    (match index_of t tbl with
     | Some k -> Some [([k], 1)]
     | None -> None)

let rec term_polys (p:int) (tbl:list expr) (ts:list expr)
  : Tot (option (list poly)) (decreases ts) =
  match ts with
  | [] -> Some []
  | t :: rest ->
    (match term_poly p tbl t, term_polys p tbl rest with
     | Some q, Some qs -> Some (q :: qs)
     | _, _ -> None)

let allocate (st:encoding) (t:expr) : option encoding =
  if L.length st.terms + 1 > max_variables then None
  else Some { st with terms = L.append st.terms [t] }

let push (st:encoding) (e:equation) : option encoding =
  if st.count + 1 > max_equations then None
  else Some { st with equations = e :: st.equations; count = st.count + 1 }

let definition (k:nat) (f:poly) : poly =
  padd [([k], 1)] (pscale (-1) f)

let define (st:encoding) (t:expr) (f:poly) : option encoding =
  let k = L.length st.terms in
  match allocate st t with
  | Some st1 -> push st1 (definition k f, Definition)
  | None -> None

let rec visit (p:int) (st:encoding) (t:expr) : Tot (option encoding) (decreases t) =
  match numeral t with
  | Some (q, _) -> if q = p then Some st else None
  | None ->
    if Some? (index_of t st.terms) then Some st
    else if get_sort t <> ff_sort p then None
    else
      match t with
      | App f args ->
        (match operation_at f args with
         | Some (q, op) ->
           if q <> p then None
           else
             (match visit_args p st args with
              | None -> None
              | Some st1 ->
                (match term_polys p st1.terms args with
                 | None -> None
                 | Some qs ->
                   (match combine op qs with
                    | None -> None
                    | Some f -> define st1 t f)))
         | None -> allocate st t)
      | _ -> None

and visit_args (p:int) (st:encoding) (args:list expr)
  : Tot (option encoding) (decreases args) =
  match args with
  | [] -> Some st
  | a :: rest ->
    (match visit_args p st rest with
     | None -> None
     | Some st1 -> visit p st1 a)

let eq_parts (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] ->
    if f = R.eq_decl (get_sort a) && get_sort a = get_sort b then Some (a, b)
    else None
  | _ -> None

let closed_ff (p:int) (e:expr) : bool =
  D.scoped [] e && get_sort e = ff_sort p

let premise_parts (p:int) (l:expr) : option (bool & expr & expr) =
  let positive, atom =
    match PT.is_not l with
    | Some a -> false, a
    | None -> true, l in
  match eq_parts atom with
  | Some (a, b) ->
    if closed_ff p a && closed_ff p b then Some (positive, a, b) else None
  | None -> None

let premise_equation (p:int) (k:nat) (l a b:expr) (st:encoding)
                     (positive:bool) : option encoding =
  if positive then
    (match term_poly p st.terms a, term_poly p st.terms b with
     | Some qa, Some qb ->
       push st (padd qa (pscale (-1) qb), Premise k l)
     | _, _ -> None)
  else
    (match allocate st l with
     | Some st1 -> push st1 ([], Witness)
     | None -> None)

let rec bind (p:int) (k:nat) (st:encoding) (ps:list expr)
  : Tot (option encoding) (decreases ps) =
  match ps with
  | [] -> Some st
  | l :: rest ->
    (match premise_parts p l with
     | None -> None
     | Some (positive, a, b) ->
       (match visit p st a with
        | None -> None
        | Some st1 ->
          (match visit p st1 b with
           | None -> None
           | Some st2 ->
             (match premise_equation p k l a b st2 positive with
              | None -> None
              | Some st3 -> bind p (k + 1) st3 rest))))

let rec index_equations (tree:IX.index_tree equation) (k:int) (es:list equation)
  : Tot (IX.index_tree equation) (decreases es) =
  match es with
  | [] -> tree
  | e :: rest ->
    if k < 0 then tree else index_equations (IX.index_put tree k e) (k - 1) rest

let clause_literals (e:expr) : list expr =
  match e with
  | App f args -> if C.canonical_or f then args else [e]
  | _ -> [e]

let rec negated_in (l:expr) (lits:list expr) : Tot bool (decreases lits) =
  match lits with
  | [] -> false
  | x :: rest -> PT.is_not x = Some l || negated_in l rest

let rec support_tree (n:int) (previous:int) (tree:IX.index_tree bool) (s:list int)
  : Tot (option (IX.index_tree bool)) (decreases s) =
  match s with
  | [] -> Some tree
  | k :: rest ->
    if 0 <= k && previous < k && k < n
    then support_tree n k (IX.index_put tree k true) rest
    else None

let rec all_used (used:IX.index_tree bool) (s:list int) : Tot bool (decreases s) =
  match s with
  | [] -> true
  | k :: rest -> k >= 0 && IX.index_get used k = Some true && all_used used rest

let rec variables (n:nat) (previous:int) (fs:list int)
  : Tot (option (list nat)) (decreases fs) =
  match fs with
  | [] -> Some []
  | f :: rest ->
    if 0 <= f && previous <= f && f < n
    then (match variables n f rest with Some vs -> Some (f :: vs) | None -> None)
    else None

let rec poly_size (q:poly) : Tot nat (decreases q) =
  match q with
  | [] -> 0
  | (m, _) :: rest -> 1 + L.length m + poly_size rest

let rec scale_mono (m:mono) (c:int) (q:poly) : Tot poly (decreases q) =
  match q with
  | [] -> []
  | (m2, c2) :: rest -> (mono_mul m m2, c * c2) :: scale_mono m c rest

#push-options "--fuel 2"
let rec split (q:poly)
  : Tot (r:(poly & poly){L.length (fst r) + L.length (snd r) == L.length q /\
                          (L.length q >= 2 ==>
                           L.length (fst r) < L.length q /\
                           L.length (snd r) < L.length q)})
        (decreases q) =
  match q with
  | x :: y :: rest -> let (a, b) = split rest in (x :: a, y :: b)
  | _ -> (q, [])
#pop-options

let rec canon (q:poly) : Tot poly (decreases (L.length q)) =
  if L.length q < 2 then q
  else let (a, b) = split q in padd (canon a) (canon b)

let rec reduce (p:pos) (q:poly) : Tot poly (decreases q) =
  match q with
  | [] -> []
  | (m, c) :: rest ->
    if c % p = 0 then reduce p rest else (m, c % p) :: reduce p rest

let normalize (p:pos) (q:poly) : poly = reduce p (canon q)

noeq
type replay = {
  values: IX.index_tree poly;
  next: nat;
  work: nat;
  used: IX.index_tree bool;
}

let initial_replay : replay = { values = IX.Empty; next = 0; work = 0; used = IX.Empty }

let earlier (r:replay) (j:int) : option poly =
  if 0 <= j && j < r.next then IX.index_get r.values j else None

let record (p:pos) (r:replay) (cost:nat) (q:poly)
           (used:IX.index_tree bool) : option replay =
  Some { values = IX.index_put r.values r.next (normalize p q);
         next = r.next + 1; work = r.work + cost; used = used }

let step (p:pos) (nvars:nat) (eqs:IX.index_tree equation)
         (sup:IX.index_tree bool) (lits:list expr) (r:replay)
         (n:pac_node) : option replay =
  match n with
  | PacInput j ->
    if j < 0 then None
    else
      (match IX.index_get eqs j with
       | Some (q, Definition) ->
         if r.work + poly_size q > max_work then None
         else record p r (poly_size q) q r.used
       | Some (q, Premise k l) ->
         if IX.index_get sup k = Some true && negated_in l lits &&
            r.work + poly_size q <= max_work
         then record p r (poly_size q) q (IX.index_put r.used k true)
         else None
       | _ -> None)
  | PacAdd a b ->
    (match earlier r a, earlier r b with
     | Some qa, Some qb ->
       let cost = poly_size qa + poly_size qb in
       if cost > max_poly_size || r.work + cost > max_work then None
       else record p r cost (padd qa qb) r.used
     | _, _ -> None)
  | PacMul source c fs ->
    (match earlier r source, numeral c, variables nvars 0 fs with
     | Some q, Some (pc, k), Some vs ->
       let cost = poly_size q + L.length q * L.length vs in
       if pc <> p || cost > max_poly_size || r.work + cost > max_work
       then None
       else record p r cost (scale_mono vs k q) r.used
     | _, _, _ -> None)

let rec replay_nodes (p:pos) (nvars:nat) (eqs:IX.index_tree equation)
                     (sup:IX.index_tree bool) (lits:list expr)
                     (r:replay) (ns:list pac_node)
  : Tot (option replay) (decreases ns) =
  match ns with
  | [] -> Some r
  | n :: rest ->
    (match step p nvars eqs sup lits r n with
     | Some r' -> replay_nodes p nvars eqs sup lits r' rest
     | None -> None)

let unit_root (r:replay) (root:int) : bool =
  0 <= root && root < r.next &&
  IX.index_get r.values root = Some [([], 1)]

let modulus_of (e:expr) : option int =
  match numeral e with
  | Some (p, _) -> Some p
  | None ->
    (match e with
     | App f args -> (match operation_at f args with Some (p, _) -> Some p | None -> None)
     | _ -> None)

let rec find_modulus (e:expr) : Tot (option int) (decreases e) =
  match modulus_of e with
  | Some p -> Some p
  | None -> (match e with App _ args -> find_modulus_args args | _ -> None)

and find_modulus_args (args:list expr) : Tot (option int) (decreases args) =
  match args with
  | [] -> None
  | a :: rest ->
    (match find_modulus a with Some p -> Some p | None -> find_modulus_args rest)

let check (c:certificate) (e:expr) : bool =
  let n = L.length c.pac_premises in
  if n = 0 || n > max_premises || L.length c.pac_nodes > max_nodes then false
  else
    match find_modulus_args c.pac_premises with
    | None -> false
    | Some p ->
      if p < 2 then false
      else
        (match bind p 0 empty_encoding c.pac_premises,
               support_tree n (-1) IX.Empty c.pac_support with
         | Some st, Some sup ->
           let eqs = index_equations IX.Empty
                       (L.length st.equations - 1) st.equations in
           (match replay_nodes p (L.length st.terms) eqs sup
                    (clause_literals e) initial_replay c.pac_nodes with
            | Some r -> unit_root r c.pac_root && all_used r.used c.pac_support
            | None -> false)
         | _, _ -> false)

#push-options "--fuel 2"
let rec lemma_split (v:nat -> int) (q:poly)
  : Lemma (ensures peval v (fst (split q)) + peval v (snd (split q)) ==
                   peval v q)
          (decreases q) =
  match q with
  | _ :: _ :: rest -> lemma_split v rest
  | _ -> ()
#pop-options

let rec lemma_canon (v:nat -> int) (q:poly)
  : Lemma (ensures peval v (canon q) == peval v q)
          (decreases (L.length q)) =
  if L.length q < 2 then ()
  else (
    let (a, b) = split q in
    lemma_split v q;
    lemma_canon v a;
    lemma_canon v b;
    lemma_padd v (canon a) (canon b))

let rec lemma_reduce (v:nat -> int) (p:pos) (q:poly)
  : Lemma (ensures peval v (reduce p q) % p == peval v q % p)
          (decreases q) =
  match q with
  | [] -> ()
  | (m, c) :: rest ->
    lemma_reduce v p rest;
    M.lemma_mod_mul_distr_l c (mval v m) p;
    if c % p = 0 then
      lemma_add_cong p (c * mval v m) (peval v rest) 0 (peval v (reduce p rest))
    else (
      M.lemma_mod_mul_distr_l (c % p) (mval v m) p;
      M.lemma_mod_twice c p;
      lemma_add_cong p ((c % p) * mval v m) (peval v (reduce p rest))
                        (c * mval v m) (peval v rest))

let lemma_normalize (v:nat -> int) (p:pos) (q:poly)
  : Lemma (peval v (normalize p q) % p == peval v q % p) =
  lemma_canon v q;
  lemma_reduce v p (canon q)

let rec lemma_scale_mono (v:nat -> int) (m:mono) (c:int) (q:poly)
  : Lemma (ensures peval v (scale_mono m c q) ==
                   (c * mval v m) * peval v q)
          (decreases q) =
  match q with
  | [] -> ()
  | (m2, c2) :: rest ->
    lemma_scale_mono v m c rest;
    lemma_mval_mul v m m2;
    lemma_mul4 c c2 (mval v m) (mval v m2);
    M.distributivity_add_right (c * mval v m) (c2 * mval v m2) (peval v rest)

let lemma_zero_product (p:pos) (a b:int)
  : Lemma (requires b % p == 0) (ensures (a * b) % p == 0) =
  M.lemma_mod_mul_distr_r a b p

let lemma_zero_sum (p:pos) (a b:int)
  : Lemma (requires a % p == 0 /\ b % p == 0)
          (ensures (a + b) % p == 0) =
  lemma_add_cong p a b 0 0

#push-options "--fuel 2"
let lemma_peval_constant (v:nat -> int) (n:int)
  : Lemma (peval v [([], n)] == n) = ()

let lemma_peval_variable (v:nat -> int) (k:nat)
  : Lemma (peval v [([k], 1)] == v k) = ()
#pop-options

let rec projections (#base:sort -> Type0) (project:V.tree base -> int)
                    (xs:list (V.tree base)) : Tot (list int) (decreases xs) =
  match xs with
  | [] -> []
  | x :: rest -> project x :: projections project rest

(* Primitive field applications are specified at the operation boundary.
   The interface is polymorphic in the sorted base carriers and is separate
   from the arbitrary interpretation used for declarations outside FF. *)
noeq
type model (base:sort -> Type0) (schema:S.checked_schema) (p:pos) = {
  booleans: S.boolean_carrier base;
  scalar_model: SS.scalar_model base;
  other: V.interpretation base (S.signature schema);
  field_sort_is_scalar: not (V.datatype_sort (S.signature schema) (ff_sort p));
  project: V.tree base -> int;
  project_range:
    v:V.tree base ->
    Lemma (requires V.has_sort (S.signature schema) (ff_sort p) v)
          (ensures 0 <= project v /\ project v < p);
  project_reflection:
    x:V.tree base -> y:V.tree base ->
    Lemma (requires V.has_sort (S.signature schema) (ff_sort p) x /\
                     V.has_sort (S.signature schema) (ff_sort p) y)
          (ensures (x == y <==> project x == project y));
  field_application:
    f:func_decl -> V.arguments base (S.signature schema) f.domain ->
    GTot (V.value base (S.signature schema) f.range);
  numeral_law:
    f:func_decl -> n:int ->
    Lemma (requires numeral (App f []) == Some (p, n))
          (ensures project (field_application f []) == n);
  operation_law:
    f:func_decl -> xs:V.arguments base (S.signature schema) f.domain ->
    op:decl_kind ->
    Lemma (requires operation_of f == Some (p, op))
          (ensures project (field_application f xs) ==
                   calculate p op (projections project xs))
}

let application (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                (m:model base schema p) (f:func_decl)
                (xs:V.arguments base (S.signature schema) f.domain)
  : GTot (V.value base (S.signature schema) f.range) =
  match numeral (App f []) with
  | Some (q, _) -> if q = p then m.field_application f xs else m.other.application f xs
  | None ->
    (match operation_of f with
     | Some (q, _) -> if q = p then m.field_application f xs else m.other.application f xs
     | None -> m.other.application f xs)

let override (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
             (m:model base schema p)
  : V.interpretation base (S.signature schema) = {
  application = application schema p m;
  quantification = m.other.quantification;
}

#push-options "--fuel 4 --ifuel 2"
let rec lemma_not_registered (sigma:V.signature) (f:func_decl)
  : Lemma (requires not (V.datatype_sort sigma f.range))
          (ensures not (L.mem f sigma))
          (decreases sigma) =
  match sigma with
  | [] -> ()
  | g :: rest ->
    if f = g then (
      assert (V.datatype_sort (g :: rest) f.range);
      assert (not (V.datatype_sort sigma f.range)))
    else lemma_not_registered rest f

let rec lemma_no_recognizer (f:func_decl) (cs:list S.constructor_case)
  : Lemma (requires f.range <> bool_sort)
          (ensures not (Some? (S.find_recognizer f cs)))
          (decreases cs) =
  match cs with
  | [] -> ()
  | _ :: rest ->
    lemma_no_recognizer f rest;
    assert_norm (Some? (S.find_recognizer f cs) == Some? (S.find_recognizer f rest))

let rec lemma_no_accessor (f:func_decl) (cs:list S.constructor_case)
  : Lemma (requires f.interp <> Some DT.op_accessor)
          (ensures not (Some? (S.find_accessor f cs)))
          (decreases cs) =
  match cs with
  | [] -> ()
  | _ :: rest ->
    lemma_no_accessor f rest;
    assert_norm (Some? (S.find_accessor f cs) == Some? (S.find_accessor f rest))

let lemma_application_dispatch (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                               (m:model base schema p) (f:func_decl)
                               (xs:V.arguments base (S.signature schema) f.domain)
                               (op:decl_kind)
  : Lemma (requires operation_of f == Some (p, op))
          (ensures SS.application schema m.booleans m.scalar_model
                    (override schema p m) f xs == m.field_application f xs)
  = assert (f.range == ff_sort p);
    lemma_not_registered (S.signature schema) f;
    lemma_no_recognizer f schema.cases;
    assert (f.interp <> Some DT.op_accessor);
    lemma_no_accessor f schema.cases
#pop-options

let lemma_numeral_dispatch (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                           (m:model base schema p) (f:func_decl) (n:int)
  : Lemma (requires numeral (App f []) == Some (p, n))
          (ensures SS.application schema m.booleans m.scalar_model
                    (override schema p m) f [] == m.field_application f [])
  = assert (f.range == ff_sort p);
    lemma_not_registered (S.signature schema) f;
    lemma_no_recognizer f schema.cases;
    assert (f.interp <> Some DT.op_accessor);
    lemma_no_accessor f schema.cases

let interpretation (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                   (m:model base schema p)
  : V.interpretation base (S.signature schema) =
  SS.interpretation schema m.booleans m.scalar_model (override schema p m)

let empty_environment (#base:sort -> Type0) (schema:S.checked_schema)
  : V.environment base (S.signature schema) [] =
  SS.empty_environment (S.signature schema)

let evaluate_at (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                (m:model base schema p)
                (scope:list sort)
                (rho:V.environment base (S.signature schema) scope)
                (e:expr{D.scoped scope e})
  : GTot (V.value base (S.signature schema) (get_sort e)) =
  V.evaluate (S.signature schema) (interpretation schema p m) scope rho e

#push-options "--fuel 3 --ifuel 2"
let lemma_evaluate_operation_at (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                               (m:model base schema p) (scope:list sort)
                               (rho:V.environment base (S.signature schema) scope)
                               (f:func_decl) (args:list expr) (op:decl_kind)
  : Lemma (requires D.scoped scope (App f args) /\
                    operation_of f == Some (p, op))
          (ensures m.project
                     (evaluate_at schema p m scope rho (App f args)) ==
                   calculate p op
                     (projections m.project
                       (V.evaluate_args (S.signature schema)
                         (interpretation schema p m) scope rho args f.domain)))
  = let xs = V.evaluate_args (S.signature schema)
               (interpretation schema p m) scope rho args f.domain in
    lemma_not_registered (S.signature schema) f;
    lemma_application_dispatch schema p m f xs op;
    assert (evaluate_at schema p m scope rho (App f args) ==
            SS.application schema m.booleans m.scalar_model (override schema p m) f xs);
    m.operation_law f xs op

let lemma_evaluate_numeral_at (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                             (m:model base schema p) (scope:list sort)
                             (rho:V.environment base (S.signature schema) scope)
                             (f:func_decl) (n:int)
  : Lemma (requires D.scoped scope (App f []) /\
                    numeral (App f []) == Some (p, n))
          (ensures m.project (evaluate_at schema p m scope rho (App f [])) == n)
  = let xs = V.evaluate_args (S.signature schema)
               (interpretation schema p m) scope rho [] f.domain in
    lemma_not_registered (S.signature schema) f;
    lemma_numeral_dispatch schema p m f n;
    assert (evaluate_at schema p m scope rho (App f []) ==
            SS.application schema m.booleans m.scalar_model (override schema p m) f xs);
    m.numeral_law f n
#pop-options

let evaluate (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
             (m:model base schema p)
             (e:expr{D.scoped [] e})
  : GTot (V.value base (S.signature schema) (get_sort e)) =
  evaluate_at schema p m [] (empty_environment schema) e

unfold let truth_at (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
             (m:model base schema p)
             (scope:list sort) (rho:V.environment base (S.signature schema) scope)
             (e:expr) : GTot bool =
  SS.truth_at schema m.booleans m.scalar_model (override schema p m) scope rho e

let truth (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
          (m:model base schema p)
          (e:expr) : GTot bool =
  SS.truth schema m.booleans m.scalar_model (override schema p m) e

let residue (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
            (m:model base schema p)
            (rho:V.environment base (S.signature schema) [])
            (e:expr{D.scoped [] e}) : GTot int =
  m.project (evaluate_at schema p m [] rho e)

let rec expressions_residues (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                             (m:model base schema p)
                             (rho:V.environment base (S.signature schema) [])
                             (args:list expr{D.scoped_args [] args})
                             : GTot (list int) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> residue schema p m rho a :: expressions_residues schema p m rho rest

let valuation (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
              (m:model base schema p)
              (rho:V.environment base (S.signature schema) [])
              (tbl:list expr{D.scoped_args [] tbl}) : GTot (nat -> int) =
  let values = expressions_residues schema p m rho tbl in
  fun k -> if k < L.length values then L.index values k else 0

let rec lemma_index_of (e:expr) (tbl:list expr) (k:nat)
  : Lemma (requires index_of e tbl == Some k)
          (ensures k < L.length tbl /\ L.index tbl k == e)
          (decreases tbl) =
  match tbl with
  | [] -> ()
  | x :: rest ->
    if x = e then ()
    else
      (match index_of e rest with
       | Some j -> lemma_index_of e rest j
       | None -> ())

let rec prefix (a b:list expr) : Tot bool (decreases a) =
  match a, b with
  | [], _ -> true
  | x :: a', y :: b' -> x = y && prefix a' b'
  | _, _ -> false

let rec lemma_prefix_refl (a:list expr)
  : Lemma (ensures prefix a a) (decreases a) =
  match a with [] -> () | _ :: rest -> lemma_prefix_refl rest

let rec lemma_prefix_trans (a b c:list expr)
  : Lemma (requires prefix a b /\ prefix b c) (ensures prefix a c)
          (decreases a) =
  match a, b, c with
  | _ :: a', _ :: b', _ :: c' -> lemma_prefix_trans a' b' c'
  | _, _, _ -> ()

let rec lemma_prefix_append (a:list expr) (t:expr)
  : Lemma (ensures prefix a (L.append a [t])) (decreases a) =
  match a with [] -> () | _ :: rest -> lemma_prefix_append rest t

let rec lemma_scoped_append_single (xs:list expr) (t:expr)
  : Lemma (requires D.scoped_args [] xs /\ D.scoped [] t)
          (ensures D.scoped_args [] (L.append xs [t]))
          (decreases xs) =
  match xs with
  | [] -> ()
  | _ :: rest -> lemma_scoped_append_single rest t

let lemma_allocate_scoped (st:encoding) (t:expr) (st':encoding)
  : Lemma (requires allocate st t == Some st' /\
                    D.scoped_args [] st.terms /\ D.scoped [] t)
          (ensures D.scoped_args [] st'.terms) =
  assert (st'.terms == L.append st.terms [t]);
  lemma_scoped_append_single st.terms t

let rec lemma_visit_scoped (p:int) (st:encoding) (t:expr) (st':encoding)
  : Lemma (requires D.scoped_args [] st.terms /\ D.scoped [] t /\
                    visit p st t == Some st')
          (ensures D.scoped_args [] st'.terms)
          (decreases t) =
  match numeral t with
  | Some (q, _) -> ()
  | None ->
    if Some? (index_of t st.terms) then ()
    else if get_sort t <> ff_sort p then ()
    else
      match t with
      | App f args ->
        (match operation_at f args with
         | Some (q, op) ->
           let st1 = Some?.v (visit_args p st args) in
           let st2 = Some?.v (define st1 t
                     (Some?.v (combine op
                       (Some?.v (term_polys p st1.terms args))))) in
           let st_alloc = Some?.v (allocate st1 t) in
           assert (st2.terms == st_alloc.terms);
           assert (D.scoped_args [] args);
           lemma_visit_args_scoped p st args st1;
           lemma_allocate_scoped st1 t st_alloc
         | None -> lemma_allocate_scoped st t st')
      | _ -> lemma_allocate_scoped st t st'

and lemma_visit_args_scoped (p:int) (st:encoding) (args:list expr) (st':encoding)
  : Lemma (requires D.scoped_args [] st.terms /\ D.scoped_args [] args /\
                    visit_args p st args == Some st')
          (ensures D.scoped_args [] st'.terms)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    let st1 = Some?.v (visit_args p st rest) in
    lemma_visit_args_scoped p st rest st1;
    lemma_visit_scoped p st1 a st'

let rec lemma_prefix_index (a b:list expr) (k:nat)
  : Lemma (requires prefix a b /\ k < L.length a)
          (ensures k < L.length b /\ L.index b k == L.index a k)
          (decreases a) =
  match a, b with
  | _ :: a', _ :: b' -> if k = 0 then () else lemma_prefix_index a' b' (k - 1)

let rec lemma_append_last (a:list expr) (t:expr)
  : Lemma (ensures L.length (L.append a [t]) == L.length a + 1 /\
                   L.index (L.append a [t]) (L.length a) == t)
          (decreases a) =
  match a with [] -> () | _ :: rest -> lemma_append_last rest t

let rec lemma_scoped_args_index (args:list expr) (k:nat)
  : Lemma (requires D.scoped_args [] args /\ k < L.length args)
          (ensures D.scoped [] (L.index args k))
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: rest -> if k = 0 then () else lemma_scoped_args_index rest (k - 1)

let rec lemma_expressions_residues_length (#base:sort -> Type0)
                                          (schema:S.checked_schema) (p:pos)
                                          (m:model base schema p)
                                          (rho:V.environment base (S.signature schema) [])
                                          (args:list expr{D.scoped_args [] args})
  : Lemma (ensures L.length (expressions_residues schema p m rho args) == L.length args)
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: rest -> lemma_expressions_residues_length schema p m rho rest

let rec lemma_expressions_residues_index (#base:sort -> Type0)
                                         (schema:S.checked_schema) (p:pos)
                                         (m:model base schema p)
                                         (rho:V.environment base (S.signature schema) [])
                                         (args:list expr{D.scoped_args [] args}) (k:nat)
  : Lemma (requires k < L.length args /\
                    k < L.length (expressions_residues schema p m rho args) /\
                    D.scoped [] (L.index args k))
          (ensures L.index (expressions_residues schema p m rho args) k ==
                   residue schema p m rho (L.index args k))
          (decreases args) =
  lemma_expressions_residues_length schema p m rho args;
  assert (k < L.length (expressions_residues schema p m rho args));
  lemma_scoped_args_index args k;
  match args with
  | [] -> ()
  | _ :: rest ->
    if k = 0 then ()
    else (
      assert (k - 1 < L.length rest);
      lemma_scoped_args_index rest (k - 1);
      lemma_expressions_residues_length schema p m rho rest;
      assert (k - 1 < L.length (expressions_residues schema p m rho rest));
      lemma_expressions_residues_index schema p m rho rest (k - 1))

let lemma_valuation_index (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                          (m:model base schema p)
                          (rho:V.environment base (S.signature schema) [])
                          (tbl:list expr{D.scoped_args [] tbl}) (k:nat)
  : Lemma (requires k < L.length tbl /\ D.scoped [] (L.index tbl k))
          (ensures valuation schema p m rho tbl k ==
                   residue schema p m rho (L.index tbl k)) =
  lemma_expressions_residues_length schema p m rho tbl;
  lemma_scoped_args_index tbl k;
  assert (k < L.length (expressions_residues schema p m rho tbl));
  lemma_expressions_residues_index schema p m rho tbl k;
  assert (valuation schema p m rho tbl k ==
          L.index (expressions_residues schema p m rho tbl) k);
  assert (L.index (expressions_residues schema p m rho tbl) k ==
          residue schema p m rho (L.index tbl k))

let lemma_same_mod_diff (p:pos) (x y:int)
  : Lemma (requires x % p == y % p)
          (ensures (x - y) % p == 0) =
  M.euclidean_division_definition x p;
  M.euclidean_division_definition y p;
  M.distributivity_sub_left (x / p) (y / p) p;
  M.cancel_mul_mod (x / p - y / p) p

let lemma_truth_field_eq (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                         (m:model base schema p)
                         (rho:V.environment base (S.signature schema) [])
                         (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\
                    get_sort a == ff_sort p /\ get_sort b == ff_sort p)
          (ensures SS.truth_at schema m.booleans m.scalar_model (override schema p m) [] rho
                     (R.mk_eq_expr a b) ==
                   (residue schema p m rho a == residue schema p m rho b))
  = SS.lemma_equality_at schema m.booleans m.scalar_model (override schema p m) [] rho a b;
    m.project_reflection
      (evaluate_at schema p m [] rho a) (evaluate_at schema p m [] rho b)

let lemma_truth_positive_premise (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                                 (m:model base schema p)
                                 (rho:V.environment base (S.signature schema) [])
                                 (l a b:expr)
  : Lemma (requires D.scoped [] l /\ eq_parts l == Some (a, b) /\
                    D.scoped [] a /\ D.scoped [] b /\ l == R.mk_eq_expr a b /\
                    get_sort a == ff_sort p /\ get_sort b == ff_sort p)
          (ensures (SS.truth_at schema m.booleans m.scalar_model (override schema p m) [] rho l ==>
                    residue schema p m rho a == residue schema p m rho b))
  = lemma_truth_field_eq schema p m rho a b

#push-options "--fuel 8 --ifuel 4"
let lemma_nary_at (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                  (m:model base schema p)
                  (rho:V.environment base (S.signature schema) [])
                  (f:func_decl) (args:list expr) (op:B.nary_op)
  : Lemma (requires D.scoped [] (App f args) /\ SS.classify f == SS.Nary op)
          (ensures SS.truth_at schema m.booleans m.scalar_model
                     (override schema p m) [] rho (App f args) ==
                   B.geval_args
                     (SS.truth_at schema m.booleans m.scalar_model
                       (override schema p m) [] rho)
                     op (L.map B.Atom args)) =
  let xs = SS.evaluate_arguments_at schema m.booleans m.scalar_model
             (override schema p m) [] rho args f.domain in
  SS.lemma_evaluate_core_at schema m.booleans m.scalar_model (override schema p m)
    [] rho f args;
  assert (SS.truth_at schema m.booleans m.scalar_model (override schema p m) [] rho (App f args) ==
          SS.truth_value schema m.booleans
            (SS.application schema m.booleans m.scalar_model (override schema p m) f xs));
  assert (SS.truth_value schema m.booleans
            (SS.application schema m.booleans m.scalar_model (override schema p m) f xs) ==
          SS.combine op (SS.boolean_values schema m.booleans f.domain xs));
  SS.lemma_boolean_arguments_at schema m.booleans m.scalar_model (override schema p m)
    [] rho args f.domain op

let lemma_negation_at (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                      (m:model base schema p)
                      (rho:V.environment base (S.signature schema) [])
                      (f:func_decl) (arg:expr)
  : Lemma (requires D.scoped [] (App f [arg]) /\ SS.classify f == SS.Negation)
          (ensures SS.truth_at schema m.booleans m.scalar_model (override schema p m) [] rho
                     (App f [arg]) ==
                   not (SS.truth_at schema m.booleans m.scalar_model (override schema p m) [] rho arg)) =
  SS.lemma_evaluate_core_at schema m.booleans m.scalar_model (override schema p m)
    [] rho f [arg];
  V.lemma_sort_eq (get_sort arg) bool_sort
#pop-options

let rec none_true (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                  (m:model base schema p)
                  (rho:V.environment base (S.signature schema) [])
                  (lits:list expr) : Tot prop (decreases lits) =
  match lits with
  | [] -> True
  | l :: rest ->
    not (SS.truth_at schema m.booleans m.scalar_model (override schema p m) [] rho l) /\
    none_true schema p m rho rest

#push-options "--fuel 8 --ifuel 4"
let rec lemma_negated_in (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                         (m:model base schema p)
                         (rho:V.environment base (S.signature schema) [])
                         (l:expr) (lits:list expr)
  : Lemma (requires D.scoped_args [] lits /\
                    none_true schema p m rho lits /\ negated_in l lits)
          (ensures SS.truth_at schema m.booleans m.scalar_model
                     (override schema p m) [] rho l)
          (decreases lits) =
  match lits with
  | [] -> ()
  | x :: rest ->
    if PT.is_not x == Some l then
      (match x with
       | App f [a] ->
         assert (a == l);
         assert (C.canonical_not f);
         assert (SS.classify f == SS.Negation);
         lemma_negation_at schema p m rho f a;
         assert (not (SS.truth_at schema m.booleans m.scalar_model
                       (override schema p m) [] rho (App f [a])));
         assert (SS.truth_at schema m.booleans m.scalar_model
                  (override schema p m) [] rho (App f [a]) ==
                not (SS.truth_at schema m.booleans m.scalar_model
                  (override schema p m) [] rho a));
         assert (SS.truth_at schema m.booleans m.scalar_model
                  (override schema p m) [] rho a)
       | _ -> ())
    else lemma_negated_in schema p m rho l rest

let rec lemma_or_false_args (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                            (m:model base schema p)
                            (rho:V.environment base (S.signature schema) [])
                            (args:list expr)
  : Lemma (requires not (B.geval_args
                    (SS.truth_at schema m.booleans m.scalar_model
                       (override schema p m) [] rho)
                    B.Or (L.map B.Atom args)))
          (ensures none_true schema p m rho args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    assert (B.geval_args
              (SS.truth_at schema m.booleans m.scalar_model
                 (override schema p m) [] rho)
              B.Or (L.map B.Atom (a :: rest)) ==
            (SS.truth_at schema m.booleans m.scalar_model
               (override schema p m) [] rho a ||
             B.geval_args
               (SS.truth_at schema m.booleans m.scalar_model
                 (override schema p m) [] rho)
               B.Or (L.map B.Atom rest)));
    assert (not (SS.truth_at schema m.booleans m.scalar_model
                  (override schema p m) [] rho a));
    assert (not (B.geval_args
                  (SS.truth_at schema m.booleans m.scalar_model
                    (override schema p m) [] rho)
                  B.Or (L.map B.Atom rest)));
    lemma_or_false_args schema p m rho rest

let rec lemma_boolean_sorts_agree (dom:list sort)
  : Lemma (C.boolean_sorts dom == SS.boolean_sorts dom) (decreases dom) =
  match dom with
  | [] -> ()
  | _ :: rest -> lemma_boolean_sorts_agree rest

let lemma_canonical_or_classified (f:func_decl)
  : Lemma (requires C.canonical_or f)
          (ensures SS.classify f == SS.Nary B.Or) =
  assert (f.decl_name == "or");
  assert (f.interp == Some op_or);
  assert (C.boolean_sorts f.domain);
  lemma_boolean_sorts_agree f.domain;
  assert (SS.boolean_sorts f.domain);
  assert (f.range == bool_sort);
  assert (f.int_params == [])

let lemma_canonical_and_classified (f:func_decl)
  : Lemma (requires C.canonical_and f)
          (ensures SS.classify f == SS.Nary B.And) =
  assert (f.decl_name == "and");
  assert (f.interp == Some op_and);
  assert (C.boolean_sorts f.domain);
  lemma_boolean_sorts_agree f.domain;
  assert (SS.boolean_sorts f.domain);
  assert (f.range == bool_sort);
  assert (f.int_params == [])

let lemma_clause_false_literals (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                               (m:model base schema p)
                               (rho:V.environment base (S.signature schema) [])
                               (e:expr)
  : Lemma (requires D.scoped [] e /\ get_sort e == bool_sort /\
                    not (SS.truth_at schema m.booleans m.scalar_model
                           (override schema p m) [] rho e))
          (ensures none_true schema p m rho (clause_literals e)) =
  match e with
  | App f args ->
    if C.canonical_or f then
      (lemma_canonical_or_classified f;
       lemma_nary_at schema p m rho f args B.Or;
       lemma_or_false_args schema p m rho args)
    else assert (none_true schema p m rho [e])
  | _ -> assert (none_true schema p m rho [e])
#pop-options

let eq_ok (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
          (m:model base schema p)
          (rho:V.environment base (S.signature schema) [])
          (v:nat -> int) (e:equation) : prop =
  match e with
  | (q, Definition) -> peval v q % p == 0
  | (q, Premise _ l) ->
    get_sort l == bool_sort /\
    (SS.truth_at schema m.booleans m.scalar_model (override schema p m) [] rho l ==>
     peval v q % p == 0)
  | (_, Witness) -> True

let rec eqs_ok (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
               (m:model base schema p)
               (rho:V.environment base (S.signature schema) [])
               (v:nat -> int) (es:list equation) : Tot prop (decreases es) =
  match es with
  | [] -> True
  | e :: rest -> eq_ok schema p m rho v e /\ eqs_ok schema p m rho v rest

let lemma_term_poly (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                        (m:model base schema p)
                        (rho:V.environment base (S.signature schema) [])
                        (tbl final:list expr) (t:expr) (q:poly)
  : Lemma (requires D.scoped [] t /\ get_sort t == ff_sort p /\
                    D.scoped_args [] final /\ prefix tbl final /\
                    term_poly p tbl t == Some q)
          (ensures peval (valuation schema p m rho final) q % p ==
                   residue schema p m rho t)
  = let v = valuation schema p m rho final in
    match numeral t with
    | Some (qmod, n) ->
      assert (qmod == p);
      lemma_evaluate_numeral_at schema p m [] rho
        (match t with App f [] -> f | _ -> FStar.Pervasives.false_elim ()) n;
      lemma_peval_constant v n;
      M.small_mod n p
    | None ->
      let k = Some?.v (index_of t tbl) in
      lemma_index_of t tbl k;
      lemma_prefix_index tbl final k;
      lemma_scoped_args_index final k;
      lemma_valuation_index schema p m rho final k;
      lemma_peval_variable v k;
      m.project_range (evaluate_at schema p m [] rho (L.index final k));
      M.small_mod (residue schema p m rho t) p

let rec lemma_term_polys (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                         (m:model base schema p)
                         (rho:V.environment base (S.signature schema) [])
                         (tbl final:list expr) (args:list expr) (qs:list poly)
  : Lemma (requires D.scoped_args [] args /\
                    args_have_sort p args /\
                    D.scoped_args [] final /\ prefix tbl final /\
                    term_polys p tbl args == Some qs)
          (ensures match_list (valuation schema p m rho final) p qs
                   (expressions_residues schema p m rho args))
          (decreases args) =
  match args, qs with
  | a :: rest, q :: qs' ->
    assert (sort_eq (get_sort a) (ff_sort p));
    V.lemma_sort_eq (get_sort a) (ff_sort p);
    lemma_term_poly schema p m rho tbl final a q;
    lemma_term_polys schema p m rho tbl final rest qs'
  | _, _ -> ()

let rec lemma_residues_args (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                            (m:model base schema p)
                            (rho:V.environment base (S.signature schema) [])
                            (args:list expr{D.scoped_args [] args})
                            (dom:list sort{sorts_match args dom})
  : Lemma (expressions_residues schema p m rho args ==
           projections m.project
             (V.evaluate_args (S.signature schema) (interpretation schema p m)
                              [] rho args dom))
          (decreases args) =
  match args, dom with
  | e :: rest, _ :: tail ->
    V.lemma_sort_eq (get_sort e) (L.hd dom);
    lemma_residues_args schema p m rho rest tail
  | _, _ -> ()

let lemma_definition (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                     (m:model base schema p)
                     (rho:V.environment base (S.signature schema) [])
                     (tbl final:list expr) (f:func_decl) (args:list expr)
                     (op:decl_kind) (qs:list poly) (fq:poly)
  : Lemma (requires D.scoped [] (App f args) /\
                    operation_at f args == Some (p, op) /\
                    D.scoped_args [] final /\
                    prefix tbl final /\
                    L.length tbl < L.length final /\
                    L.index final (L.length tbl) == App f args /\
                    term_polys p tbl args == Some qs /\ combine op qs == Some fq)
          (ensures peval (valuation schema p m rho final)
                    (definition (L.length tbl) fq) % p == 0)
  = let v = valuation schema p m rho final in
    let k = L.length tbl in
    let t = App f args in
    let qxs = expressions_residues schema p m rho args in
    let appxs = V.evaluate_args (S.signature schema)
                  (interpretation schema p m) [] rho args f.domain in
    assert (args_have_sort p args);
    assert (operation_of f == Some (p, op));
    lemma_term_polys schema p m rho tbl final args qs;
    lemma_residues_args schema p m rho args f.domain;
    lemma_evaluate_operation_at schema p m [] rho f args op;
    lemma_combine v p op qs qxs fq;
    lemma_valuation_index schema p m rho final k;
    lemma_peval_variable v k;
    lemma_pscale v (-1) fq;
    lemma_padd v [([k], 1)] (pscale (-1) fq);
    lemma_same_mod_diff p
      (residue schema p m rho t) (peval v fq)

let lemma_eqs_prepend (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                     (m:model base schema p)
                     (rho:V.environment base (S.signature schema) [])
                     (v:nat -> int) (e:equation) (es:list equation)
  : Lemma (ensures eqs_ok schema p m rho v (e :: es) ==
                    (eq_ok schema p m rho v e /\ eqs_ok schema p m rho v es)) = ()

let rec lemma_visit (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                    (m:model base schema p)
                    (rho:V.environment base (S.signature schema) [])
                    (st:encoding) (t:expr) (st':encoding) (final:list expr)
  : Lemma (requires p >= 2 /\ D.scoped_args [] st.terms /\ D.scoped [] t /\
                    D.scoped_args [] final /\ visit p st t == Some st' /\
                    prefix st'.terms final)
          (ensures prefix st.terms st'.terms /\
                   (eqs_ok schema p m rho (valuation schema p m rho final) st.equations ==>
                    eqs_ok schema p m rho (valuation schema p m rho final) st'.equations))
          (decreases t) =
  match numeral t with
  | Some (q, _) -> lemma_prefix_refl st.terms
  | None ->
    if Some? (index_of t st.terms) then lemma_prefix_refl st.terms
    else
      match t with
      | App f args ->
        (match operation_at f args with
         | Some (q, op) ->
           let st1 = Some?.v (visit_args p st args) in
           let qs = Some?.v (term_polys p st1.terms args) in
           let fq = Some?.v (combine op qs) in
           let st2 = Some?.v (define st1 t fq) in
           let k = L.length st1.terms in
           assert (q == p);
           lemma_visit_args_scoped p st args st1;
           lemma_prefix_append st1.terms t;
           lemma_append_last st1.terms t;
           assert (st2.terms == L.append st1.terms [t]);
           assert (st2.equations == (definition k fq, Definition) :: st1.equations);
           assert (st' == st2);
           lemma_prefix_trans st1.terms st2.terms final;
           lemma_prefix_index st2.terms final k;
           lemma_visit_args schema p m rho st args st1 final;
           lemma_prefix_trans st.terms st1.terms st2.terms;
           lemma_definition schema p m rho st1.terms final f args op qs fq;
           lemma_eqs_prepend schema p m rho
             (valuation schema p m rho final) (definition k fq, Definition) st1.equations;
           assert (prefix st.terms st'.terms);
           assert (eqs_ok schema p m rho (valuation schema p m rho final) st.equations ==>
                   eqs_ok schema p m rho (valuation schema p m rho final) st'.equations)
         | None ->
           lemma_prefix_append st.terms t;
           assert (st'.terms == L.append st.terms [t]);
           assert (st'.equations == st.equations);
           assert (prefix st.terms st'.terms))
      | _ ->
        lemma_prefix_append st.terms t;
        assert (st'.terms == L.append st.terms [t]);
        assert (st'.equations == st.equations);
        assert (prefix st.terms st'.terms)

and lemma_visit_args (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                     (m:model base schema p)
                     (rho:V.environment base (S.signature schema) [])
                     (st:encoding) (args:list expr) (st':encoding) (final:list expr)
  : Lemma (requires p >= 2 /\ D.scoped_args [] st.terms /\ D.scoped_args [] args /\
                    D.scoped_args [] final /\ visit_args p st args == Some st' /\
                    prefix st'.terms final)
          (ensures prefix st.terms st'.terms /\
                   (eqs_ok schema p m rho (valuation schema p m rho final) st.equations ==>
                    eqs_ok schema p m rho (valuation schema p m rho final) st'.equations))
          (decreases args) =
  match args with
  | [] -> lemma_prefix_refl st.terms
  | a :: rest ->
    let st1 = Some?.v (visit_args p st rest) in
    lemma_visit_args_scoped p st rest st1;
    lemma_visit schema p m rho st1 a st' final;
    lemma_prefix_trans st1.terms st'.terms final;
    lemma_visit_args schema p m rho st rest st1 final;
    lemma_prefix_trans st.terms st1.terms st'.terms;
    assert (prefix st.terms st'.terms)

#push-options "--fuel 6 --ifuel 3"
let lemma_eq_parts_normalized (e a b:expr)
  : Lemma (requires eq_parts e == Some (a, b))
          (ensures e == R.mk_eq_expr a b) =
  match e with
  | App f [x; y] ->
    assert (x == a /\ y == b);
    assert (f == R.eq_decl (get_sort x));
    assert (get_sort x == get_sort y);
    assert (e == R.mk_eq_expr a b)
  | _ -> ()

let lemma_premise_parts_wf (p:int) (l:expr) (positive:bool) (a b:expr)
  : Lemma (requires premise_parts p l == Some (positive, a, b))
          (ensures D.scoped [] a /\ D.scoped [] b /\
                   get_sort a == ff_sort p /\ get_sort b == ff_sort p /\
                   get_sort l == bool_sort /\
                   (positive ==> l == R.mk_eq_expr a b)) =
  match PT.is_not l with
  | Some atom ->
    assert (not positive);
    assert (eq_parts atom == Some (a, b));
    lemma_eq_parts_normalized atom a b;
    assert (D.scoped [] a /\ D.scoped [] b);
    assert (get_sort a == ff_sort p /\ get_sort b == ff_sort p);
    assert (get_sort l == bool_sort)
  | None ->
    assert positive;
    match l with
    | App f [x; y] ->
      assert (x == a /\ y == b);
      lemma_eq_parts_normalized l a b;
      assert (f == R.eq_decl (get_sort x));
      assert (D.scoped [] x /\ D.scoped [] y);
      assert (get_sort x == ff_sort p /\ get_sort y == ff_sort p);
      assert (D.scoped [] a /\ D.scoped [] b);
      assert (get_sort a == ff_sort p /\ get_sort b == ff_sort p);
      assert (get_sort l == bool_sort);
      assert (l == R.mk_eq_expr a b)
    | _ -> ()
#pop-options

let lemma_premise_equation (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                           (m:model base schema p)
                           (rho:V.environment base (S.signature schema) [])
                           (k:nat) (l a b:expr) (st st':encoding)
                           (positive:bool) (final:list expr)
  : Lemma (requires p >= 2 /\ D.scoped_args [] st.terms /\
                    D.scoped_args [] final /\ D.scoped [] l /\
                    premise_parts p l == Some (positive, a, b) /\
                    premise_equation p k l a b st positive == Some st' /\
                    prefix st'.terms final)
          (ensures prefix st.terms st'.terms /\
                   (eqs_ok schema p m rho (valuation schema p m rho final) st.equations ==>
                    eqs_ok schema p m rho (valuation schema p m rho final) st'.equations)) =
  if positive then (
    lemma_premise_parts_wf p l positive a b;
    let qa = Some?.v (term_poly p st.terms a) in
    let qb = Some?.v (term_poly p st.terms b) in
    let q = padd qa (pscale (-1) qb) in
    assert (st'.terms == st.terms);
    assert (st'.equations == (q, Premise k l) :: st.equations);
    lemma_prefix_refl st.terms;
    assert (prefix st.terms st'.terms);
    assert (prefix st.terms final);
    let aux () : Lemma
        (requires SS.truth_at schema m.booleans m.scalar_model
                    (override schema p m) [] rho l)
        (ensures peval (valuation schema p m rho final) q % p == 0) =
      lemma_term_poly schema p m rho st.terms final a qa;
      lemma_term_poly schema p m rho st.terms final b qb;
      lemma_truth_positive_premise schema p m rho l a b;
      lemma_pscale (valuation schema p m rho final) (-1) qb;
      lemma_padd (valuation schema p m rho final) qa
        (pscale (-1) qb);
      lemma_same_mod_diff p
        (peval (valuation schema p m rho final) qa)
        (peval (valuation schema p m rho final) qb) in
    FStar.Classical.move_requires aux ();
    lemma_eqs_prepend schema p m rho (valuation schema p m rho final)
      (q, Premise k l) st.equations;
    assert (eqs_ok schema p m rho (valuation schema p m rho final) st.equations ==>
            eqs_ok schema p m rho (valuation schema p m rho final) st'.equations))
  else (
    assert (st'.terms == L.append st.terms [l]);
    assert (st'.equations == ([], Witness) :: st.equations);
    lemma_prefix_append st.terms l;
    lemma_eqs_prepend schema p m rho (valuation schema p m rho final)
      ([], Witness) st.equations;
    assert (prefix st.terms st'.terms);
    assert (eqs_ok schema p m rho (valuation schema p m rho final) st.equations ==>
            eqs_ok schema p m rho (valuation schema p m rho final) st'.equations))

let rec lemma_bind_scoped (p:int) (k:nat) (st:encoding) (ps:list expr) (st':encoding)
  : Lemma (requires D.scoped_args [] st.terms /\ D.scoped_args [] ps /\
                    bind p k st ps == Some st')
          (ensures D.scoped_args [] st'.terms)
          (decreases ps) =
  match ps with
  | [] -> ()
  | l :: rest ->
    let (positive, a, b) = Some?.v (premise_parts p l) in
    lemma_premise_parts_wf p l positive a b;
    let st1 = Some?.v (visit p st a) in
    let st2 = Some?.v (visit p st1 b) in
    let st3 = Some?.v (premise_equation p k l a b st2 positive) in
    lemma_visit_scoped p st a st1;
    lemma_visit_scoped p st1 b st2;
    if positive then assert (st3.terms == st2.terms)
    else (
      assert (st3.terms == L.append st2.terms [l]);
      lemma_scoped_append_single st2.terms l);
    lemma_bind_scoped p (k + 1) st3 rest st'

let rec lemma_bind (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                   (m:model base schema p)
                   (rho:V.environment base (S.signature schema) [])
                   (k:nat) (st:encoding) (ps:list expr) (st':encoding) (final:list expr)
  : Lemma (requires p >= 2 /\ D.scoped_args [] st.terms /\ D.scoped_args [] ps /\
                    D.scoped_args [] final /\ bind p k st ps == Some st' /\
                    prefix st'.terms final)
          (ensures prefix st.terms st'.terms /\
                   (eqs_ok schema p m rho (valuation schema p m rho final) st.equations ==>
                    eqs_ok schema p m rho (valuation schema p m rho final) st'.equations))
          (decreases ps) =
  match ps with
  | [] -> lemma_prefix_refl st.terms
  | l :: rest ->
    let (positive, a, b) = Some?.v (premise_parts p l) in
    let st1 = Some?.v (visit p st a) in
    let st2 = Some?.v (visit p st1 b) in
    let st3 = Some?.v (premise_equation p k l a b st2 positive) in
    lemma_bind_scoped p k st (l :: rest) st';
    lemma_premise_parts_wf p l positive a b;
    lemma_visit_scoped p st a st1;
    lemma_visit_scoped p st1 b st2;
    if positive then assert (st3.terms == st2.terms)
    else (
      assert (st3.terms == L.append st2.terms [l]);
      lemma_scoped_append_single st2.terms l);
    lemma_bind schema p m rho (k + 1) st3 rest st' final;
    lemma_prefix_trans st3.terms st'.terms final;
    lemma_premise_equation schema p m rho k l a b st2 st3 positive final;
    lemma_prefix_trans st2.terms st3.terms final;
    lemma_visit schema p m rho st1 b st2 final;
    lemma_prefix_trans st1.terms st2.terms final;
    lemma_visit schema p m rho st a st1 final;
    lemma_prefix_trans st.terms st1.terms st2.terms;
    lemma_prefix_trans st.terms st2.terms st3.terms;
    lemma_prefix_trans st.terms st3.terms st'.terms;
    assert (prefix st.terms st'.terms)

let tree_ok (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
            (m:model base schema p)
            (rho:V.environment base (S.signature schema) [])
            (v:nat -> int) (tree:IX.index_tree equation) : prop =
  forall (j:nat).
    match IX.index_get tree j with
    | Some e -> eq_ok schema p m rho v e
    | None -> True

let rec lemma_index_equations (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                              (m:model base schema p)
                              (rho:V.environment base (S.signature schema) [])
                              (v:nat -> int) (tree:IX.index_tree equation)
                              (k:int) (es:list equation)
  : Lemma (requires tree_ok schema p m rho v tree /\
                    eqs_ok schema p m rho v es)
          (ensures tree_ok schema p m rho v (index_equations tree k es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    if k < 0 then ()
    else (
      let tree' = IX.index_put tree k e in
      let aux (j:nat) : Lemma
          (match IX.index_get tree' j with
           | Some x -> eq_ok schema p m rho v x
           | None -> True) =
        IX.lemma_index_put tree k e j;
        if j = k then assert (eq_ok schema p m rho v e)
        else ()
      in
      FStar.Classical.forall_intro aux;
      lemma_index_equations schema p m rho v tree' (k - 1) rest)

let node_ok (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
            (m:model base schema p)
            (rho:V.environment base (S.signature schema) [])
            (v:nat -> int) (lits:list expr) (q:poly) : prop =
  none_true schema p m rho lits ==> peval v q % p == 0

let values_ok (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
              (m:model base schema p)
              (rho:V.environment base (S.signature schema) [])
              (v:nat -> int) (lits:list expr)
              (tree:IX.index_tree poly) : prop =
  forall (j:nat).
    match IX.index_get tree j with
    | Some q -> node_ok schema p m rho v lits q
    | None -> True

let lemma_tree_get (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                   (m:model base schema p)
                   (rho:V.environment base (S.signature schema) [])
                   (v:nat -> int) (tree:IX.index_tree equation)
                   (j:nat) (e:equation)
  : Lemma (requires tree_ok schema p m rho v tree /\
                    IX.index_get tree j == Some e)
          (ensures eq_ok schema p m rho v e) = ()

let lemma_values_get (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                     (m:model base schema p)
                     (rho:V.environment base (S.signature schema) [])
                     (v:nat -> int) (lits:list expr)
                     (tree:IX.index_tree poly) (j:nat) (q:poly)
  : Lemma (requires values_ok schema p m rho v lits tree /\
                    IX.index_get tree j == Some q)
          (ensures node_ok schema p m rho v lits q) = ()

let lemma_record (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                 (m:model base schema p)
                 (rho:V.environment base (S.signature schema) [])
                 (v:nat -> int) (lits:list expr) (r:replay)
                 (cost:nat) (q:poly) (used:IX.index_tree bool)
  : Lemma (requires values_ok schema p m rho v lits r.values /\
                    node_ok schema p m rho v lits q)
          (ensures values_ok schema p m rho v lits
                    (Some?.v (record p r cost q used)).values) =
  let q' = normalize p q in
  let tree' = IX.index_put r.values r.next q' in
  let aux (j:nat) : Lemma
      (match IX.index_get tree' j with
       | Some x -> node_ok schema p m rho v lits x
       | None -> True) =
    IX.lemma_index_put r.values r.next q' j;
    if j = r.next then (
      assert (node_ok schema p m rho v lits q);
      lemma_normalize v p q)
    else ()
  in
  FStar.Classical.forall_intro aux

let lemma_step (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
               (m:model base schema p)
               (rho:V.environment base (S.signature schema) [])
               (v:nat -> int) (nvars:nat) (eqs:IX.index_tree equation)
               (sup:IX.index_tree bool) (lits:list expr)
               (r:replay) (n:pac_node) (r':replay)
  : Lemma (requires D.scoped_args [] lits /\
                    tree_ok schema p m rho v eqs /\
                    values_ok schema p m rho v lits r.values /\
                    step p nvars eqs sup lits r n == Some r')
          (ensures values_ok schema p m rho v lits r'.values) =
  match n with
  | PacInput j ->
    (match IX.index_get eqs j with
     | Some (q, Definition) ->
       lemma_tree_get schema p m rho v eqs j (q, Definition);
       assert (node_ok schema p m rho v lits q);
       lemma_record schema p m rho v lits r (poly_size q) q r.used
     | Some (q, Premise k l) ->
       lemma_tree_get schema p m rho v eqs j (q, Premise k l);
       let aux () : Lemma
           (requires none_true schema p m rho lits /\ negated_in l lits)
           (ensures peval v q % p == 0) =
         lemma_negated_in schema p m rho l lits;
         assert (eq_ok schema p m rho v (q, Premise k l));
         assert (SS.truth_at schema m.booleans m.scalar_model
                   (override schema p m) [] rho l);
         assert (peval v q % p == 0)
       in
       FStar.Classical.move_requires aux ();
       lemma_record schema p m rho v lits r (poly_size q) q
         (IX.index_put r.used k true)
     | _ -> ())
  | PacAdd a b ->
    let qa = Some?.v (earlier r a) in
    let qb = Some?.v (earlier r b) in
    assert (IX.index_get r.values a == Some qa);
    assert (IX.index_get r.values b == Some qb);
    lemma_values_get schema p m rho v lits r.values a qa;
    lemma_values_get schema p m rho v lits r.values b qb;
    lemma_padd v qa qb;
    let aux () : Lemma
        (requires none_true schema p m rho lits)
        (ensures peval v (padd qa qb) % p == 0) =
      assert (peval v qa % p == 0);
      assert (peval v qb % p == 0);
      lemma_zero_sum p (peval v qa) (peval v qb)
    in
    FStar.Classical.move_requires aux ();
    lemma_record schema p m rho v lits r (poly_size qa + poly_size qb)
      (padd qa qb) r.used
  | PacMul source c fs ->
    let q = Some?.v (earlier r source) in
    let (_, k) = Some?.v (numeral c) in
    let vs = Some?.v (variables nvars 0 fs) in
    assert (IX.index_get r.values source == Some q);
    lemma_values_get schema p m rho v lits r.values source q;
    lemma_scale_mono v vs k q;
    let aux () : Lemma
        (requires none_true schema p m rho lits)
        (ensures peval v (scale_mono vs k q) % p == 0) =
      assert (peval v q % p == 0);
      lemma_zero_product p (k * mval v vs) (peval v q)
    in
    FStar.Classical.move_requires aux ();
    lemma_record schema p m rho v lits r
      (poly_size q + L.length q * L.length vs)
      (scale_mono vs k q) r.used

let rec lemma_replay_nodes (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                           (m:model base schema p)
                           (rho:V.environment base (S.signature schema) [])
                           (v:nat -> int) (nvars:nat)
                           (eqs:IX.index_tree equation) (sup:IX.index_tree bool)
                           (lits:list expr) (r:replay) (ns:list pac_node) (r':replay)
  : Lemma (requires D.scoped_args [] lits /\
                    tree_ok schema p m rho v eqs /\
                    values_ok schema p m rho v lits r.values /\
                    replay_nodes p nvars eqs sup lits r ns == Some r')
          (ensures values_ok schema p m rho v lits r'.values)
          (decreases ns) =
  match ns with
  | [] -> ()
  | n :: rest ->
    let r1 = Some?.v (step p nvars eqs sup lits r n) in
    lemma_step schema p m rho v nvars eqs sup lits r n r1;
    lemma_replay_nodes schema p m rho v nvars eqs sup lits r1 rest r'

let lemma_clause_literals_scoped (e:expr)
  : Lemma (requires D.scoped [] e)
          (ensures D.scoped_args [] (clause_literals e)) =
  match e with
  | App f args ->
    if C.canonical_or f then assert (D.scoped_args [] args)
    else lemma_scoped_append_single [] e
  | _ -> lemma_scoped_append_single [] e

let lemma_check_sound (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                      (pmodel:model base schema p)
                      (c:certificate) (e:expr)
  : Lemma (requires find_modulus_args c.pac_premises == Some p /\
                    D.scoped_args [] c.pac_premises /\ D.scoped [] e /\
                    get_sort e == bool_sort /\ check c e)
          (ensures SS.truth_at schema pmodel.booleans pmodel.scalar_model
                    (override schema p pmodel)
                    [] (empty_environment schema) e) =
  let st = Some?.v (bind p 0 empty_encoding c.pac_premises) in
  assert (p >= 2);
  lemma_bind_scoped p 0 empty_encoding c.pac_premises st;
  let sup = Some?.v
    (support_tree (L.length c.pac_premises) (-1) IX.Empty c.pac_support) in
  let v = valuation schema p pmodel (empty_environment schema) st.terms in
  let eqs = index_equations IX.Empty (L.length st.equations - 1) st.equations in
  let lits = clause_literals e in
  let r = Some?.v
    (replay_nodes p (L.length st.terms) eqs sup lits initial_replay c.pac_nodes) in
  lemma_prefix_refl st.terms;
  lemma_bind schema p pmodel (empty_environment schema) 0
    empty_encoding c.pac_premises st st.terms;
  lemma_index_equations schema p pmodel (empty_environment schema) v
    IX.Empty (L.length st.equations - 1) st.equations;
  lemma_clause_literals_scoped e;
  lemma_replay_nodes schema p pmodel (empty_environment schema) v
    (L.length st.terms) eqs sup lits initial_replay c.pac_nodes r;
  assert (IX.index_get r.values c.pac_root == Some [([], 1)]);
  lemma_values_get schema p pmodel (empty_environment schema) v lits
    r.values c.pac_root [([], 1)];
  lemma_peval_constant v 1;
  M.small_mod 1 p;
  let aux () : Lemma
      (requires not (SS.truth_at schema pmodel.booleans pmodel.scalar_model
                       (override schema p pmodel) [] (empty_environment schema) e))
      (ensures False) =
    lemma_clause_false_literals schema p pmodel (empty_environment schema) e;
    assert (none_true schema p pmodel (empty_environment schema) lits);
    assert (node_ok schema p pmodel (empty_environment schema) v lits [([], 1)]);
    assert (peval v [([], 1)] % p == 0);
    assert (peval v [([], 1)] == 1);
    assert (1 % p == 0);
    assert (1 % p == 1);
    assert False
  in
  FStar.Classical.move_requires aux ()

(* ----------------------------------------------------------------- *)
(* Sort-indexed counterparts of the legacy rewrite checkers            *)
(* ----------------------------------------------------------------- *)

let atom_poly (tbl:list expr) (e:expr) : option poly =
  match index_of e tbl with
  | Some k -> Some [([k], 1)]
  | None -> None

let rec to_poly (p:int) (tbl:list expr) (e:expr) : Tot (option poly) (decreases e) =
  match numeral e with
  | Some (q, n) -> if q = p then Some [([], n)] else None
  | None ->
    (match e with
     | App f args ->
       (match operation_at f args with
        | Some (q, op) ->
          if q <> p then None
          else (match to_polys p tbl args with
                | Some qs -> combine op qs
                | None -> None)
        | None -> if get_sort e = ff_sort p then atom_poly tbl e else None)
     | _ -> if get_sort e = ff_sort p then atom_poly tbl e else None)

and to_polys (p:int) (tbl:list expr) (args:list expr)
  : Tot (option (list poly)) (decreases args) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match to_poly p tbl a, to_polys p tbl rest with
     | Some q, Some qs -> Some (q :: qs)
     | _, _ -> None)

let rec collect (p:int) (tbl:list expr) (e:expr) : Tot (list expr) (decreases e) =
  match numeral e with
  | Some _ -> tbl
  | None ->
    (match e with
     | App f args ->
       (match operation_at f args with
        | Some (q, _) -> if q <> p then tbl else collect_args p tbl args
        | None -> if L.mem e tbl then tbl else L.append tbl [e])
     | _ -> if L.mem e tbl then tbl else L.append tbl [e])

and collect_args (p:int) (tbl:list expr) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> tbl
  | a :: rest -> collect_args p (collect p tbl a) rest

let shared_modulus (a b:expr) : option int =
  match modulus_of a with
  | Some p -> Some p
  | None -> modulus_of b

let difference (p:int) (tbl:list expr) (a b:expr) : option poly =
  match to_poly p tbl a, to_poly p tbl b with
  | Some qa, Some qb -> Some (padd qa (pscale (-1) qb))
  | _, _ -> None

let rec zero_mod (p:pos) (q:poly) : Tot bool (decreases q) =
  match q with
  | [] -> true
  | (_, c) :: rest -> c % p = 0 && zero_mod p rest

let rec prune (p:pos) (q:poly) : Tot poly (decreases q) =
  match q with
  | [] -> []
  | (m, c) :: rest -> if c % p = 0 then prune p rest else (m, c) :: prune p rest

let nonzero_constant (p:pos) (d:poly) : bool =
  match prune p d with
  | [([], c)] -> c % p <> 0
  | _ -> false

let term_equivalent (a b:expr) : bool =
  match shared_modulus a b with
  | None -> false
  | Some p ->
    if p >= 2 && closed_ff p a && closed_ff p b
    then (match difference p (collect p (collect p [] a) b) a b with
          | Some d -> zero_mod p d
          | None -> false)
    else false

let atom_modulus (e:expr) : option int =
  match eq_parts e with
  | Some (s, t) -> shared_modulus s t
  | None -> None

let eq_collect (p:int) (tbl:list expr) (e:expr) : list expr =
  match eq_parts e with
  | Some (s, t) -> collect p (collect p tbl s) t
  | None -> tbl

let eq_diff (p:int) (tbl:list expr) (e:expr) : option poly =
  match eq_parts e with
  | Some (s, t) -> if closed_ff p s && closed_ff p t then difference p tbl s t else None
  | None -> None

let eq_truth_equivalent (a b:expr) : bool =
  match atom_modulus a with
  | None -> false
  | Some p ->
    if p >= 2
    then (match eq_diff p (eq_collect p [] a) a with
          | Some d -> (b = R.true_expr && zero_mod p d) ||
                      (b = R.false_expr && nonzero_constant p d)
          | None -> false)
    else false

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

let scale_witness (p:pos) (d1 d2:poly) : option (int & int) =
  match first_nonzero p d2 with
  | None -> None
  | Some m ->
    let c1 = coeff_of m d1 in
    let c2 = coeff_of m d2 in
    (match inverse_mod p c1, inverse_mod p c2 with
     | Some i1, Some i2 -> Some ((c1 * i2) % p, (c2 * i1) % p)
     | _, _ -> None)

let same_zero_set (p:pos) (d1 d2:poly) : bool =
  (zero_mod p d1 && zero_mod p d2) ||
  (match scale_witness p d1 d2 with
   | Some (k, w) ->
     zero_mod p (padd d1 (pscale (-k) d2)) &&
     zero_mod p (padd d2 (pscale (-w) d1))
   | None -> false)

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

let atom_equivalent (atom x:expr) : bool =
  x = atom || eq_truth_equivalent atom x || eq_eq_equivalent atom x

let ite_eq_parts (e:expr) : option (expr & expr & expr & expr) =
  match eq_parts e with
  | Some (l, k) ->
    (match A.ite_parts l with
     | Some (c, t, u) -> Some (c, t, u, k)
     | None -> None)
  | None -> None

let conjunction_parts (e:expr) : option (expr & expr) =
  match e with
  | App f [x; y] ->
    if f = R.and_decl [x; y] && get_sort x = bool_sort && get_sort y = bool_sort
    then Some (x, y) else None
  | _ -> None

let ite_eq_equivalent (a b:expr) : bool =
  match ite_eq_parts a, conjunction_parts b with
  | Some (c, t, u, k), Some (x, y) ->
    let at = R.mk_eq_expr t k in
    let au = R.mk_eq_expr u k in
    (y = R.mk_not_expr c && eq_truth_equivalent at R.false_expr && atom_equivalent au x) ||
    (y = c && eq_truth_equivalent au R.false_expr && atom_equivalent at x)
  | _, _ -> false

let equivalent (a b:expr) : bool =
  term_equivalent a b || eq_eq_equivalent a b ||
  eq_truth_equivalent a b || eq_truth_equivalent b a || ite_eq_equivalent a b

(* ----------------------------------------------------------------- *)
(* Sort-indexed exhaustive finite-field clause checker                 *)
(* ----------------------------------------------------------------- *)

let max_assignments : nat = 4096

let leaf (p:pos) (tbl:list expr) (v:nat -> int) (e:expr) : option int =
  if get_sort e = ff_sort p
  then (match index_of e tbl with Some k -> Some (v k) | None -> None)
  else None

let rec eval_ff (p:pos) (tbl:list expr) (v:nat -> int) (e:expr)
  : Tot (option int) (decreases e) =
  match numeral e with
  | Some (q, n) -> if q = p then Some n else None
  | None ->
    (match e with
     | App f args ->
       (match operation_at f args with
        | Some (q, op) ->
          if q <> p then None
          else (match eval_ffs p tbl v args with
                | Some xs -> Some (calculate p op xs)
                | None -> None)
        | None ->
          (match args with
           | [c; t; u] ->
             if f = A.term_ite_decl (ff_sort p) && get_sort c = bool_sort &&
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

and eval_bool (p:pos) (tbl:list expr) (v:nat -> int) (e:expr)
  : Tot (option bool) (decreases e) =
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

let add_leaf (tbl:list expr) (e:expr) : list expr =
  if L.mem e tbl then tbl else L.append tbl [e]

let rec leaves (p:int) (tbl:list expr) (e:expr) : Tot (list expr) (decreases e) =
  match numeral e with
  | Some _ -> tbl
  | None ->
    (match e with
     | App f args ->
       if Some? (operation_at f args) || get_sort e <> ff_sort p || Some? (A.ite_parts e)
       then leaves_args p tbl args
       else add_leaf tbl e
     | _ -> if get_sort e = ff_sort p then add_leaf tbl e else tbl)

and leaves_args (p:int) (tbl:list expr) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> tbl
  | a :: rest -> leaves_args p (leaves p tbl a) rest

let rec within_budget (p:int) (n:nat) (acc:int) : Tot bool (decreases n) =
  if acc > max_assignments then false
  else if n = 0 then true
  else within_budget p (n - 1) (acc * p)

let with_head (f:list int -> bool) (x:int) (r:list int) : bool = f (x :: r)

let rec for_all_vectors (p:nat) (n:nat) (f:list int -> bool)
  : Tot bool (decreases %[n; 0; 0]) =
  if n = 0 then f [] else for_all_heads p p (n - 1) f

and for_all_heads (p:nat) (k:nat) (n:nat) (f:list int -> bool)
  : Tot bool (decreases %[n; 1; k]) =
  if k = 0 then true
  else for_all_vectors p n (with_head f (k - 1)) && for_all_heads p (k - 1) n f

let vector_value (r:list int) : nat -> int =
  fun k -> if k < L.length r then L.index r k else 0

let clause_true (p:pos) (tbl:list expr) (e:expr) (r:list int) : bool =
  eval_bool p tbl (vector_value r) e = Some true

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

(* ----------------------------------------------------------------- *)
(* Polynomial translation and equality-rewrite soundness               *)
(* ----------------------------------------------------------------- *)

let lemma_diff_mod (p:pos) (x y:int)
  : Lemma (requires (x - y) % p == 0) (ensures x % p == y % p) =
  M.euclidean_division_definition (x - y) p;
  M.lemma_mod_plus y ((x - y) / p) p

let rec lemma_zero_mod_poly (v:nat -> int) (p:pos) (q:poly)
  : Lemma (requires zero_mod p q) (ensures peval v q % p == 0)
          (decreases q) =
  match q with
  | [] -> ()
  | (m, c) :: rest ->
    lemma_zero_mod_poly v p rest;
    M.lemma_mod_mul_distr_l c (mval v m) p;
    lemma_add_cong p (c * mval v m) (peval v rest) 0 0

let lemma_atom_poly_sem (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                        (m:model base schema p)
                        (rho:V.environment base (S.signature schema) [])
                        (tbl:list expr) (e:expr) (q:poly)
  : Lemma (requires D.scoped [] e /\ get_sort e == ff_sort p /\
                    D.scoped_args [] tbl /\ atom_poly tbl e == Some q)
          (ensures peval (valuation schema p m rho tbl) q % p ==
                   residue schema p m rho e) =
  let k = Some?.v (index_of e tbl) in
  lemma_index_of e tbl k;
  lemma_scoped_args_index tbl k;
  lemma_valuation_index schema p m rho tbl k;
  assert (q == [([k], 1)]);
  lemma_peval_variable (valuation schema p m rho tbl) k;
  assert (peval (valuation schema p m rho tbl) q ==
          valuation schema p m rho tbl k);
  m.project_range (evaluate_at schema p m [] rho e);
  M.small_mod (residue schema p m rho e) p

#push-options "--fuel 4 --ifuel 2"
let rec lemma_to_poly_sem (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                          (m:model base schema p)
                          (rho:V.environment base (S.signature schema) [])
                          (tbl:list expr) (e:expr) (q:poly)
  : Lemma (requires D.scoped [] e /\ get_sort e == ff_sort p /\
                    D.scoped_args [] tbl /\ to_poly p tbl e == Some q)
          (ensures peval (valuation schema p m rho tbl) q % p ==
                   residue schema p m rho e)
          (decreases e) =
  match numeral e with
  | Some (qmod, n) ->
    assert (qmod == p);
    (match e with
     | App f [] -> lemma_evaluate_numeral_at schema p m [] rho f n
     | _ -> ());
    lemma_peval_constant (valuation schema p m rho tbl) n;
    M.small_mod n p
  | None ->
    (match e with
     | App f args ->
       (match operation_at f args with
        | Some (qmod, op) ->
          if qmod == p then (
            let qs = Some?.v (to_polys p tbl args) in
            let fq = Some?.v (combine op qs) in
            assert (D.scoped_args [] args);
            assert (args_have_sort p args);
            assert (operation_of f == Some (p, op));
            lemma_to_polys_sem schema p m rho tbl args qs;
            let xs = expressions_residues schema p m rho args in
            assert (match_list (valuation schema p m rho tbl) p qs xs);
            lemma_evaluate_operation_at schema p m [] rho f args op;
            lemma_residues_args schema p m rho args f.domain;
            lemma_combine (valuation schema p m rho tbl) p op qs xs fq;
            assert (residue schema p m rho e ==
                    calculate p op xs);
            lemma_same_mod_diff p
              (peval (valuation schema p m rho tbl) fq)
              (residue schema p m rho e))
        | None -> lemma_atom_poly_sem schema p m rho tbl e q)
     | _ -> lemma_atom_poly_sem schema p m rho tbl e q)

and lemma_to_polys_sem (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                       (m:model base schema p)
                       (rho:V.environment base (S.signature schema) [])
                       (tbl:list expr) (args:list expr) (qs:list poly)
  : Lemma (requires D.scoped_args [] args /\ args_have_sort p args /\
                    D.scoped_args [] tbl /\ to_polys p tbl args == Some qs)
          (ensures match_list (valuation schema p m rho tbl) p qs
                   (expressions_residues schema p m rho args))
          (decreases args) =
  match args, qs with
  | a :: rest, q :: qs' ->
    V.lemma_sort_eq (get_sort a) (ff_sort p);
    lemma_to_poly_sem schema p m rho tbl a q;
    lemma_to_polys_sem schema p m rho tbl rest qs'
  | _, _ -> ()
#pop-options

let lemma_difference_sem (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                         (m:model base schema p)
                         (rho:V.environment base (S.signature schema) [])
                         (tbl:list expr) (a b:expr) (d:poly)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\
                    get_sort a == ff_sort p /\ get_sort b == ff_sort p /\
                    D.scoped_args [] tbl /\ difference p tbl a b == Some d)
          (ensures peval (valuation schema p m rho tbl) d % p ==
                   (residue schema p m rho a - residue schema p m rho b) % p) =
  let qa = Some?.v (to_poly p tbl a) in
  let qb = Some?.v (to_poly p tbl b) in
  let v = valuation schema p m rho tbl in
  lemma_to_poly_sem schema p m rho tbl a qa;
  lemma_to_poly_sem schema p m rho tbl b qb;
  lemma_pscale v (-1) qb;
  lemma_padd v qa (pscale (-1) qb);
  M.lemma_mod_sub_distr 0 (peval v qb) p;
  lemma_add_cong p (peval v qa) (peval v (pscale (-1) qb))
    (residue schema p m rho a) (0 - residue schema p m rho b)

let lemma_residues_equal (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                         (m:model base schema p) (x y:int)
  : Lemma (requires 0 <= x /\ x < p /\ 0 <= y /\ y < p)
          (ensures ((x - y) % p == 0) <==> x == y) =
  if (x - y) % p == 0 then (
    lemma_diff_mod p x y;
    M.small_mod x p;
    M.small_mod y p)

let rec lemma_collect_scoped (p:int) (tbl:list expr) (e:expr)
  : Lemma (requires D.scoped_args [] tbl /\ D.scoped [] e)
          (ensures D.scoped_args [] (collect p tbl e))
          (decreases e) =
  match numeral e with
  | Some _ -> ()
  | None ->
    (match e with
     | App f args ->
       (match operation_at f args with
        | Some (q, _) ->
          if q == p then (
            lemma_collect_args_scoped p tbl args;
            assert (D.scoped_args [] (collect_args p tbl args)))
        | None ->
          if L.mem e tbl then ()
          else (
           lemma_scoped_append_single tbl e;
            assert (D.scoped_args [] (L.append tbl [e]))))
     | _ ->
       if L.mem e tbl then ()
       else (
        lemma_scoped_append_single tbl e;
         assert (D.scoped_args [] (L.append tbl [e]))))

and lemma_collect_args_scoped (p:int) (tbl args:list expr)
  : Lemma (requires D.scoped_args [] tbl /\ D.scoped_args [] args)
          (ensures D.scoped_args [] (collect_args p tbl args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_scoped_args_index (a :: rest) 0;
    lemma_collect_scoped p tbl a;
    lemma_collect_args_scoped p (collect p tbl a) rest

let lemma_term_equivalent_sound (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                                (m:model base schema p)
                                (rho:V.environment base (S.signature schema) [])
                                (a b:expr)
  : Lemma (requires term_equivalent a b /\ shared_modulus a b == Some p)
          (ensures evaluate_at schema p m [] rho a ==
                   evaluate_at schema p m [] rho b) =
  assert (p >= 2 /\ closed_ff p a /\ closed_ff p b);
  let tbl = collect p (collect p [] a) b in
  lemma_collect_scoped p [] a;
  lemma_collect_scoped p (collect p [] a) b;
  assert (D.scoped_args [] tbl);
  let d = Some?.v (difference p tbl a b) in
  let v = valuation schema p m rho tbl in
  lemma_zero_mod_poly v p d;
  lemma_difference_sem schema p m rho tbl a b d;
  m.project_range (evaluate_at schema p m [] rho a);
  m.project_range (evaluate_at schema p m [] rho b);
  assert (residue schema p m rho a == m.project (evaluate_at schema p m [] rho a));
  assert (residue schema p m rho b == m.project (evaluate_at schema p m [] rho b));
  lemma_diff_mod p (residue schema p m rho a) (residue schema p m rho b);
  lemma_residues_equal schema p m (residue schema p m rho a) (residue schema p m rho b);
  m.project_reflection
    (evaluate_at schema p m [] rho a) (evaluate_at schema p m [] rho b)

let lemma_boolean_evaluations_equal (#base:sort -> Type0) (schema:S.checked_schema)
                                    (p:pos) (m:model base schema p)
                                    (rho:V.environment base (S.signature schema) [])
                                    (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort /\
                    truth_at schema p m [] rho a == truth_at schema p m [] rho b)
          (ensures evaluate_at schema p m [] rho a == evaluate_at schema p m [] rho b) =
  SS.lemma_boolean schema m.booleans (evaluate_at schema p m [] rho a);
  SS.lemma_boolean schema m.booleans (evaluate_at schema p m [] rho b)

let rec lemma_prune_mod (v:nat -> int) (p:pos) (q:poly)
  : Lemma (ensures peval v (prune p q) % p == peval v q % p)
          (decreases q) =
  match q with
  | [] -> ()
  | (m, c) :: rest ->
    lemma_prune_mod v p rest;
    M.lemma_mod_mul_distr_l c (mval v m) p;
    if c % p == 0 then (
      assert (prune p q == prune p rest);
      lemma_add_cong p (c * mval v m) (peval v rest) 0 (peval v rest))
    else (
      assert (prune p q == (m, c) :: prune p rest);
      lemma_add_cong p (c * mval v m) (peval v (prune p rest))
        (c * mval v m) (peval v rest))

let lemma_eq_collect_scoped (p:int) (tbl:list expr) (e:expr)
  : Lemma (requires D.scoped_args [] tbl /\ D.scoped [] e)
          (ensures D.scoped_args [] (eq_collect p tbl e)) =
  match e with
  | App f args ->
    (match args with
     | a :: b :: [] ->
       assert (D.scoped_args [] [a; b]);
       assert_norm (D.scoped_args [] [a; b] ==
                    (D.scoped [] a /\ D.scoped [] b));
       assert_norm (L.length [a; b] == 2);
       assert (D.scoped [] a);
       assert (D.scoped [] b);
       (match eq_parts e with
        | Some (x, y) ->
          assert (x == a);
          assert (y == b);
          assert (D.scoped [] x);
          assert (D.scoped [] y);
          lemma_collect_scoped p tbl x;
          lemma_collect_scoped p (collect p tbl x) y
        | None -> assert (eq_collect p tbl e == tbl))
     | [] -> assert (eq_collect p tbl e == tbl)
     | [_] -> assert (eq_collect p tbl e == tbl)
     | _ :: _ :: _ -> assert (eq_collect p tbl e == tbl))
  | _ -> assert (eq_collect p tbl e == tbl)

let lemma_eq_diff_sem (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                      (m:model base schema p)
                      (rho:V.environment base (S.signature schema) [])
                      (tbl:list expr) (e:expr) (d:poly)
  : Lemma (requires D.scoped [] e /\ D.scoped_args [] tbl /\
                    eq_diff p tbl e == Some d)
          (ensures truth_at schema p m [] rho e ==
                   (peval (valuation schema p m rho tbl) d % p == 0)) =
  let (a, b) = Some?.v (eq_parts e) in
  let x = residue schema p m rho a in
  let y = residue schema p m rho b in
  lemma_eq_parts_normalized e a b;
  assert (e == R.mk_eq_expr a b);
  lemma_difference_sem schema p m rho tbl a b d;
  lemma_truth_field_eq schema p m rho a b;
  m.project_range (evaluate_at schema p m [] rho a);
  m.project_range (evaluate_at schema p m [] rho b);
  lemma_residues_equal schema p m x y;
  assert (residue schema p m rho a == x);
  assert (residue schema p m rho b == y);
  assert (truth_at schema p m [] rho e == (x == y));
  assert ((peval (valuation schema p m rho tbl) d % p == 0) <==>
          ((x - y) % p == 0));
  assert ((peval (valuation schema p m rho tbl) d % p == 0) <==> x == y);
  assert (truth_at schema p m [] rho e ==
          (peval (valuation schema p m rho tbl) d % p == 0))

let lemma_true_false_values (#base:sort -> Type0) (schema:S.checked_schema)
                            (p:pos) (m:model base schema p)
                            (rho:V.environment base (S.signature schema) [])
  : Lemma (truth_at schema p m [] rho R.true_expr == true /\
           truth_at schema p m [] rho R.false_expr == false) =
  assert_norm (D.scoped [] R.true_expr);
  assert_norm (D.scoped [] R.false_expr);
  match R.true_expr, R.false_expr with
  | App t [], App f [] ->
    SS.lemma_evaluate_core_at schema m.booleans m.scalar_model
      (override schema p m) [] rho t [];
    SS.lemma_evaluate_core_at schema m.booleans m.scalar_model
      (override schema p m) [] rho f []
  | _, _ -> ()

let lemma_eq_truth_equivalent_sound (#base:sort -> Type0) (schema:S.checked_schema)
                                    (p:pos) (m:model base schema p)
                                    (rho:V.environment base (S.signature schema) [])
                                    (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\
                    eq_truth_equivalent a b /\ atom_modulus a == Some p)
          (ensures truth_at schema p m [] rho a == truth_at schema p m [] rho b) =
  let tbl = eq_collect p [] a in
  lemma_eq_collect_scoped p [] a;
  assert (D.scoped_args [] tbl);
  let d = Some?.v (eq_diff p tbl a) in
  let v = valuation schema p m rho tbl in
  lemma_eq_diff_sem schema p m rho tbl a d;
  lemma_true_false_values schema p m rho;
  if b == R.true_expr then (
    lemma_zero_mod_poly v p d;
    assert (truth_at schema p m [] rho a);
    assert (truth_at schema p m [] rho a == truth_at schema p m [] rho b))
  else (
    lemma_prune_mod v p d;
    match prune p d with
    | [([], c)] ->
      lemma_peval_constant v c;
      assert (peval v (prune p d) % p == c % p);
      assert (c % p <> 0);
      assert (peval v d % p <> 0);
      assert (not (truth_at schema p m [] rho a));
      assert (truth_at schema p m [] rho a == truth_at schema p m [] rho b)
    | _ -> ())

let lemma_scaled_zero (p:pos) (y x k:int)
  : Lemma (requires (y - k * x) % p == 0)
          (ensures x % p == 0 ==> y % p == 0) =
  lemma_diff_mod p y (k * x);
  M.lemma_mod_mul_distr_r k x p

let lemma_same_zero_set_sound (v:nat -> int) (p:pos) (d1 d2:poly)
  : Lemma (requires same_zero_set p d1 d2)
          (ensures (peval v d1 % p == 0 <==> peval v d2 % p == 0)) =
  if zero_mod p d1 && zero_mod p d2 then (
    lemma_zero_mod_poly v p d1;
    lemma_zero_mod_poly v p d2)
  else
    match scale_witness p d1 d2 with
    | Some (k, w) ->
      lemma_pscale v (-k) d2;
      lemma_padd v d1 (pscale (-k) d2);
      lemma_zero_mod_poly v p (padd d1 (pscale (-k) d2));
      lemma_pscale v (-w) d1;
      lemma_padd v d2 (pscale (-w) d1);
      lemma_zero_mod_poly v p (padd d2 (pscale (-w) d1));
      M.neg_mul_left k (peval v d2);
      M.neg_mul_left w (peval v d1);
      assert (peval v (padd d1 (pscale (-k) d2)) ==
              peval v d1 - k * peval v d2);
      assert (peval v (padd d2 (pscale (-w) d1)) ==
              peval v d2 - w * peval v d1);
      lemma_scaled_zero p (peval v d1) (peval v d2) k;
      lemma_scaled_zero p (peval v d2) (peval v d1) w
    | None -> ()

let lemma_eq_eq_equivalent_sound (#base:sort -> Type0) (schema:S.checked_schema)
                                 (p:pos) (m:model base schema p)
                                 (rho:V.environment base (S.signature schema) [])
                                 (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\
                    eq_eq_equivalent a b /\
                    (match atom_modulus a with
                     | Some q -> q == p
                     | None -> atom_modulus b == Some p))
          (ensures truth_at schema p m [] rho a == truth_at schema p m [] rho b) =
  let tbl = eq_collect p (eq_collect p [] a) b in
  lemma_eq_collect_scoped p [] a;
  lemma_eq_collect_scoped p (eq_collect p [] a) b;
  assert (D.scoped_args [] tbl);
  let d1 = Some?.v (eq_diff p tbl a) in
  let d2 = Some?.v (eq_diff p tbl b) in
  let v = valuation schema p m rho tbl in
  lemma_eq_diff_sem schema p m rho tbl a d1;
  lemma_eq_diff_sem schema p m rho tbl b d2;
  lemma_same_zero_set_sound v p d1 d2

let lemma_eq_atom_truth (#base:sort -> Type0) (schema:S.checked_schema)
                        (p:pos) (m:model base schema p)
                        (rho:V.environment base (S.signature schema) [])
                        (e s t:expr)
  : Lemma (requires D.scoped [] e /\ D.scoped [] s /\ D.scoped [] t /\
                    get_sort s == get_sort t /\ eq_parts e == Some (s, t))
          (ensures truth_at schema p m [] rho e ==
                   (evaluate_at schema p m [] rho s ==
                    evaluate_at schema p m [] rho t)) =
  lemma_eq_parts_normalized e s t;
  SS.lemma_equality_at schema m.booleans m.scalar_model
    (override schema p m) [] rho s t

let atom_equivalent_at_modulus (p:int) (atom x:expr) : bool =
  x = atom ||
  (match atom_modulus atom with
   | Some q -> q = p
   | None -> atom_modulus x = Some p)

let lemma_atom_equivalent_modulus (p:int) (atom x:expr)
  : Lemma (requires atom_equivalent_at_modulus p atom x)
          (ensures x == atom \/
                   (match atom_modulus atom with
                    | Some q -> q == p
                    | None -> atom_modulus x == Some p)) = ()

let lemma_atom_equivalent_truth (#base:sort -> Type0) (schema:S.checked_schema)
                                (p:pos) (m:model base schema p)
                                (rho:V.environment base (S.signature schema) [])
                                (atom x:expr)
  : Lemma (requires D.scoped [] atom /\ D.scoped [] x /\
                    atom_equivalent atom x /\
                    atom_equivalent_at_modulus p atom x)
          (ensures truth_at schema p m [] rho atom ==
                   truth_at schema p m [] rho x) =
  if x == atom then ()
  else if eq_truth_equivalent atom x then
    lemma_eq_truth_equivalent_sound schema p m rho atom x
  else (
    lemma_atom_equivalent_modulus p atom x;
    lemma_eq_eq_equivalent_sound schema p m rho atom x
  )

let ite_eq_sound_at_modulus (p:int) (a b:expr) : bool =
  match ite_eq_parts a, conjunction_parts b with
  | Some (c, t, u, k), Some (x, y) ->
    let at = R.mk_eq_expr t k in
    let au = R.mk_eq_expr u k in
    if y = R.mk_not_expr c then
      atom_modulus at = Some p && atom_equivalent_at_modulus p au x
    else if y = c then
      atom_modulus au = Some p && atom_equivalent_at_modulus p at x
    else false
  | _, _ -> false

let lemma_ite_eq_modulus_parts (p:int) (a b c t u k x y:expr)
  : Lemma (requires ite_eq_parts a == Some (c, t, u, k) /\
                    conjunction_parts b == Some (x, y) /\
                    ite_eq_sound_at_modulus p a b)
          (ensures
            (y == R.mk_not_expr c ==>
             atom_modulus (R.mk_eq_expr t k) == Some p /\
             atom_equivalent_at_modulus p (R.mk_eq_expr u k) x) /\
            (y == c ==>
             atom_modulus (R.mk_eq_expr u k) == Some p /\
             atom_equivalent_at_modulus p (R.mk_eq_expr t k) x)) =
  if y = R.mk_not_expr c then (
    assert (atom_modulus (R.mk_eq_expr t k) == Some p);
    assert (atom_equivalent_at_modulus p (R.mk_eq_expr u k) x))
  else if y = c then (
    assert (atom_modulus (R.mk_eq_expr u k) == Some p);
    assert (atom_equivalent_at_modulus p (R.mk_eq_expr t k) x))

let lemma_conjunction_parts_scoped (e x y:expr)
  : Lemma (requires D.scoped [] e /\ conjunction_parts e == Some (x, y))
          (ensures D.scoped [] x /\ D.scoped [] y) =
  match e with
  | App f args ->
    (match args with
     | a :: b :: [] ->
       assert (D.scoped_args [] [a; b]);
       assert_norm (D.scoped_args [] [a; b] ==
                    (D.scoped [] a /\ D.scoped [] b));
       assert (D.scoped [] a /\ D.scoped [] b);
       assert (a == x /\ b == y)
     | [] -> ()
     | [_] -> ()
     | _ :: _ :: _ -> ())
  | _ -> ()

let lemma_false_atom (#base:sort -> Type0) (schema:S.checked_schema)
                     (p:pos) (m:model base schema p)
                     (rho:V.environment base (S.signature schema) [])
                     (atom:expr)
  : Lemma (requires D.scoped [] atom /\
                    eq_truth_equivalent atom R.false_expr /\
                    atom_modulus atom == Some p)
          (ensures not (truth_at schema p m [] rho atom)) =
  assert_norm (D.scoped [] R.false_expr);
  lemma_eq_truth_equivalent_sound schema p m rho atom R.false_expr;
  lemma_true_false_values schema p m rho

#push-options "--fuel 8 --ifuel 4"
let lemma_conjunction_truth (#base:sort -> Type0) (schema:S.checked_schema)
                            (p:pos) (m:model base schema p)
                            (rho:V.environment base (S.signature schema) [])
                            (e x y:expr)
  : Lemma (requires D.scoped [] e /\ D.scoped [] x /\ D.scoped [] y /\
                    get_sort x == bool_sort /\ get_sort y == bool_sort /\
                    conjunction_parts e == Some (x, y))
          (ensures truth_at schema p m [] rho e ==
                   (truth_at schema p m [] rho x &&
                    truth_at schema p m [] rho y)) =
  match e with
  | App f [a; b] ->
    assert (a == x /\ b == y);
    assert (f == R.and_decl [x; y]);
    assert (f.decl_name == "and");
    assert (f.interp == Some op_and);
    assert (f.range == bool_sort);
    assert (f.int_params == []);
    assert_norm (SS.boolean_sorts f.domain);
    lemma_boolean_sorts_agree f.domain;
    assert (C.boolean_sorts f.domain);
    assert (C.canonical_and f);
    assert (SS.classify f == SS.Nary B.And);
    lemma_nary_at schema p m rho f [x; y] B.And;
    assert_norm (B.geval_args (truth_at schema p m [] rho) B.And
                   [B.Atom x; B.Atom y] ==
                 (truth_at schema p m [] rho x && truth_at schema p m [] rho y))
  | _ -> ()
#pop-options

let lemma_ite_eq_equivalent_sound (#base:sort -> Type0) (schema:S.checked_schema)
                                  (p:pos) (m:model base schema p)
                                  (rho:V.environment base (S.signature schema) [])
                                  (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\
                    ite_eq_equivalent a b /\
                    ite_eq_sound_at_modulus p a b)
          (ensures truth_at schema p m [] rho a ==
                   truth_at schema p m [] rho b) =
  let (c, t, u, k) = Some?.v (ite_eq_parts a) in
  let (x, y) = Some?.v (conjunction_parts b) in
  let (l, k') = Some?.v (eq_parts a) in
  let (c', t', u') = Some?.v (A.ite_parts l) in
  let at = R.mk_eq_expr t k in
  let au = R.mk_eq_expr u k in
  assert (ite_eq_parts a == Some (c, t, u, k));
  assert (conjunction_parts b == Some (x, y));
  assert (k == k' /\ c == c' /\ t == t' /\ u == u');
  lemma_eq_parts_normalized a l k';
  assert (D.scoped [] (R.mk_eq_expr l k'));
  assert_norm (D.scoped [] (R.mk_eq_expr l k') ==
               (D.scoped [] l && D.scoped [] k'));
  assert (D.scoped [] l /\ D.scoped [] k);
  SArray.lemma_ite_scope [] l c t u;
  assert (D.scoped [] c /\ D.scoped [] t /\ D.scoped [] u);
  assert (get_sort t == get_sort k);
  assert (get_sort u == get_sort k);
  V.lemma_sort_eq (get_sort k) (get_sort t);
  assert (sorts_match [t; k] [get_sort t; get_sort t]);
  assert_norm (D.scoped_args [] [t; k] ==
               (D.scoped [] t && D.scoped [] k));
  assert (D.scoped [] at);
  assert (sorts_match [u; k] [get_sort u; get_sort u]);
  V.lemma_sort_eq (get_sort k) (get_sort u);
  assert_norm (D.scoped_args [] [u; k] ==
               (D.scoped [] u && D.scoped [] k));
  assert (D.scoped [] au);
  lemma_conjunction_parts_scoped b x y;
  assert (D.scoped [] x /\ D.scoped [] y);
  assert (get_sort x == bool_sort /\ get_sort y == bool_sort);
  lemma_eq_atom_truth schema p m rho a l k;
  SArray.lemma_ite schema m.booleans m.scalar_model (override schema p m)
    [] rho l c t u;
  lemma_eq_atom_truth schema p m rho at t k;
  lemma_eq_atom_truth schema p m rho au u k;
  lemma_conjunction_truth schema p m rho b x y;
  let vc = truth_at schema p m [] rho c in
  let vt = truth_at schema p m [] rho at in
  let vu = truth_at schema p m [] rho au in
  let vx = truth_at schema p m [] rho x in
  lemma_ite_eq_modulus_parts p a b c t u k x y;
  if y == R.mk_not_expr c then (
    assert (atom_equivalent_at_modulus p au x);
    lemma_false_atom schema p m rho at;
    lemma_atom_equivalent_truth schema p m rho au x;
    lemma_negation_at schema p m rho R.not_decl c;
    assert (truth_at schema p m [] rho y == not vc);
    assert (vt == false /\ vu == vx);
    assert (truth_at schema p m [] rho a ==
            (if vc then vt else vu));
    assert (truth_at schema p m [] rho b == (vx && not vc)))
  else (
    assert (atom_equivalent_at_modulus p at x);
    lemma_false_atom schema p m rho au;
    lemma_atom_equivalent_truth schema p m rho at x;
    assert (vu == false /\ vt == vx);
    assert (truth_at schema p m [] rho a ==
            (if vc then vt else vu));
    assert (truth_at schema p m [] rho b == (vx && vc)))

let lemma_equivalent_sound (#base:sort -> Type0) (schema:S.checked_schema)
                           (p:pos) (m:model base schema p)
                           (rho:V.environment base (S.signature schema) [])
                           (a b:expr)
  : Lemma (requires D.scoped [] a /\ D.scoped [] b /\ equivalent a b /\
                    get_sort a == get_sort b /\
                    (term_equivalent a b ==> shared_modulus a b == Some p) /\
                    (eq_truth_equivalent a b ==> atom_modulus a == Some p) /\
                    (eq_truth_equivalent b a ==> atom_modulus b == Some p) /\
                    (eq_eq_equivalent a b ==>
                      (match atom_modulus a with
                       | Some q -> q == p
                       | None -> atom_modulus b == Some p)) /\
                    (ite_eq_equivalent a b ==> ite_eq_sound_at_modulus p a b))
          (ensures evaluate_at schema p m [] rho a ==
                   evaluate_at schema p m [] rho b) =
  if term_equivalent a b then
    lemma_term_equivalent_sound schema p m rho a b
  else if eq_eq_equivalent a b then (
    lemma_eq_eq_equivalent_sound schema p m rho a b;
    lemma_boolean_evaluations_equal schema p m rho a b)
  else if eq_truth_equivalent a b then (
    lemma_eq_truth_equivalent_sound schema p m rho a b;
    lemma_boolean_evaluations_equal schema p m rho a b)
  else if eq_truth_equivalent b a then (
    lemma_eq_truth_equivalent_sound schema p m rho b a;
    lemma_boolean_evaluations_equal schema p m rho b a)
  else (
    lemma_ite_eq_equivalent_sound schema p m rho a b;
    lemma_boolean_evaluations_equal schema p m rho a b)

(* ----------------------------------------------------------------- *)
(* Compositional soundness of exhaustive clause evaluation             *)
(* ----------------------------------------------------------------- *)

let rec residues_in_range (p:int) (xs:list int) : Tot bool (decreases xs) =
  match xs with
  | [] -> true
  | x :: rest -> 0 <= x && x < p && residues_in_range p rest

let expression_residue_at (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                           (m:model base schema p)
                           (rho:V.environment base (S.signature schema) [])
                           (tbl:list expr{D.scoped_args [] tbl}) (k:nat) : GTot int =
  let xs = expressions_residues schema p m rho tbl in
  if k < L.length xs then L.index xs k else 0

let field_agrees (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                 (m:model base schema p)
                 (rho:V.environment base (S.signature schema) [])
                 (tbl:list expr{D.scoped_args [] tbl}) (v:nat -> int) : prop =
  forall (k:nat). k < L.length tbl ==>
    v k == expression_residue_at schema p m rho tbl k

let lemma_field_leaf (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                     (m:model base schema p)
                     (rho:V.environment base (S.signature schema) [])
                     (tbl:list expr{D.scoped_args [] tbl})
                     (v:nat -> int) (e:expr) (n:int)
  : Lemma (requires field_agrees schema p m rho tbl v /\
                    D.scoped_args [] tbl /\ D.scoped [] e /\
                    leaf p tbl v e == Some n)
          (ensures residue schema p m rho e == n) =
  let k = Some?.v (index_of e tbl) in
  lemma_index_of e tbl k;
  lemma_scoped_args_index tbl k;
  lemma_expressions_residues_length schema p m rho tbl;
  assert (L.length (expressions_residues schema p m rho tbl) == L.length tbl);
  assert (k < L.length (expressions_residues schema p m rho tbl));
  lemma_expressions_residues_index schema p m rho tbl k;
  assert (field_agrees schema p m rho tbl v);
  assert (L.index tbl k == e);
  assert (leaf p tbl v e == Some (v k));
  assert (expression_residue_at schema p m rho tbl k ==
          L.index (expressions_residues schema p m rho tbl) k);
  assert (v k == expression_residue_at schema p m rho tbl k);
  assert (residue schema p m rho e == expression_residue_at schema p m rho tbl k)

#push-options "--fuel 8 --ifuel 4"
let rec lemma_eval_ff (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                      (m:model base schema p)
                      (rho:V.environment base (S.signature schema) [])
                      (tbl:list expr) (v:nat -> int) (e:expr) (n:int)
  : Lemma (requires p >= 2 /\ D.scoped [] e /\
                    D.scoped_args [] tbl /\
                    field_agrees schema p m rho tbl v /\
                    eval_ff p tbl v e == Some n)
          (ensures residue schema p m rho e == n)
          (decreases e) =
  match numeral e with
  | Some (q, k) ->
    assert (q == p /\ n == k);
    (match e with
     | App f [] -> lemma_evaluate_numeral_at schema p m [] rho f k
     | _ -> ());
    assert (residue schema p m rho e == k)
  | None ->
    (match e with
     | App f args ->
       (match operation_at f args with
        | Some (q, op) ->
          if q == p then (
            let xs = Some?.v (eval_ffs p tbl v args) in
            assert (D.scoped_args [] args);
            assert (args_have_sort p args);
            lemma_eval_ffs schema p m rho tbl v args xs;
            lemma_evaluate_operation_at schema p m [] rho f args op;
            lemma_residues_args schema p m rho args f.domain;
            assert (n == calculate p op xs);
            assert (expressions_residues schema p m rho args == xs))
        | None ->
          (match args with
           | [c; t; u] ->
             if f == A.term_ite_decl (ff_sort p) &&
                get_sort c == bool_sort && get_sort t == ff_sort p &&
                get_sort u == ff_sort p then (
               let b = Some?.v (eval_bool p tbl v c) in
               assert (D.scoped_args [] [c; t; u]);
               lemma_eval_bool schema p m rho tbl v c b;
               assert (A.ite_parts e == Some (c, t, u));
               SArray.lemma_ite schema m.booleans m.scalar_model
                 (override schema p m) [] rho e c t u;
               if b then (
                 assert (truth_at schema p m [] rho c);
                 lemma_eval_ff schema p m rho tbl v t n;
                 assert (residue schema p m rho e == residue schema p m rho t))
               else (
                 assert (not (truth_at schema p m [] rho c));
                 lemma_eval_ff schema p m rho tbl v u n;
                 assert (residue schema p m rho e == residue schema p m rho u)))
             else
               lemma_field_leaf schema p m rho tbl v e n
           | _ -> lemma_field_leaf schema p m rho tbl v e n))
     | _ -> lemma_field_leaf schema p m rho tbl v e n)

and lemma_eval_ffs (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                   (m:model base schema p)
                   (rho:V.environment base (S.signature schema) [])
                   (tbl:list expr) (v:nat -> int) (args:list expr) (xs:list int)
  : Lemma (requires p >= 2 /\ D.scoped_args [] args /\ D.scoped_args [] tbl /\
                    field_agrees schema p m rho tbl v /\
                    eval_ffs p tbl v args == Some xs)
          (ensures xs == expressions_residues schema p m rho args)
          (decreases args) =
  match args, xs with
  | a :: rest, x :: tail ->
    lemma_eval_ff schema p m rho tbl v a x;
    lemma_eval_ffs schema p m rho tbl v rest tail
  | [], [] -> ()
  | _, _ -> ()

and lemma_eval_bool (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                    (m:model base schema p)
                    (rho:V.environment base (S.signature schema) [])
                    (tbl:list expr) (v:nat -> int) (e:expr) (b:bool)
  : Lemma (requires p >= 2 /\ D.scoped [] e /\ get_sort e == bool_sort /\
                    D.scoped_args [] tbl /\
                    field_agrees schema p m rho tbl v /\
                    eval_bool p tbl v e == Some b)
          (ensures truth_at schema p m [] rho e == b)
          (decreases e) =
  match e with
  | App f args ->
    assert (D.scoped_args [] args);
    if C.canonical_true f && args == [] then (
      assert (e == R.true_expr);
      lemma_true_false_values schema p m rho;
      assert (b == true))
    else if C.canonical_false f && args == [] then (
      assert (e == R.false_expr);
      lemma_true_false_values schema p m rho;
      assert (b == false))
    else if C.canonical_not f then
      (match args with
       | [a] ->
         let ba = Some?.v (eval_bool p tbl v a) in
         lemma_eval_bool schema p m rho tbl v a ba;
         lemma_negation_at schema p m rho f a;
         assert (b == not ba)
       | _ -> ())
    else if C.canonical_or f then (
      let r = Some?.v (eval_or p tbl v args) in
      lemma_eval_or schema p m rho tbl v args r;
      lemma_canonical_or_classified f;
      lemma_nary_at schema p m rho f args B.Or;
      assert (SS.truth_at schema m.booleans m.scalar_model
                (override schema p m) [] rho (App f args) ==
              B.geval_args (SS.truth_at schema m.booleans m.scalar_model
                              (override schema p m) [] rho)
                B.Or (L.map B.Atom args));
      assert (truth_at schema p m [] rho e ==
              SS.truth_at schema m.booleans m.scalar_model
                (override schema p m) [] rho (App f args));
      assert (eval_bool p tbl v e == eval_or p tbl v args);
      assert (truth_at schema p m [] rho e == r);
      assert (b == r);
      assert (truth_at schema p m [] rho e == b))
    else if C.canonical_and f then (
      let r = Some?.v (eval_and p tbl v args) in
      lemma_eval_and schema p m rho tbl v args r;
      lemma_canonical_and_classified f;
      lemma_nary_at schema p m rho f args B.And;
      assert (SS.truth_at schema m.booleans m.scalar_model
                (override schema p m) [] rho (App f args) ==
              B.geval_args (SS.truth_at schema m.booleans m.scalar_model
                              (override schema p m) [] rho)
                B.And (L.map B.Atom args));
      assert (truth_at schema p m [] rho e ==
              SS.truth_at schema m.booleans m.scalar_model
                (override schema p m) [] rho (App f args));
      assert (eval_bool p tbl v e == eval_and p tbl v args);
      assert (truth_at schema p m [] rho e == r);
      assert (b == r);
      assert (truth_at schema p m [] rho e == b))
    else
      (match args with
       | [a; bterm] ->
         if get_sort a == ff_sort p && get_sort bterm == ff_sort p then (
           let x = Some?.v (eval_ff p tbl v a) in
           let y = Some?.v (eval_ff p tbl v bterm) in
           lemma_eval_ff schema p m rho tbl v a x;
           lemma_eval_ff schema p m rho tbl v bterm y;
           assert (e == R.mk_eq_expr a bterm);
           lemma_truth_field_eq schema p m rho a bterm;
           assert (b == (x == y)))
         else if get_sort a == bool_sort && get_sort bterm == bool_sort then (
           let x = Some?.v (eval_bool p tbl v a) in
           let y = Some?.v (eval_bool p tbl v bterm) in
           lemma_eval_bool schema p m rho tbl v a x;
           lemma_eval_bool schema p m rho tbl v bterm y;
           assert (e == R.mk_eq_expr a bterm);
           SS.lemma_boolean_equality_at schema m.booleans m.scalar_model
             (override schema p m) [] rho a bterm;
           assert (b == (x == y)))
         else ()
       | _ -> ())
  | _ -> ()

and lemma_eval_or (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                  (m:model base schema p)
                  (rho:V.environment base (S.signature schema) [])
                  (tbl:list expr) (v:nat -> int) (args:list expr) (b:bool)
  : Lemma (requires p >= 2 /\ D.scoped_args [] args /\ D.scoped_args [] tbl /\
                    field_agrees schema p m rho tbl v /\
                    eval_or p tbl v args == Some b)
          (ensures b == B.geval_args
                    (SS.truth_at schema m.booleans m.scalar_model
                      (override schema p m) [] rho)
                    B.Or (L.map B.Atom args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    let x = Some?.v (eval_bool p tbl v a) in
    let y = Some?.v (eval_or p tbl v rest) in
    lemma_eval_bool schema p m rho tbl v a x;
    lemma_eval_or schema p m rho tbl v rest y;
    assert (SS.truth_at schema m.booleans m.scalar_model
              (override schema p m) [] rho a == x);
    assert_norm (B.geval_args
                   (SS.truth_at schema m.booleans m.scalar_model
                     (override schema p m) [] rho) B.Or
                   (L.map B.Atom (a :: rest)) ==
                 (SS.truth_at schema m.booleans m.scalar_model
                    (override schema p m) [] rho a ||
                  B.geval_args (SS.truth_at schema m.booleans m.scalar_model
                    (override schema p m) [] rho) B.Or
                    (L.map B.Atom rest)));
    assert (b == (x || y))

and lemma_eval_and (#base:sort -> Type0) (schema:S.checked_schema) (p:pos)
                   (m:model base schema p)
                   (rho:V.environment base (S.signature schema) [])
                   (tbl:list expr) (v:nat -> int) (args:list expr) (b:bool)
  : Lemma (requires p >= 2 /\ D.scoped_args [] args /\ D.scoped_args [] tbl /\
                    field_agrees schema p m rho tbl v /\
                    eval_and p tbl v args == Some b)
          (ensures b == B.geval_args
                    (SS.truth_at schema m.booleans m.scalar_model
                      (override schema p m) [] rho)
                    B.And (L.map B.Atom args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    let x = Some?.v (eval_bool p tbl v a) in
    let y = Some?.v (eval_and p tbl v rest) in
    lemma_eval_bool schema p m rho tbl v a x;
    lemma_eval_and schema p m rho tbl v rest y;
    assert (SS.truth_at schema m.booleans m.scalar_model
              (override schema p m) [] rho a == x);
    assert_norm (B.geval_args
                   (SS.truth_at schema m.booleans m.scalar_model
                     (override schema p m) [] rho) B.And
                   (L.map B.Atom (a :: rest)) ==
                 (SS.truth_at schema m.booleans m.scalar_model
                    (override schema p m) [] rho a &&
                  B.geval_args (SS.truth_at schema m.booleans m.scalar_model
                    (override schema p m) [] rho) B.And
                    (L.map B.Atom rest)));
    assert (b == (x && y))
#pop-options

let rec lemma_leaves_args_scoped (p:int) (tbl args:list expr)
  : Lemma (requires D.scoped_args [] tbl /\ D.scoped_args [] args)
          (ensures D.scoped_args [] (leaves_args p tbl args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    assert (D.scoped [] a);
    lemma_leaves_scoped p tbl a;
    lemma_leaves_args_scoped p (leaves p tbl a) rest

and lemma_leaves_scoped (p:int) (tbl:list expr) (e:expr)
  : Lemma (requires D.scoped_args [] tbl /\ D.scoped [] e)
          (ensures D.scoped_args [] (leaves p tbl e))
          (decreases e) =
  match numeral e with
  | Some _ -> ()
  | None ->
    (match e with
     | App f args ->
       if Some? (operation_at f args) || get_sort e <> ff_sort p ||
          Some? (A.ite_parts e)
       then (
         assert (D.scoped_args [] args);
         lemma_leaves_args_scoped p tbl args)
       else if L.mem e tbl then ()
       else lemma_scoped_append_single tbl e
     | _ ->
       if get_sort e == ff_sort p && not (L.mem e tbl)
       then lemma_scoped_append_single tbl e)

let rec lemma_residues_range (#base:sort -> Type0) (schema:S.checked_schema)
                             (p:pos) (m:model base schema p)
                             (rho:V.environment base (S.signature schema) [])
                             (tbl:list expr)
  : Lemma (requires D.scoped_args [] tbl /\ L.for_all (closed_ff p) tbl)
          (ensures residues_in_range p
                    (expressions_residues schema p m rho tbl))
          (decreases tbl) =
  match tbl with
  | [] -> ()
  | e :: rest ->
    m.project_range (evaluate_at schema p m [] rho e);
    lemma_residues_range schema p m rho rest

let rec power (p:int) (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else p * power p (n - 1)

let rec lemma_for_all_vectors (p:nat) (n:nat) (f:list int -> bool) (r:list int)
  : Lemma (requires for_all_vectors p n f /\ L.length r == n /\
                    residues_in_range p r)
          (ensures f r)
          (decreases %[n; 0; 0]) =
  match r with
  | [] -> ()
  | x :: rest -> lemma_for_all_heads p p (n - 1) f x rest

and lemma_for_all_heads (p:nat) (k:nat) (n:nat) (f:list int -> bool)
                        (x:int) (rest:list int)
  : Lemma (requires for_all_heads p k n f /\ 0 <= x /\ x < k /\
                    L.length rest == n /\ residues_in_range p rest)
          (ensures f (x :: rest))
          (decreases %[n; 1; k]) =
  if x == k - 1 then
    lemma_for_all_vectors p n (with_head f (k - 1)) rest
  else
    lemma_for_all_heads p (k - 1) n f x rest

let lemma_field_agrees_residues (#base:sort -> Type0) (schema:S.checked_schema)
                                (p:pos) (m:model base schema p)
                                (rho:V.environment base (S.signature schema) [])
                                (tbl:list expr)
  : Lemma (requires D.scoped_args [] tbl)
          (ensures field_agrees schema p m rho tbl
                    (vector_value (expressions_residues schema p m rho tbl))) =
  let aux (k:nat)
    : Lemma (k < L.length tbl ==>
             vector_value (expressions_residues schema p m rho tbl) k ==
             expression_residue_at schema p m rho tbl k) =
    if k < L.length tbl then (
      lemma_expressions_residues_length schema p m rho tbl;
      assert (k < L.length (expressions_residues schema p m rho tbl));
      assert (vector_value (expressions_residues schema p m rho tbl) k ==
              L.index (expressions_residues schema p m rho tbl) k);
      assert (expression_residue_at schema p m rho tbl k ==
              L.index (expressions_residues schema p m rho tbl) k))
  in
  FStar.Classical.forall_intro aux

let lemma_exhaustive_clause_sound (#base:sort -> Type0) (schema:S.checked_schema)
                                  (p:pos) (m:model base schema p)
                                  (rho:V.environment base (S.signature schema) [])
                                  (e:expr)
  : Lemma (requires exhaustive_clause e /\ find_modulus e == Some p /\
                    D.scoped [] e /\ get_sort e == bool_sort)
          (ensures truth_at schema p m [] rho e) =
  let tbl = leaves p [] e in
  assert (p >= 2);
  lemma_leaves_scoped p [] e;
  assert (D.scoped_args [] tbl);
  assert (within_budget p (L.length tbl) 1);
  assert (L.for_all (closed_ff p) tbl);
  assert (for_all_vectors p (L.length tbl) (clause_true p tbl e) == true);
  let r = expressions_residues schema p m rho tbl in
  lemma_expressions_residues_length schema p m rho tbl;
  lemma_residues_range schema p m rho tbl;
  assert (residues_in_range p r);
  lemma_for_all_vectors p (L.length tbl) (clause_true p tbl e) r;
  lemma_field_agrees_residues schema p m rho tbl;
  let v = vector_value r in
  assert (field_agrees schema p m rho tbl v);
  assert (clause_true p tbl e r);
  assert (eval_bool p tbl v e == Some true);
  lemma_eval_bool schema p m rho tbl v e true

