module DomainSelects

(* Model of the mixed-radix enumeration in assert_domain_selects (sat) and
   instantiate_domain_selects (smt): s = per-dimension domain sizes. *)
let rec prod (s:list pos) : pos = match s with [] -> 1 | x::t -> x * prod t

(* args.push_back(vals[r % size]); r /= size *)
let rec decode (s:list pos) (r:nat) : list nat =
  match s with [] -> [] | x::t -> (r % x) :: decode t (r / x)

let rec encode (s:list pos) (d:list nat) : nat =
  match s, d with
  | x::t, a::u -> a + x * encode t u
  | _ -> 0

let rec inb (s:list pos) (d:list nat) : bool =
  match s, d with
  | [], [] -> true
  | x::t, a::u -> a < x && inb t u
  | _ -> false

let rec decode_len (s:list pos) (r:nat) : Lemma (ensures List.length (decode s r) == List.length s) =
  match s with [] -> () | x::t -> decode_len t (r / x)

(* O1: each k < total yields an in-range index tuple *)
let rec decode_inrange (s:list pos) (r:nat{r < prod s})
  : Lemma (ensures inb s (decode s r)) (decreases s) =
  match s with
  | [] -> ()
  | x::t -> decode_inrange t (r / x)

(* O2: every in-range tuple d is produced by some k < total (full coverage) *)
let rec encode_bound (s:list pos) (d:list nat{inb s d})
  : Lemma (ensures encode s d < prod s) (decreases s) =
  match s, d with
  | [], [] -> ()
  | x::t, a::u -> encode_bound t u

let rec roundtrip (s:list pos) (d:list nat{inb s d})
  : Lemma (ensures decode s (encode s d) == d) (decreases s) =
  match s, d with
  | [], [] -> ()
  | x::t, a::u ->
    roundtrip t u;
    FStar.Math.Lemmas.lemma_mod_plus a (encode t u) x;
    FStar.Math.Lemmas.small_mod a x;
    FStar.Math.Lemmas.lemma_div_plus a (encode t u) x;
    FStar.Math.Lemmas.small_div a x

(* O3: C++ guard: after each dimension, tot<=32 else return false; each size<=32,
   so the unsigned product never exceeds 32*32 = 1024 (no 32-bit overflow). *)
let step_ok (tot:pos{tot <= 32}) (sz:pos{sz <= 32}) : Lemma (tot * sz <= 1024) = ()

(* Domain sizes used: bool 2, bv(n<=5) 2^n <= 32, enum = #constructors (checked via total). *)
let bv_size_ok (n:nat{n <= 5}) : Lemma (pow2 n >= 1 /\ pow2 n <= 32) =
  assert_norm (pow2 5 == 32);
  FStar.Math.Lemmas.pow2_le_compat 5 n
