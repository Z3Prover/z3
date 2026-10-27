module Z3PR11358FfAudit
(* Independent obligations for PR #11358 (Z3FiniteFieldLemma.fst at af02798e).
   Self-contained: re-states the integer-level definitions of the PR's
   bitsum_mod / neg / same_zero_set guard and proves their laws. The PR's own
   module is not imported or trusted. *)
module M = FStar.Math.Lemmas
module L = FStar.List.Tot

(* O1: bitsum_mod (PR: Z3FiniteFieldLemma.bitsum_mod) equals the exact sum
   x0*w + x1*2w + ... reduced mod p. *)
let rec bitsum_mod (p:pos) (w:int) (xs:list int) : Tot int (decreases xs) =
  match xs with
  | [] -> 0
  | x :: rest -> (x * w + bitsum_mod p (2 * w) rest) % p

let rec bitsum_exact (w:int) (xs:list int) : Tot int (decreases xs) =
  match xs with
  | [] -> 0
  | x :: rest -> x * w + bitsum_exact (2 * w) rest

let rec lemma_bitsum (p:pos) (w:int) (xs:list int)
  : Lemma (ensures bitsum_mod p w xs == bitsum_exact w xs % p) (decreases xs)
  = match xs with
    | [] -> ()
    | x :: rest ->
      lemma_bitsum p (2 * w) rest;
      M.lemma_mod_plus_distr_r (x * w) (bitsum_exact (2 * w) rest) p

(* O2: negation yields a canonical residue that is the additive inverse. *)
let ff_neg (p:pos) (x:int) : int = (0 - x) % p

let lemma_neg (p:pos) (x:int)
  : Lemma (0 <= ff_neg p x /\ ff_neg p x < p /\ (x + ff_neg p x) % p == 0)
  = M.lemma_mod_plus_distr_r x (0 - x) p

(* O3: the same_zero_set unit-multiple branch. If d1 = k*d2 and d2 = w*d1
   (mod p, for any p, prime or not), then d1 and d2 vanish together. *)
let lemma_scaled_zero (p:pos) (y x k:int)
  : Lemma (requires (y - k * x) % p == 0)
          (ensures x % p == 0 ==> y % p == 0)
  = M.lemma_mod_mul_distr_r k x p;
    M.lemma_mod_sub_distr y (k * x) p

let lemma_same_zero (p:pos) (d1 d2 k w:int)
  : Lemma (requires (d1 - k * d2) % p == 0 /\ (d2 - w * d1) % p == 0)
          (ensures d1 % p == 0 <==> d2 % p == 0)
  = lemma_scaled_zero p d1 d2 k;
    lemma_scaled_zero p d2 d1 w
