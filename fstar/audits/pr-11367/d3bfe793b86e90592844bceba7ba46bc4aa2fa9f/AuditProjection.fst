module AuditProjection
(* Arithmetic model of PR #11367 projection semantics, independent of PR proof modules.
   bit n b  models: bvule 1 (extract b b n)  with extract = (n / 2^b) % 2. *)
module M = FStar.Math.Lemmas

let rec bits_number (bs:list bool) : Tot nat (decreases bs) =
  match bs with [] -> 0 | b :: r -> (if b then 1 else 0) + 2 * bits_number r

let ule (a b:nat) : bool = a <= b
let extract_bit (n:nat) (b:nat) : nat = (n / pow2 b) % 2
let projection (n b:nat) : bool = ule 1 (extract_bit n b)

let rec projection_bits (n start count:nat) : Tot (list bool) (decreases count) =
  if count = 0 then [] else projection n start :: projection_bits n (start+1) (count-1)

(* O1: bvule 1 x on a 1-bit value is exactly x <> 0 *)
let o1 (n b:nat) : Lemma (projection n b == (extract_bit n b <> 0)) = ()

(* O2: reconstruction: the projected bits of n, from start, number n / 2^start when n < 2^(start+count) *)
let rec o2 (n start count:nat)
  : Lemma (requires n < pow2 (start + count))
          (ensures List.Tot.length (projection_bits n start count) == count /\
                   bits_number (projection_bits n start count) == n / pow2 start)
          (decreases count)
  = if count = 0 then M.small_div n (pow2 start)
    else begin
      o2 n (start+1) (count-1);
      M.pow2_plus start 1;
      M.division_multiplication_lemma n (pow2 start) 2;
      M.lemma_div_mod (n / pow2 start) 2
    end
