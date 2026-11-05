module Z3FmaSmallSig
(* Model of the extraction step of mpf_manager::fma (src/util/mpf.cpp, head 59fc59af, ~l.921-929).
   After renormalisation res.significand = S, 2s+3 bits, value S * 2^(e-(2s+2)).
   Extracted o has significand m (s+4 bits incl. 3 guard bits), value m * 2^(e'-(s+3)).
   Both sides are scaled by 2^20 so everything stays an integer. *)

let rec p2 (n:nat) : pos = if n = 0 then 1 else 2 * p2 (n-1)

let true_val (s:nat{s>=2 /\ s<=6}) (sg:int) : int = sg * p2 (20 - (2*s+2))
(* value of o given m and exponent offset d = e'-e, d<=0 ; need 20+d-(s+3) >= 0 *)
let cand_val (s:nat{s>=2 /\ s<=6}) (nd:nat{20 - nd - (s+3) >= 0}) (m:int) : int =
  m * p2 (20 - nd - (s+3))

(* base code for s<4: m = S * 2^(4-s+3), exponent -= 4-s+3 *)
let old_m (s:nat{s<4}) (sg:int) : int = sg * p2 (4 - s + 3)

let rec p2_add (a b:nat) : Lemma (p2 (a+b) = p2 a * p2 b) (decreases a) =
  if a = 0 then () else p2_add (a-1) b

(* Obligation 1 (counterexample on base): FP(2,3) has s=3; any positive S is mis-scaled
   by factor 2^(s-1)=4. Witness: S = 1536 (= 1.5*2^10, i.e. 1.5 at s=3 alignment). *)
let witness_base_s3 () : Lemma
  (cand_val 3 4 (old_m 3 1536) = 4 * true_val 3 1536 /\ cand_val 3 4 (old_m 3 1536) <> true_val 3 1536)
  = assert_norm (p2 8 = 256); assert_norm (p2 12 = 4096); assert_norm (p2 4 = 16);
    assert_norm (p2 10 = 1024); assert_norm (p2 14 = 16384); assert_norm (p2 13 = 8192);
    assert_norm (p2 3 = 8);  assert_norm (p2 6 = 64); assert_norm (p2 9 = 512)

(* same for s=2 (FP(*,2)), nd = 4-s+3 = 5 *)
let witness_base_s2 () : Lemma
  (cand_val 2 5 (old_m 2 1024) = 2 * true_val 2 1024 /\ cand_val 2 5 (old_m 2 1024) <> true_val 2 1024)
  = assert_norm (p2 10 = 1024); assert_norm (p2 12 = 4096); assert_norm (p2 14 = 16384);
    assert_norm (p2 5 = 32); assert_norm (p2 8 = 256); assert_norm (p2 9 = 512); assert_norm (p2 13 = 8192);
    assert_norm (p2 6 = 64); assert_norm (p2 7 = 128); assert_norm (p2 11 = 2048)

(* Obligation 2 (head): extraction m = S / 2^(s-1) with exponent unchanged is value-exact
   when the discarded bits are zero, for all s in 2..6, all q>=0. *)
let head_exact (s:nat{s>=2 /\ s<=6}) (q:nat) : Lemma
  (cand_val s 0 ((q * p2 (s-1)) / p2 (s-1)) = true_val s (q * p2 (s-1)))
  = FStar.Math.Lemmas.cancel_mul_div q (p2 (s-1));
    p2_add (s-1) (20 - (s+3) - (s-1))
