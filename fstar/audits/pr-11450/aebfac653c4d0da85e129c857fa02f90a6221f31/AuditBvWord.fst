module AuditBvWord

module M = FStar.Math.Lemmas

(* O1: bvsub a b = bvadd a (bvmul ones b) modulo p = 2^w, with ones = p-1. *)
let o1 (p:pos) (a b:nat)
  : Lemma (requires a < p /\ b < p)
          (ensures (a - b) % p == (a + ((p - 1) * b) % p) % p)
  = let c = (p - 1) * b in
    M.lemma_mod_add_distr a c p;
    M.distributivity_sub_left p 1 b;
    M.swap_mul p b;
    assert (a + c == (a - b) + b * p);
    M.lemma_mod_plus (a - b) b p

(* O2: concat-vs-numeral equality splits into two equalities.
   x < pl (left of width lw), y < p (right of width rw), n < p*pl, p)0. *)
let o2 (p pl:pos) (x y n:nat)
  : Lemma (requires x < pl /\ y < p /\ n < p * pl)
          (ensures (x * p + y == n) <==> (x == n / p /\ y == n % p))
  = M.lemma_div_mod n p;
    M.lemma_div_plus y x p;
    M.lemma_mod_plus y x p;
    M.small_div y p;
    M.small_mod y p

(* O3: ripple-carry sum: pa+pb = s + p*ov with s<p, ov in {0,1} gives (pa+pb)%p = s. *)
let o3 (p:pos) (s ov pa pb:nat)
  : Lemma (requires s < p /\ (ov == 0 \/ ov == 1) /\ pa + pb == s + p * ov)
          (ensures (pa + pb) % p == s)
  = M.lemma_mod_plus s ov p; M.small_mod s p
