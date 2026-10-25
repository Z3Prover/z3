module Z3FpaWrappedUf11320

(* Audit of PR 11320 fpa2bv_converter_wrapped::mk_uf, head 15695a7e.
   O1: float unwrap (extract sgn/exp/sig) of a w-bit wrapped value
       rejoined by concat (wrap/mk_fp semantics) is the identity.
   O2: bit-field widths of the three extracts partition ebits+sbits.
   O3: RM unwrap ite-chain is total, decodes codes 0..4 correctly
       (BV_RM_TIES_TO_EVEN=0, TIES_TO_AWAY=1, TO_POSITIVE=2,
       TO_NEGATIVE=3, TO_ZERO=4) and maps 5..7 to RTZ. *)

let pow2 = Prims.pow2
let pow2_add (a b:nat) : Lemma (pow2 (a + b) = pow2 a * pow2 b) = FStar.Math.Lemmas.pow2_plus a b

(* extract(hi,lo) of a bit-vector value x: (x / 2^lo) mod 2^(hi-lo+1) *)
let extract (hi lo:nat{hi >= lo}) (x:nat) : nat = (x / pow2 lo) % pow2 (hi - lo + 1)

(* unwrap for floats; w = ebits+sbits, sbits>=2, ebits>=2 *)
let sgn_of (e s:nat{e >= 2 /\ s >= 2}) (w:nat) = extract (e+s-1) (e+s-1) w
let exp_of (e s:nat{e >= 2 /\ s >= 2}) (w:nat) = extract (e+s-2) (s-1) w
let sig_of (e s:nat{e >= 2 /\ s >= 2}) (w:nat) = extract (s-2) 0 w

let concat3 (e s:nat{e >= 2 /\ s >= 2}) (a b c:nat) : nat =
  a * (pow2 e * pow2 (s-1)) + b * pow2 (s-1) + c

(* O1 *)
let o1 (e s:nat{e >= 2 /\ s >= 2}) (w:nat{w < pow2 (e+s)})
  : Lemma (concat3 e s (sgn_of e s w) (exp_of e s w) (sig_of e s w) = w)
  = pow2_add e (s-1);
    pow2_add (e+s-1) 1;
    let p = pow2 (s-1) in
    let q = pow2 e in
    assert (pow2 (e+s-1) = q * p);
    assert (pow2 (e+s) = 2 * (q * p));
    assert (pow2 1 = 2);
    assert (pow2 (e+s-1-(s-1)) = q);
    FStar.Math.Lemmas.division_multiplication_lemma w p q;
    FStar.Math.Lemmas.lemma_div_lt w (e+s) (e+s-1);
    FStar.Math.Lemmas.small_mod (w / (p*q)) 2;
    FStar.Math.Lemmas.euclidean_division_definition w p;
    FStar.Math.Lemmas.euclidean_division_definition (w / p) q

(* O2: widths *)
let o2 (e s:nat{e >= 2 /\ s >= 2})
  : Lemma ((e+s-1) - (e+s-1) + 1 + ((e+s-2) - (s-1) + 1) + ((s-2) - 0 + 1) = e + s)
  = ()

(* O3 *)
type rm = | RNE | RNA | RTP | RTN | RTZ

let unwrap_rm (b:nat{b < 8}) : rm =
  let r = RTZ in
  let r = if b = 2 then RTP else r in
  let r = if b = 3 then RTN else r in
  let r = if b = 0 then RNE else r in
  let r = if b = 1 then RNA else r in
  r

let code (r:rm) : (b:nat{b < 8}) =
  match r with RNE -> 0 | RNA -> 1 | RTP -> 2 | RTN -> 3 | RTZ -> 4

let o3_roundtrip (r:rm) : Lemma (unwrap_rm (code r) = r) = ()

let o3_total (b:nat{b < 8})
  : Lemma (b >= 5 ==> unwrap_rm b = RTZ) = ()
