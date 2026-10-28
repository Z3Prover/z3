module ArithScaledAudit

(* Rationals num/den with den > 0; equality by cross multiplication *)
type rat = { n: int; d: (d:int{d > 0}) }
let rmul (a b: rat) : rat = { n = a.n * b.n; d = a.d * b.d }
let req (a b: rat) : bool = a.n * b.d = b.n * a.d
let zero : rat = { n = 0; d = 1 }
let rge0 (a: rat) : bool = a.n >= 0
let rneg (a: rat) : rat = { n = - a.n; d = a.d }
(* magnitude = ite(scale >= 0, scale, -scale) *)
let mag (s: rat) : rat = if rge0 s then s else rneg s
(* denominator = 1 + magnitude *)
let denom (s: rat) : rat = let m = mag s in { n = m.d + m.n; d = m.d }
(* a.mk_div(m, denom): m / denom, valid when denom.n > 0 *)
let rdiv (m: rat) (x: rat{x.n > 0}) : rat = { n = m.n * x.d; d = m.d * x.n }

(* S1: denominator is always strictly positive, so mk_div never divides by zero. *)
let s1_denom_pos (s: rat) : Lemma (ensures (denom s).n > 0 /\ (denom s).d > 0) = ()

(* S2: shared monomial. monomial = s * r (scale factors removed from the flattened product
   leave r); emitted term r equals monomial / s whenever s <> 0. *)
let div_nz (m: rat) (x: rat{x.n <> 0}) : rat =
  if x.n > 0 then { n = m.n * x.d; d = m.d * x.n } else { n = - (m.n * x.d); d = m.d * (- x.n) }

let s2_shared (s: rat{s.n <> 0}) (r: rat)
  : Lemma (req (div_nz (rmul s r) s) r)
  = ()

(* S3: non-shared monomial m becomes m/(1+|s|): same sign as m (nonzero-ness and sign kept). *)
let s3_sign (m s: rat)
  : Lemma (let q = rdiv m (denom s) in
           (m.n = 0 <==> q.n = 0) /\ (m.n > 0 <==> q.n > 0) /\ (m.n < 0 <==> q.n < 0))
  = ()

(* S3b: NOT a division identity: with s = 1, m = 1 the hint is 1/2 while m/s = 1. *)
let s3_not_identity () : Lemma (let q = rdiv ({n=1;d=1}) (denom {n=1;d=1}) in
                             ~(req q {n=1;d=1}))
  = ()
