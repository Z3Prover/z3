module Z3OptCurveCertificate

(* basis[j] of opt_curve_certificate.cpp::certify: j*b_j = b_{j-1}*(t+j-1) *)
let rec h2 (t:nat) : Tot int (decreases t) = if t = 0 then 0 else h2 (t-1) + t
let rec h3 (t:nat) : Tot int (decreases t) = if t = 0 then 0 else h3 (t-1) + h2 t

(* O1: the integer witnesses exist for every t >= 0 and satisfy the emitted constraints *)
let rec h2_ok (t:nat) : Lemma (ensures 2 * h2 t == 1 * t * (t + 1)) (decreases t) =
  if t = 0 then () else h2_ok (t-1)
let rec h3_ok (t:nat) : Lemma (ensures 3 * h3 t == h2 t * (t + 2)) (decreases t) =
  if t = 0 then () else (h3_ok (t-1); h2_ok t; h2_ok (t-1))

(* O2: Newton backward form interpolates the last four models (degree 3 case),
   with B1=t, B2=h2, B3=h3 evaluated at t = 0,-1,-2,-3 (6*B3 = t(t+1)(t+2), 2*B2 = t(t+1)). *)
let d1 (f0 f1:int) = f0 - f1
let d2 (f0 f1 f2:int) = f0 - 2*f1 + f2
let d3 (f0 f1 f2 f3:int) = f0 - 3*f1 + 3*f2 - f3
let sp3 (f0 f1 f2 f3 t:int) =
  6*f0 + 6 * d1 f0 f1 * t + 3 * d2 f0 f1 f2 * (t*(t+1)) + d3 f0 f1 f2 f3 * (t*(t+1)*(t+2))
let interp (f0 f1 f2 f3:int)
  : Lemma (sp3 f0 f1 f2 f3 0 == 6*f0 /\ sp3 f0 f1 f2 f3 (-1) == 6*f1 /\
           sp3 f0 f1 f2 f3 (-2) == 6*f2 /\ sp3 f0 f1 f2 f3 (-3) == 6*f3) = ()

(* O3: ray case: p(t)=c0+c1*t, p(t)>=c0 for t>=0 and nonconstant (p(t1)<>c0, t1>=1)
   implies unbounded above. *)
let ray_unbounded (c0 c1 t1 m:int)
  : Lemma (requires t1 >= 1 /\ c0 + c1*t1 >= c0 /\ c0 + c1*t1 <> c0)
          (ensures (exists (t:int). t >= 0 /\ c0 + c1*t > m))
  = let abs (x:int) = if x < 0 then -x else x in
    assert (c1 > 0);
    let t = abs m + abs c0 + 1 in
    assert (t >= 0);
    assert (c1*t >= t)
