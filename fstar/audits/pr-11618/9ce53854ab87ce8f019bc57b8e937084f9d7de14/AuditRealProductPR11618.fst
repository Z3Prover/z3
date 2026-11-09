module AuditRealProductPR11618
open FStar.Real

let ob1 (x y:real) : Lemma (requires x >. 0.0R /\ y >. 0.0R) (ensures x *. y >. 0.0R) = ()

let ob2 (x y:real)
  : Lemma (requires (x >=. 0.0R /\ y <=. 0.0R) \/ (x <=. 0.0R /\ y >=. 0.0R))
          (ensures x *. y <=. 0.0R) = ()

let ob3 (facts:prop) (x y p:real)
  : Lemma (requires facts /\ (facts ==> x >. 0.0R) /\ (facts ==> y >. 0.0R) /\
                    p == x *. y /\ ((p >. 0.0R) ==> False))
          (ensures False) = ()
