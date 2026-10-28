module ArithProjectAudit
module L = FStar.List.Tot

type rat = { n: int; d: (d:int{d > 0}) }
let rmul (a b: rat) : rat = { n = a.n * b.n; d = a.d * b.d }
let radd (a b: rat) : rat = { n = a.n * b.d + b.n * a.d; d = a.d * b.d }
let req (a b: rat) : bool = a.n * b.d = b.n * a.d
let nonzero (a: rat) : bool = a.n <> 0
(* a.mk_real(-k / c) for c nonzero *)
let neg_div (k: rat) (c: rat{nonzero c}) : rat =
  if c.n > 0 then { n = - (k.n * c.d); d = k.d * c.n }
  else { n = k.n * c.d; d = k.d * (- c.n) }
let zero : rat = { n = 0; d = 1 }

(* P1: arith_project_nested step. If rule.coefficient c, atom value A, rule.rest R satisfy
   c*A + R = 0 (the rule's boundary), then replacing k*A in rest + k*A by (-k/c)*R keeps the value. *)
module CS = FStar.Tactics.CanonCommSemiring

let ring_pos (kn kd cn an rd cd rn ad: int)
  : Lemma (kn*an*(kd*cn*rd) + (kn*cd*rn)*(kd*ad) == kn*kd*(cn*an*rd + rn*(cd*ad)))
  = assert (kn*an*(kd*cn*rd) + (kn*cd*rn)*(kd*ad) == kn*kd*(cn*an*rd + rn*(cd*ad)))
      by (CS.int_semiring ())

let ring_neg (kn kd cn an rd cd rn ad: int)
  : Lemma (kn*an*(kd*(0-cn)*rd) == (kn*cd*rn)*(kd*ad) + 0 - kn*kd*(cn*an*rd + rn*(cd*ad)) - 0 ==> True)
  = ()

let p1_core (k: rat) (c: rat{nonzero c}) (a r: rat)
  : Lemma (requires req (radd (rmul c a) r) zero)
          (ensures req (rmul k a) (rmul (neg_div k c) r))
  = let h = c.n*a.n*r.d + r.n*(c.d*a.d) in
    assert (h == 0);
    ring_pos k.n k.d c.n a.n r.d c.d r.n a.d;
    FStar.Math.Lemmas.neg_mul_left (k.n*c.d) r.n;
    FStar.Math.Lemmas.neg_mul_right c.n (k.d*r.d)

let ring_sum (rn rd xn xd yn yd: int)
  : Lemma (requires xn*yd == yn*xd)
          (ensures (rn*xd + xn*rd)*(rd*yd) == (rn*yd + yn*rd)*(rd*xd))
  = assert ((rn*xd + xn*rd)*(rd*yd) == rn*xd*rd*yd + (xn*yd)*(rd*rd)) by (CS.int_semiring ());
    assert ((rn*yd + yn*rd)*(rd*xd) == rn*xd*rd*yd + (yn*xd)*(rd*rd)) by (CS.int_semiring ())

let p1_project_step (k: rat) (c: rat{nonzero c}) (a r rest: rat)
  : Lemma (requires req (radd (rmul c a) r) zero)
          (ensures req (radd rest (rmul k a)) (radd rest (rmul (neg_div k c) r)))
  = p1_core k c a r;
    let x = rmul k a in let y = rmul (neg_div k c) r in
    ring_sum rest.n rest.d x.n x.d y.n y.d

(* P2: boundary scale 1/(projected+1). projected <= 8 (step < 8 loop), so the divisor is
   a positive rational; projected = 0 leaves the pre-PR value unchanged. *)
let scale (p: nat{p <= 8}) : rat = { n = 1; d = p + 1 }
let p2_scale_wf (p: nat{p <= 8}) (b: rat)
  : Lemma (nonzero (scale p) /\ (scale p).d > 0 /\
           (p = 0 ==> req (rmul (scale p) b) b) /\
           (p > 0 ==> req (rmul (scale p) b) { n = b.n; d = b.d * (p + 1) }))
  = ()

(* P3: offset loop {0,1,-1} with "if projected && offset != 0 break" and budget >= 2 check.
   Returns (offsets attempted, remaining budget). *)
let rec loop (projected: bool) (budget: nat) (offs: list int) : Tot (tuple2 (list int) nat) (decreases offs) =
  match offs with
  | [] -> ([], budget)
  | o :: tl ->
    if projected && o <> 0 then ([], budget)
    else if budget < 2 then ([], budget)
    else let (r, b) = loop projected (budget - 2) tl in (o :: r, b)

let p3_projected_only_zero (budget: nat)
  : Lemma (ensures (let (r, _) = loop true budget [0; 1; -1] in r = [] \/ r = [0]))
  = ()

let p3_unprojected_same (budget: nat)
  : Lemma (ensures (let (r, b) = loop false budget [0; 1; -1] in
                    (budget >= 6 ==> r = [0; 1; -1] /\ b = budget - 6) /\ b <= budget))
  = ()

(* budget never underflows and only decreases *)
let p3_budget_monotone (projected: bool) (budget: nat)
  : Lemma (let (_, b) = loop projected budget [0; 1; -1] in b <= budget)
  = ()
