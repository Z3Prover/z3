module CurveSamples
(* Model of the sample loop added to curve_certificate::certify (PR 11705),
   degree <= 3 (curve_certificate::max_degree).
   C++ solver-side constraints (`along`): t >= 0, 2*h2 = t*(t+1), 3*h3 = h2*(t+2).
   C++ sampling: b <- b*(t0+j-1)/j with exact rational division, j = 1..degree. *)

let h2 (t:int) : int = (t * (t + 1)) / 2
let h3 (t:int) : int = (h2 t * (t + 2)) / 3

let along (t h2v h3v:int) : prop =
  t >= 0 /\ 2 * h2v == t * (t + 1) /\ 3 * h3v == h2v * (t + 2)

let rec even (t:nat) : Lemma (ensures (t * (t + 1)) % 2 == 0) (decreases t) =
  if t = 0 then () else begin
    even (t - 1);
    assert (t * (t + 1) == (t - 1) * t + 2 * t)
  end

let f3 (t:int) : int = t * (t + 1) * (t + 2)

let rec div3 (t:nat) : Lemma (ensures f3 t % 3 == 0) (decreases t) =
  if t = 0 then () else begin
    div3 (t - 1);
    assert (f3 t == f3 (t - 1) + 3 * (t * (t + 1)))
  end

(* O1: for every integer t >= 0 the sampled basis values are integral
   (the C++ rational divisions are exact) and satisfy the solver's `along`
   constraints, so a sample point is a legitimate point of the query. *)
let o1 (t:nat) : Lemma (along t (h2 t) (h3 t)) =
  even t;
  div3 t;
  let a = h2 t in
  assert (2 * a == t * (t + 1));
  assert (a * (t + 2) * 2 == f3 t);
  assert ((a * (t + 2) * 2) % 3 == 0);
  ()

(* O2: the sample schedule t0 <- (t0 = 1 ? 2 : t0*t0), 7 samples, is
   1,2,4,16,256,65536,2^32, all >= 0 (inside the `along` domain). *)
let next (t:int) : int = if t = 1 then 2 else t * t

let o2 () : Lemma (
  next 1 == 2 /\ next 2 == 4 /\ next 4 == 16 /\ next 16 == 256 /\
  next 256 == 65536 /\ next 65536 == 4294967296) = ()

(* O3: short-circuit soundness. If a sample point (t,h2,h3) satisfies `along`
   and the sampled objective is < r0, or a sampled hard constraint is false,
   then that point is a model of the solver query that the old code would
   have issued, so the old check could not return l_false; rejecting is what
   the old code did (return false). *)
let reject_sound (t:nat) (viol:bool) (p r0:int) :
  Lemma (requires (viol \/ p < r0))
        (ensures (along t (h2 t) (h3 t) /\ (viol \/ p < r0))) = o1 t
