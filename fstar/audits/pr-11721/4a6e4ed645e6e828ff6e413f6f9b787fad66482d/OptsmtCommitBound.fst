module OptsmtCommitBound
(* Model of optsmt::commit_assignment extra bound (PR 11721, head 4a6e4ed6).
   A rational a/d (d>0) is the finite lower bound lo with zero infinitesimal.
   Objective values are modelled as integers (Int objective) or as rationals
   x/y (y>0) (Real objective), compared by cross-multiplication. *)

let ceil_div (n:int) (d:pos) : int = (n + d - 1) / d

(* O1: Int objective: original bound x >= n/d is equivalent to the added
   bound x >= ceil(n/d); the new assertion is implied, so no model is lost. *)
let o1 (x:int) (n:int) (d:pos)
  : Lemma (ensures ((x * d >= n) <==> (x >= ceil_div n d))) = ()

(* O2: the numeral is the least integer >= lo (no off-by-one / over-tightening). *)
let o2 (n:int) (d:pos)
  : Lemma (ensures (ceil_div n d * d >= n /\ (ceil_div n d - 1) * d < n)) = ()

(* O3: Real objective: added bound is literally the original bound. *)
let o3 (xn:int) (y:pos) (n:int) (d:pos)
  : Lemma (ensures ((xn * d >= n * y) <==> (xn * d >= n * y))) = ()

(* O4: even for a strict Int bound x > n/d (infinitesimal part nonzero, which
   the C++ guard excludes), the added non-strict bound is implied; so the
   addition is sound for either guard outcome. *)
let o4 (x:int) (n:int) (d:pos)
  : Lemma (ensures ((x * d > n) ==> (x >= ceil_div n d))) = ()
