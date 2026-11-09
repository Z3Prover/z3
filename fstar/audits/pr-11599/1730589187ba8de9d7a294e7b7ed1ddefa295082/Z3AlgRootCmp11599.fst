module Z3AlgRootCmp11599
(* Model of compare_core's same-polynomial overlap branch. Points are ordered
   values (int); sg models sign of p at non-root points, valued in {-1,1}.
   Each cell is isolating: exactly one root r in (lo,hi), p changes sign there. *)

type cell = { lo:int; hi:int; r:int }

let isolating (sg:int -> int) (c:cell) : prop =
  c.lo < c.r /\ c.r < c.hi /\
  (forall (x:int). (c.lo <= x /\ x < c.r) ==> sg x = sg c.lo) /\
  (forall (x:int). (c.r < x /\ x <= c.hi) ==> sg x = - (sg c.lo)) /\
  sg c.r = 0 /\ (sg c.lo = 1 \/ sg c.lo = -1)

(* new code: 0 -> equal, -1 -> a<b, 1 -> a>b *)
let new_cmp (sg:int -> int) (a b:cell) : int =
  if a.hi <= b.lo then -1
  else if a.lo >= b.hi then 1
  else if sg a.lo = sg b.lo then 0
  else if a.lo < b.lo then -1 else 1

let old_cmp (a b:cell) : int =
  if a.hi <= b.lo then -1 else if a.lo >= b.hi then 1 else 0

let spec (a b:cell) : int = if a.r = b.r then 0 else if a.r < b.r then -1 else 1

(* O1/O2/O3: soundness and completeness of the new branch for overlapping cells *)
let new_correct (sg:int -> int) (a b:cell)
  : Lemma (requires isolating sg a /\ isolating sg b /\ a.hi > b.lo /\ a.lo < b.hi)
          (ensures new_cmp sg a b = spec a b)
  = assert (a.lo < b.lo ==> (b.lo < a.r \/ b.lo > a.r));
    ()

(* the early interval exits are also correct for any isolating cells *)
let cheap_correct (sg:int -> int) (a b:cell)
  : Lemma (requires isolating sg a /\ isolating sg b /\ (a.hi <= b.lo \/ a.lo >= b.hi))
          (ensures new_cmp sg a b = spec a b)
  = ()

(* concrete witness refuting the OLD code: roots 8 and 12 of one polynomial with
   sign pattern + on x<8, - on 8(x<12, + on x)12 *)
let sgw (x:int) : int = if x = 8 || x = 12 then 0 else if x < 8 then 1 else if x < 12 then -1 else 1
let wa : cell = {lo=6; hi=10; r=8}
let wb : cell = {lo=9; hi=14; r=12}
let old_wrong ()
  : Lemma (isolating sgw wa /\ isolating sgw wb /\ old_cmp wa wb = 0 /\ spec wa wb = -1 /\ new_cmp sgw wa wb = -1)
  = ()
