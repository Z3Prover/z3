module Bit2IntModAudit

(* Integer mod with unspecified zero-divisor completion: any total function z. *)
let imod (z: int -> int) (a d: int) : int = if d = 0 then z a else a % d
(* SMT-LIB bvurem on value a (0 <= a < 2^w): x urem 0 = x. *)
let urem (a d: nat) : nat = if d = 0 then a else a % d

(* The lowering emitted by bit2int for (p - n) mod d, with p, n, d naturals. *)
let lowered (p n: nat) (d: pos) : nat =
  let r = urem n d in
  let s = d - r in
  urem (p + s) d

(* O1: reachable witness showing the BASE behavior (lowering with d = 0) is unsound
   for some legal completion z: u=1, v=0, z 1 = 2. *)
let z_wit (a: int) : int = if a = 1 then 2 else 0
let base_witness : squash (imod z_wit 1 0 <> urem 1 0) = ()

(* O2: head guard (only numeral d <> 0) makes the lowering exact for every completion z,
   with no overflow: the add stays below 2^(w+1) when p,d < 2^w. *)
let lowering_exact (z: int -> int) (p n: nat) (d: pos)
  : Lemma (lowered p n d == imod z (p - n) d) =
  let r = n % d in
  assert (r >= 0 /\ r < d);
  let q = n / d in
  assert (n == q * d + r);
  (* p - n + q*d + d  ... = p + (d - r) *)
  FStar.Math.Lemmas.lemma_mod_plus (p - n) (q + 1) d;
  assert ((p - n + (q+1) * d) == p + (d - r))

let no_overflow (w: pos) (p d: (x:nat{x < pow2 w})) (n: nat)
  : Lemma (p + (d - (if d = 0 then n else n % d)) < pow2 (w+1)) =
  FStar.Math.Lemmas.pow2_double_sum w
