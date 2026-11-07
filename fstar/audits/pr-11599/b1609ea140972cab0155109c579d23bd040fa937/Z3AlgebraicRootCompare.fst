module Z3AlgebraicRootCompare
(* Model of algebraic_manager::compare_core for two cells with the same polynomial.
   A squarefree polynomial has simple roots r 0 < r 1 < ... < r (n-1).
   cnt n r x = number of roots strictly below x. An isolating interval (l,u)
   has p(l),p(u) nonzero (l,u not roots) and exactly one root inside: cnt u = cnt l + 1.
   Its root is r (cnt l). sign_lower is the parity of cnt l (p's sign flips at each simple root). *)

let rec cnt (n:nat) (r:nat -> int) (x:int) : Tot nat (decreases n) =
  if n = 0 then 0 else cnt (n-1) r x + (if r (n-1) < x then 1 else 0)

let sorted (n:nat) (r:nat -> int) = forall (i j:nat). i < j /\ j < n ==> r i < r j

let rec cnt_mono (n:nat) (r:nat -> int) (x y:int)
  : Lemma (requires x <= y) (ensures cnt n r x <= cnt n r y) (decreases n)
  = if n = 0 then () else cnt_mono (n-1) r x y

let rec cnt_le (n:nat) (r:nat -> int) (x:int)
  : Lemma (ensures cnt n r x <= n) (decreases n)
  = if n = 0 then () else cnt_le (n-1) r x

(* interval is isolating *)
noeq type cell = { l:int; u:int; }
let not_root (n:nat) (r:nat -> int) (x:int) = forall (i:nat). i < n ==> r i <> x
let isolating (n:nat) (r:nat -> int) (c:cell) =
  c.l < c.u /\ not_root n r c.l /\ not_root n r c.u /\ cnt n r c.u = cnt n r c.l + 1

let sgn_lower (n:nat) (r:nat -> int) (c:cell) : bool = (cnt n r c.l) % 2 = 0

let overlap (a b:cell) = not (a.u <= b.l) && not (a.l >= b.u)

type sign = | Neg | Zero | Pos

(* head code after compare_p holds *)
let compare_head (n:nat) (r:nat -> int) (a b:cell) : sign =
  if sgn_lower n r a = sgn_lower n r b then Zero
  else if a.l < b.l then Neg else Pos

(* base code *)
let compare_base (a b:cell) : sign = Zero

(* index of root contained in the cell *)
let idx (n:nat) (r:nat -> int) (c:cell) : nat = cnt n r c.l

(* Obligation 1: overlap + isolation => parity equal iff same root index *)
let ob1 (n:nat) (r:nat -> int) (a b:cell)
  : Lemma (requires sorted n r /\ isolating n r a /\ isolating n r b /\ overlap a b)
          (ensures (sgn_lower n r a = sgn_lower n r b) <==> (idx n r a = idx n r b))
  = cnt_mono n r b.l a.u; cnt_mono n r a.l b.u

(* Obligation 2: head compare agrees with true comparison of roots r(idx a) vs r(idx b) *)
let true_cmp (n:nat) (r:nat -> int) (a b:cell) : sign =
  let ia = idx n r a in let ib = idx n r b in
  if ia = ib then Zero else if r ia < r ib then Neg else Pos

let ob2 (n:nat) (r:nat -> int) (a b:cell)
  : Lemma (requires sorted n r /\ isolating n r a /\ isolating n r b /\ overlap a b)
          (ensures compare_head n r a b = true_cmp n r a b)
  = ob1 n r a b;
    // roots exist: idx < n since cnt u = cnt l + 1 <= n
    cnt_le n r a.u; cnt_le n r b.u;
    if a.l < b.l then cnt_mono n r a.l b.l else if b.l < a.l then cnt_mono n r b.l a.l else ()

(* Obligation 3: refutation of base: reachable witness with roots 0 and 10 *)
let wr (i:nat) : int = if i = 0 then 0 else 10
let wa : cell = { l = -5; u = 5 }
let wb : cell = { l = 3; u = 12 }

let witness ()
  : Lemma (ensures sorted 2 wr /\ isolating 2 wr wa /\ isolating 2 wr wb /\ overlap wa wb
                   /\ idx 2 wr wa <> idx 2 wr wb /\ compare_base wa wb = Zero
                   /\ true_cmp 2 wr wa wb = Neg /\ compare_head 2 wr wa wb = Neg)
  = assert_norm (cnt 2 wr (-5) = 0 /\ cnt 2 wr 5 = 1 /\ cnt 2 wr 3 = 1 /\ cnt 2 wr 12 = 2)
