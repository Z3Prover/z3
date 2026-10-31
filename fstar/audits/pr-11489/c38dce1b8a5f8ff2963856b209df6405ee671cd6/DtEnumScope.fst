module DtEnumScope
(* Abstract model of datatype_factory::get_enumerator (PR 11489): nodes are sorts,
   edge a b means b is a constructor-argument sort or sort parameter of a.
   Productions are registered for x iff x is reachable from s (pass 1) and s is
   reachable from x (pass 2, backward closure over the recorded parent edges). *)
type reach (e: nat -> nat -> bool) : nat -> nat -> Type0 =
  | Refl : a:nat -> reach e a a
  | Step : a:nat -> b:nat -> c:nat -> squash (e a b) -> reach e b c -> reach e a c

let selected (e: nat -> nat -> bool) (s x: nat) : Type0 = reach e s x & reach e x s

let rec trans (#e: nat -> nat -> bool) (#a #b #c: nat) (p: reach e a b) (q: reach e b c)
  : Tot (reach e a c) (decreases p) =
  match p with
  | Refl _ -> q
  | Step a' b' _ h r -> Step a' b' c h (trans r q)

(* O1: the root sort always receives its productions. *)
let o1_root (e: nat -> nat -> bool) (s: nat) : selected e s s = (Refl s, Refl s)

(* O2: soundness of scope: any two selected sorts are mutually dependent. *)
let o2_group (e: nat -> nat -> bool) (s x y: nat)
  (hx: selected e s x) (hy: selected e s y) : reach e x y & reach e y x =
  (trans (snd hx) (fst hy), trans (snd hy) (fst hx))

(* O3: preservation of mutual recursion: every sort lying on a dependency path
   s ->* x ->* s (including through Array/Seq parameters) is selected. *)
let o3_cycle (e: nat -> nat -> bool) (s x: nat) (p: reach e s x) (q: reach e x s)
  : selected e s x = (p, q)

(* Refutation attempt: a sort x that is only reachable from s but cannot reach s
   is excluded; show this is consistent with e.g. a single edge s -> x. *)
let e1 (a b: nat) : bool = (a = 0 && b = 1)
let no_back (r: reach e1 1 0) : Lemma False =
  match r with
  | Step _ b _ h _ -> ()
let o4_excluded_nonmember : (selected e1 0 1 -> Lemma False) =
  fun h -> no_back (snd h)
