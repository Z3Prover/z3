module Z3SeqArgsNested
open FStar.List.Tot

(* Abstract sequence-term graph after quotienting by the congruence closure:
   Atom = non-unit/non-concat sibling, Unit = seq.unit, Cat = seq.++. *)
type elem = | D : nat -> elem | S : sq -> elem
and sq = | Atom : sq | Unit : elem -> sq | Cat : sq -> sq -> sq

let rec occurs (s:sq) (n:nat) : Tot bool (decreases s) =
  match s with
  | Atom -> false
  | Unit (D m) -> m = n
  | Unit (S t) -> occurs t n
  | Cat a b -> occurs a n || occurs b n

(* get_seq_args in the PR head: seq-sorted unit args go back to m_todo *)
let rec collect_head (s:sq) : Tot (list nat) (decreases s) =
  match s with
  | Atom -> []
  | Unit (D m) -> [m]
  | Unit (S t) -> collect_head t
  | Cat a b -> collect_head a @ collect_head b

(* get_seq_args in the base: seq-sorted unit arg is pushed to m_args, then
   dropped by process_arg because it is not a datatype *)
let rec collect_base (s:sq) : Tot (list nat) (decreases s) =
  match s with
  | Atom -> []
  | Unit (D m) -> [m]
  | Unit (S _) -> []
  | Cat a b -> collect_base a @ collect_base b

(* O1: head collection is sound and complete for datatype leaves at any depth *)
let rec head_sound_complete (s:sq) (n:nat)
  : Lemma (ensures mem n (collect_head s) == occurs s n) (decreases s) =
  match s with
  | Atom -> ()
  | Unit (D _) -> ()
  | Unit (S t) -> head_sound_complete t n
  | Cat a b -> head_sound_complete a n; head_sound_complete b n;
               append_mem (collect_head a) (collect_head b) n

(* O2: base is sound (subset of head) *)
let rec base_subset (s:sq) (n:nat)
  : Lemma (ensures mem n (collect_base s) ==> mem n (collect_head s)) (decreases s) =
  match s with
  | Atom | Unit _ -> ()
  | Cat a b -> base_subset a n; base_subset b n;
               append_mem (collect_base a) (collect_base b) n;
               append_mem (collect_head a) (collect_head b) n

(* O3: witness for the original bug: t = node(unit(unit t)) with t = leaf 0 *)
let w : sq = Unit (S (Unit (D 0)))
let base_misses : unit =
  assert_norm (occurs w 0 == true);
  assert_norm (mem 0 (collect_base w) == false);
  assert_norm (mem 0 (collect_head w) == true)
