module Z3ElimUncnstrSeqConcat
(* Models elim_uncnstr process_seq_app (OP_SEQ_CONCAT) under m_seq_concat_only. *)
open FStar.List.Tot

let rec concat_all (#a:Type) (l:list (list a)) : list a =
  match l with [] -> [] | x::xs -> x @ concat_all xs

let rec empties (#a:Type) (n:nat) : Tot (l:list (list a){length l = n}) (decreases n) =
  if n = 0 then [] else [] :: empties (n-1)

let assignment (#a:Type) (z:list a) (n:nat{n>0}) : l:list (list a){length l = n} =
  z :: empties (n-1)

let rec concat_empties (#a:Type) (n:nat) : Lemma (concat_all (empties #a n) == []) =
  if n = 0 then () else concat_empties #a (n-1)

(* O1: soundness of the all-unconstrained concat elimination: the original
   concat equals the fresh variable z under the reconstructed assignment. *)
let o1 (#a:Type) (z:list a) (n:nat{n>0}) : Lemma (concat_all (assignment z n) == z) =
  concat_empties #a (n-1); append_l_nil z

(* O2: the new guard only restricts: guarded rewrite fires => unguarded one fires. *)
let fires_base (all_unc:bool) = all_unc || true
let fires_guarded (only:bool) (all_unc:bool) = (not only || all_unc) && fires_base all_unc
let o2 (only all_unc:bool) : Lemma (fires_guarded only all_unc ==> fires_base all_unc) = ()

(* O3: with the guard, firing implies every argument is unconstrained. *)
let o3 (all_unc:bool) : Lemma (fires_guarded true all_unc ==> all_unc) = ()
