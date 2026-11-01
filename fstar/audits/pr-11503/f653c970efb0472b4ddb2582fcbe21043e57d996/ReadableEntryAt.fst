module ReadableEntryAt
(* Model of entry_at in fstar/cherry_runtime/main.cpp (PR head f653c970): walk a cons list
   counting position, return the element when position == wanted. Index must be scalar and >= 0. *)
open FStar.List.Tot

let rec walk (#a:Type) (l:list a) (pos wanted:nat) : Tot (option a) (decreases l) =
  match l with
  | [] -> None
  | h::t -> if pos = wanted then Some h else walk t (pos+1) wanted

let entry_at (#a:Type) (l:list a) (i:int) : option a =
  if i < 0 then None else walk l 0 i

(* O1: negative index never maps *)
let o1 (#a:Type) (l:list a) (i:int{i < 0}) : Lemma (entry_at l i == None) = ()

(* O2: in-range index returns exactly the i-th entry *)
let rec walk_correct (#a:Type) (l:list a) (pos wanted:nat)
  : Lemma (requires wanted >= pos /\ wanted - pos < length l)
          (ensures walk l pos wanted == Some (index l (wanted - pos))) (decreases l) =
  match l with
  | _::t -> if pos = wanted then () else walk_correct t (pos+1) wanted
let o2 (#a:Type) (l:list a) (i:nat{i < length l}) : Lemma (entry_at l i == Some (index l i)) =
  walk_correct l 0 i

(* O3: out-of-range index yields None (no out-of-bounds read) *)
let rec walk_oob (#a:Type) (l:list a) (pos wanted:nat)
  : Lemma (requires wanted >= pos /\ wanted - pos >= length l)
          (ensures walk l pos wanted == None) (decreases l) =
  match l with
  | [] -> ()
  | _::t -> walk_oob t (pos+1) wanted
let o3 (#a:Type) (l:list a) (i:nat{i >= length l}) : Lemma (entry_at l i == None) =
  walk_oob l 0 i
