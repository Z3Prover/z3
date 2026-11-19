module NestedVisited
open FStar.List.Tot

(* Model of the container branch of add_todo in theory_datatype::get_nested_args.
   A node is abstracted by its e-class root (an int); todo holds roots, visited
   is the obj_hashtable of roots. Datatype-sorted nodes (m_args) are out of scope. *)
type st = { todo : list int; visited : list int }

(* Base: insert_if_not_there returns a non-null reference, so the Boolean test is true *)
let add_old (r:int) (s:st) : st = { todo = s.todo @ [r]; visited = if mem r s.visited then s.visited else r :: s.visited }
(* Head: !contains(r) then insert(r) then push *)
let add_new (r:int) (s:st) : st =
  if mem r s.visited then s else { todo = s.todo @ [r]; visited = r :: s.visited }

let init : st = { todo = []; visited = [] }

(* O1 refutation: a class whose sibling concat contains the class itself re-adds root r every
   time it is expanded; the old guard grows todo without bound. *)
let rec expand_self_old (r:int) (k:nat) (s:st) : Tot st (decreases k) =
  if k = 0 then s else expand_self_old r (k-1) (add_old r s)
let rec expand_self_new (r:int) (k:nat) (s:st) : Tot st (decreases k) =
  if k = 0 then s else expand_self_new r (k-1) (add_new r s)

let rec old_len (r:int) (k:nat) (s:st) : Lemma (ensures length (expand_self_old r k s).todo = length s.todo + k) (decreases k)
  = if k = 0 then () else (old_len r (k-1) (add_old r s); append_length s.todo [r])

let o1_old_unbounded (r:int) (k:nat) : Lemma (length (expand_self_old r k (add_old r init)).todo = k + 1)
  = old_len r k (add_old r init)

(* O2: new guard keeps todo duplicate-free and visited = todo as sets *)
let inv (s:st) = noRepeats s.todo /\ (forall x. mem x s.visited <==> mem x s.todo)

let rec nr_append (l:list int) (x:int) : Lemma (requires noRepeats l /\ ~(mem x l)) (ensures noRepeats (l @ [x]))
  = match l with [] -> () | h::t -> nr_append t x; append_mem t [x] h

let o2_new_preserves_inv (r:int) (s:st) : Lemma (requires inv s) (ensures inv (add_new r s))
  = if mem r s.visited then () else (
      nr_append s.todo r;
      FStar.Classical.forall_intro (append_mem s.todo [r]))

(* O3: no class is lost: after add_new r, r is in todo (queued now or earlier) *)
let o3_complete (r:int) (s:st) : Lemma (requires inv s) (ensures mem r (add_new r s).todo /\ (forall x. mem x s.todo ==> mem x (add_new r s).todo))
  = if mem r s.visited then () else FStar.Classical.forall_intro (append_mem s.todo [r])

(* Self-loop under the new guard: todo has exactly one entry for any k *)
let rec new_self (r:int) (k:nat) (s:st) : Lemma (requires inv s /\ mem r s.todo) (ensures (expand_self_new r k s).todo == s.todo) (decreases k)
  = if k = 0 then () else new_self r (k-1) s

let o2_self_bounded (r:int) (k:nat) : Lemma ((expand_self_new r k (add_new r init)).todo == [r])
  = new_self r k (add_new r init)
