module SubtermMergeAudit
(* Model of the subterm-transfer loop of theory_datatype::merge_eh (PR 11598, head 8693b2d).
   Lists are d->m_subterms (enode ids as nat). add = add_subterm_predicate's
   contains-check + push_back on d1. The oracle models propagation triggered inside
   add_subterm_predicate, assumed to only APPEND to d2 (bounded by b: finiteness). *)
open FStar.List.Tot

let add (x:nat) (d:list nat) : list nat = if mem x d then d else d @ [x]

let rec is_prefix (a b:list nat) : Tot bool =
  match a, b with
  | [], _ -> true
  | x::a', y::b' -> x = y && is_prefix a' b'
  | _ -> false

let rec prefix_trans (a b c:list nat)
  : Lemma (requires is_prefix a b /\ is_prefix b c) (ensures is_prefix a c) =
  match a, b, c with | _::a', _::b', _::c' -> prefix_trans a' b' c' | _ -> ()

let rec prefix_index (a b:list nat) (i:nat)
  : Lemma (requires is_prefix a b /\ i < length a) (ensures i < length b /\ index a i = index b i) =
  match a, b with | _::a', _::b' -> if i = 0 then () else prefix_index a' b' (i-1) | _ -> ()

let rec prefix_len (a b:list nat) : Lemma (requires is_prefix a b) (ensures length a <= length b) =
  match a, b with | _::a', _::b' -> prefix_len a' b' | _ -> ()

let rec prefix_refl (a:list nat) : Lemma (is_prefix a a) =
  match a with [] -> () | _::t -> prefix_refl t

(* all elements of d2 at positions < n are in d1 *)
let covers (d1 d2:list nat) (n:nat) : prop =
  forall (j:nat). j < n /\ j < length d2 ==> mem (index d2 j) d1

let mem_add (x y:nat) (d:list nat)
  : Lemma (ensures (mem y d ==> mem y (add x d)) /\ mem x (add x d)) =
  FStar.List.Tot.Properties.append_mem d [x] y;
  FStar.List.Tot.Properties.append_mem d [x] x

let covers_prefix (d1 d2 d2':list nat) (n:nat)
  : Lemma (requires covers d1 d2 n /\ is_prefix d2 d2' /\ n <= length d2) (ensures covers d1 d2' n) =
  let aux (j:nat) : Lemma (j < n /\ j < length d2' ==> mem (index d2' j) d1) =
    if j < n then prefix_index d2 d2' j in
  Classical.forall_intro aux

let oracle_t (b:nat) = d2:list nat{length d2 <= b} -> r:list nat{is_prefix d2 r /\ length r <= b}

(* Indexed loop of the PR: bound is re-read each iteration (d2 may grow). *)
let rec loop (b:nat) (o:oracle_t b) (i:nat) (d1 d2:list nat)
  : Ghost (list nat & list nat)
      (requires i <= length d2 /\ length d2 <= b /\ covers d1 d2 i)
      (ensures fun (d1', d2') -> is_prefix d2 d2' /\ length d2' <= b /\ covers d1' d2' (length d2') /\ length d2' >= length d2)
      (decreases (b - i)) =
  if i < length d2 then begin
    let d2' = o d2 in
    prefix_index d2 d2' i; prefix_len d2 d2'; covers_prefix d1 d2 d2' i;
    let x = index d2' i in
    let d1' = add x d1 in
    Classical.forall_intro (fun (y:nat) -> mem_add x y d1);
    let (d1'', d2'') = loop b o (i+1) d1' d2' in
    prefix_trans d2 d2' d2'';
    (d1'', d2'')
  end else (prefix_refl d2; (d1, d2))
