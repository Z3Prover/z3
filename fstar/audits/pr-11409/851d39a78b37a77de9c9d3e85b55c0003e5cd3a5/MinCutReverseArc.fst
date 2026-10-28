module MinCutReverseArc
(* Model of the reverse-flow step in min_cut::augment_path (src/util/min_cut.cpp,
   lines 157-167 at head 851d39a, base 02f6a7e). One adjacency list m_edges[k]. *)
open FStar.List.Tot
type edge = { node: nat; weight: nat }

let rec bump (l:nat) (m:nat) (es:list edge) : list edge =
  match es with
  | [] -> []
  | e :: t -> (if e.node = l then {e with weight = e.weight + m} else e) :: bump l m t

let rec exists_to (l:nat) (es:list edge) : bool =
  match es with [] -> false | e :: t -> e.node = l || exists_to l t

let rec cap (l:nat) (es:list edge) : nat =
  match es with [] -> 0 | e :: t -> (if e.node = l then e.weight else 0) + cap l t

(* new = destination of freshly created arc: head uses l, base used constant 1 *)
let step (newdst:nat) (l:nat) (m:nat) (es:list edge) : list edge =
  let b = bump l m es in
  if exists_to l es then b else b @ [{node = newdst; weight = m}]

let rec cap_append (l:nat) (a b:list edge) : Lemma (cap l (a @ b) = cap l a + cap l b) =
  match a with [] -> () | _ :: t -> cap_append l t b

(* Obligation 2 (counterexample): arc k->l missing, l<>1, m>0: base leaves cap k->l = 0 *)
let witness_es : list edge = []
let cex_base () : Lemma (cap 2 (step 1 2 5 witness_es) = 0 /\ 5 > 0) = ()
(* concrete path 0->2->1 cap 1: k=2,l=0: base creates 2->1 (already real arc) not 2->0 *)
let cex_path () : Lemma (cap 0 (step 1 0 1 [ {node=1; weight=1} ]) = 0
                        /\ cap 1 (step 1 0 1 [ {node=1; weight=1} ]) = 2) = ()

(* Obligation 1 (proved): head creates reverse capacity m, for any adjacency list
   with no parallel arcs to l *)
let rec count_to (l:nat) (es:list edge) : nat =
  match es with [] -> 0 | e :: t -> (if e.node = l then 1 else 0) + count_to l t

let rec bump_cap (l m:nat) (es:list edge) : Lemma (requires count_to l es <= 1)
  (ensures cap l (bump l m es) = cap l es + m * count_to l es) =
  match es with [] -> () | _ :: t -> bump_cap l m t

let rec ex_count (l:nat) (es:list edge) : Lemma (exists_to l es = (count_to l es > 0)) =
  match es with [] -> () | _ :: t -> ex_count l t

let head_reverse (l m:nat) (es:list edge)
  : Lemma (requires count_to l es <= 1)
          (ensures cap l (step l l m es) = cap l es + m) =
  bump_cap l m es; ex_count l es;
  if exists_to l es then () else cap_append l (bump l m es) [{node=l; weight=m}]

(* Obligation 3 (proved): head step preserves other arcs' capacities *)
let rec bump_other (j l m:nat) (es:list edge) : Lemma (requires j <> l)
  (ensures cap j (bump l m es) = cap j es) =
  match es with [] -> () | _ :: t -> bump_other j l m t

let head_other (j l m:nat) (es:list edge)
  : Lemma (requires j <> l) (ensures cap j (step l l m es) = cap j es) =
  bump_other j l m es;
  if exists_to l es then () else cap_append j (bump l m es) [{node=l; weight=m}]
