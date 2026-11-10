module AmcCoverage
(* Model of the count guard `domain_size > indices.size()` in check_array_map_coherence
   (src/ast/array_map_coherence.h, head 6eb4f3f5). Indices are e-graph roots; a root
   need not denote a distinct value in a candidate model. Arrays over Bool domain. *)
open FStar.List.Tot

type arr = { dflt: int; over: list (bool & int) }   // store chain over a const/map default

let rec sel (o: list (bool & int)) (d: int) (i: bool) : int =
  match o with
  | [] -> d
  | (j, v) :: t -> if i = j then v else sel t d i

let a_of (idx: list bool) (v: int) (d: int) : arr = { dflt = d; over = map (fun i -> (i, v)) idx }

let eq_at (a b: arr) (i: bool) = sel a.over a.dflt i = sel b.over b.dflt i

(* Obligation 1 (proved): if the store indices cover the whole Bool domain, equal values at
   every store index imply equality everywhere, whatever the defaults are. *)
let covered_implies_equal (idx: list bool) (v: int) (d1 d2: int) (i: bool)
  : Lemma (requires mem true idx /\ mem false idx)
          (ensures eq_at (a_of idx v d1) (a_of idx v d2) i)
  = let rec aux (l: list bool) : Lemma (requires mem i l)
        (ensures sel (map (fun j -> (j, v)) l) d1 i = v /\ sel (map (fun j -> (j, v)) l) d2 i = v) =
      match l with | [] -> () | j :: t -> if i = j then () else aux t in
    aux idx

(* Obligation 2 (abstract state only; NOT a reachability witness): two root-distinct index
   nodes x1,x2 that a candidate model assigns the same value (true). indices.size()=2 >= |Bool|=2
   so the select branch is taken (no default-value equality is forced), but defaults 2 vs 3 differ
   at index false: the arrays agree at all store indices yet are unequal. *)
let witness_idx : list bool = [true; true]
let wa = a_of witness_idx 5 2
let wb = a_of witness_idx 5 3
let guard_passes = assert_norm (length witness_idx >= 2)
let agree_on_stores = assert_norm (eq_at wa wb true)
let differ_outside = assert_norm (~(eq_at wa wb false))
