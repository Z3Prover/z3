module Z3NestedDatatypeSort
(* Model of theory_datatype::has_nested_datatype(sort pointer) at PR head b072c839. *)
type sort =
  | Dt : sort
  | Arr : rng:sort -> sort
  | Seq : sort -> sort
  | FSet : sort -> sort
  | Other : sort

let rec has_nested (s:sort) : Tot bool (decreases s) =
  match s with
  | Dt -> true
  | Arr r | Seq r | FSet r -> has_nested r
  | Other -> false

(* independent spec: a datatype is reachable by peeling containers *)
let rec peel (s:sort) : Tot (option sort) (decreases s) =
  match s with
  | Arr r | Seq r | FSet r -> peel r
  | x -> Some x

let rec o1 (s:sort) : Lemma (ensures has_nested s == (peel s = Some Dt)) (decreases s) =
  match s with Arr r | Seq r | FSet r -> o1 r | _ -> ()

(* the old special cases are subsumed: depth-1 forms agree *)
let o2 () : Lemma (has_nested (Arr Dt) /\ has_nested (FSet Dt) /\ has_nested (Seq Dt)
   /\ has_nested (Seq (Arr (FSet Dt))) /\ not (has_nested (Arr (Seq Other)))) = ()
