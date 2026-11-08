module Z3CovariantNested
open FStar.List.Tot
(* Model of datatype::util::is_covariant(mark, subsorts, s) at PR head b072c839.
   Simplifications: one array domain and one sort parameter (multi-arity
   domains/params are folded by `Other`). `mk` is the ast_mark predicate. *)

type sort =
  | Dt : id:nat -> sort
  | Arr : dom:sort -> rng:sort -> sort
  | Seq : sort -> sort
  | FSet : sort -> sort
  | Other : sort -> sort
  | Leaf : sort

(* get_subsorts: every sort reachable through parameters, including itself *)
let rec subsorts (s:sort) : Tot (list sort) (decreases s) =
  match s with
  | Dt _ | Leaf -> [s]
  | Arr d r -> s :: (subsorts d @ subsorts r)
  | Seq b | FSet b | Other b -> s :: subsorts b

let any_marked (mk:nat -> bool) (l:list sort) : bool =
  List.Tot.existsb (fun x -> match x with Dt n -> mk n | _ -> false) l

let is_datatype (s:sort) = Dt? s
let is_container (s:sort) = Arr? s || Seq? s || FSet? s

(* PR code: the while(true) loop as a tail recursion *)
let rec cov (mk:nat -> bool) (s:sort) : Tot bool (decreases s) =
  match s with
  | Arr d r ->
    if any_marked mk (subsorts d) then false
    else if is_datatype r then true
    else if not (is_container r) then not (any_marked mk (subsorts r))
    else cov mk r
  | Seq b | FSet b -> cov mk b
  | _ -> true

(* Independent specification: sorts occurring in contravariant/opaque positions *)
let rec forbidden (s:sort) : Tot (list sort) (decreases s) =
  match s with
  | Arr d r ->
    subsorts d @
    (match r with
     | Dt _ -> []
     | Arr _ _ | Seq _ | FSet _ -> forbidden r
     | _ -> subsorts r)
  | Seq b | FSet b -> forbidden b
  | _ -> []

let rec append_exists (mk:nat -> bool) (a b:list sort)
  : Lemma (ensures any_marked mk (a @ b) == (any_marked mk a || any_marked mk b)) (decreases a)
  = match a with [] -> () | _::t -> append_exists mk t b

(* O1: the loop returns true iff no marked sort is in a forbidden position *)
let rec o1 (mk:nat -> bool) (s:sort)
  : Lemma (ensures cov mk s == not (any_marked mk (forbidden s))) (decreases s)
  = match s with
    | Arr d r ->
      append_exists mk (subsorts d) (match r with Dt _ -> [] | Arr _ _ | Seq _ | FSet _ -> forbidden r | _ -> subsorts r);
      (match r with Arr _ _ | Seq _ | FSet _ -> o1 mk r | _ -> ())
    | Seq b | FSet b -> o1 mk b
    | _ -> ()

(* O2: sanity/witness of intended fix: nested container ranges are checked.
   Array(Int, Seq(Array(T, Int))) is rejected when T is being defined;
   Array(Int, Seq(T)) and Seq(Array(Int,T)) are accepted. *)
let mkT (n:nat) = (n = 0)
let t = Dt 0
let _ = assert_norm (cov mkT (Arr Leaf (Seq (Arr t Leaf))) == false)
let _ = assert_norm (cov mkT (Arr Leaf (FSet (Seq (Arr t Leaf)))) == false)
let _ = assert_norm (cov mkT (Arr Leaf (Seq t)) == true)
let _ = assert_norm (cov mkT (Seq (Arr Leaf t)) == true)
let _ = assert_norm (cov mkT (Seq (Arr t Leaf)) == false)

(* O3: the former check was incomplete for domain containers; the iterative
   code never returns true while a marked sort is in an array domain at any
   container depth (soundness direction, stated for the top-level array). *)
let o3 (mk:nat -> bool) (d r:sort)
  : Lemma (requires any_marked mk (subsorts d)) (ensures cov mk (Arr d r) == false)
  = ()

(* Termination of the C++ loop corresponds to F* totality of cov (checked). *)
