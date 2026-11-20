module Z3PR11701ArrayDefault

(* Large-domain array default semantics: store preserves default. *)
type arr = { def: bool; ex: list (int & bool) }

let rec lookup (l: list (int & bool)) (i: int) (d: bool) : Tot bool (decreases l) =
  match l with
  | [] -> d
  | (j, v) :: t -> if i = j then v else lookup t i d

let select (a: arr) (i: int) : bool = lookup a.ex i a.def
let store (a: arr) (i: int) (v: bool) : arr = { a with ex = (i, v) :: a.ex }
let default_ (a: arr) : bool = a.def

(* O1: the model satisfies default-preserved-by-store on an unbounded domain. *)
let store_preserves_default (a: arr) (i: int) (v: bool)
  : Lemma (default_ (store a i v) == default_ a) = ()

(* O1: the removed axiom default(L) = L[eps] is refutable for ANY default
   function d obeying store-preservation, whenever L[eps] <> v. *)
let removed_axiom_inconsistent
  (d: arr -> bool) (eps: int) (a: arr) (v: bool)
  : Lemma
    (requires (forall (b: arr) (i: int) (w: bool). d (store b i w) == d b) /\
              (forall (b: arr). d b == select b eps) /\
              v <> select a eps)
    (ensures False)
  = assert (select (store a eps v) eps == v);
    assert (d (store a eps v) == d a)

(* O1 concrete witness: lambda x. x = 5 modelled as {def=false; ex=[(5,true)]},
   eps=0, v=true: L[eps]=false <> true, so the axiom instance on
   store(L,eps,v) contradicts store-preservation. *)
let witness_L : arr = { def = false; ex = [(5, true)] }
let witness_ok () : Lemma (select witness_L 0 == false /\ select (store witness_L 0 true) 0 == true) = ()

(* O2: observed default of a const-free store component is underdetermined:
   flipping every default is consistent with select/store constraints,
   yet changes the observed default. Hence giving up is required. *)
let flip (a: arr) : arr = { a with def = not a.def }
let d2 (a: arr) : bool = not a.def

let underdetermined (a: arr) (i: int) (v: bool)
  : Lemma (d2 (store a i v) == d2 a /\ d2 a <> default_ a) = ()

(* Const anchors default: select(const(c), i) = c determines def. *)
let const_arr (c: bool) : arr = { def = c; ex = [] }
let const_fixes_default (c: bool) (i: int)
  : Lemma (select (const_arr c) i == c /\ default_ (const_arr c) == c) = ()
