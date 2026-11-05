module IteLawsAudit
(* Self-contained model of the three ITE laws accepted by NR.ite_rewritten
   (PR 11554, head 86cec18): swap, then-merge by or, else-merge by and.
   Values are of an arbitrary sort 'a; conditions are Boolean values.
   n-ary and/or are modelled as folds over the flattened operand lists,
   as in NR.joined (args = [c1;c2] or junctands c1 @ junctands c2). *)
open FStar.List.Tot

let ite (#a:Type) (c:bool) (x y:a) : a = if c then x else y
let rec disj (l:list bool) : bool = match l with [] -> false | h::t -> h || disj t
let rec conj (l:list bool) : bool = match l with [] -> true | h::t -> h && conj t

let rec disj_append (l1 l2:list bool) : Lemma (disj (l1 @ l2) == (disj l1 || disj l2)) =
  match l1 with [] -> () | _::t -> disj_append t l2
let rec conj_append (l1 l2:list bool) : Lemma (conj (l1 @ l2) == (conj l1 && conj l2)) =
  match l1 with [] -> () | _::t -> conj_append t l2

(* an operand list of a canonical n-ary term evaluates to the fold; a non-nary
   operand is its own singleton *)
let ob1 (c:bool) : Lemma (disj [c] == c /\ conj [c] == c) = ()

(* O1: swap: c' = not c *)
let swap (#a:Type) (c:bool) (x y:a) : Lemma (ite c x y == ite (not c) y x) = ()

(* O2: then-merge: ite c x (ite c2 x y2) = ite (c or c2) x y2, for both joined shapes *)
let merge_then (#a:Type) (c c2:bool) (x y2:a)
  : Lemma (ite c x (ite c2 x y2) == ite (c || c2) x y2 /\
           ite c x (ite c2 x y2) == ite (disj [c; c2]) x y2) = ()
let merge_then_flat (#a:Type) (l1 l2:list bool) (x y2:a)
  : Lemma (ite (disj l1) x (ite (disj l2) x y2) == ite (disj (l1 @ l2)) x y2) =
  disj_append l1 l2

(* O3: else-merge: ite c (ite c2 x2 y) y = ite (c and c2) x2 y *)
let merge_else (#a:Type) (c c2:bool) (x2 y:a)
  : Lemma (ite c (ite c2 x2 y) y == ite (c && c2) x2 y /\
           ite c (ite c2 x2 y) y == ite (conj [c; c2]) x2 y) = ()
let merge_else_flat (#a:Type) (l1 l2:list bool) (x2 y:a)
  : Lemma (ite (conj l1) (ite (conj l2) x2 y) y == ite (conj (l1 @ l2)) x2 y) =
  conj_append l1 l2
