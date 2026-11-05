module Z3PR11418Subterm
(* Abstract model of the datatype subterm-or-equal relation (a ⊑ b) on a binary tree datatype. *)
type tm = | Leaf : nat -> tm | Node : tm -> tm -> tm

let rec size (t:tm) : nat = match t with Leaf _ -> 1 | Node l r -> 1 + size l + size r

let rec sub (a:tm) (b:tm) : Tot bool (decreases (size b)) =
  a = b || (match b with Leaf _ -> false | Node l r -> sub a l || sub a r)

(* O1: recursive-case clause of propagate_is_subterm, ~(a⊑t) \/ a=t \/ a⊑arg_i ..., is valid (new polarity). *)
let o1_new_clause_valid (a l r:tm) : Lemma (sub a (Node l r) ==> (a = Node l r || sub a l || sub a r)) = ()

(* O1b: old polarity falsifies a true model: a=Leaf 0, t=Node (Leaf 0) (Leaf 0): a⊑t holds, a<>t, a⊑both children,
   yet the old clause (~(a⊑t) \/ a=t \/ ~(a⊑l) \/ ~(a��r)) is false. *)
let o1_old_clause_witness () : Lemma (
  let a = Leaf 0 in let t = Node (Leaf 0) (Leaf 0) in
  sub a t /\ a <> t /\
  not (not (sub a t) || a = t || not (sub a (Leaf 0)) || not (sub a (Leaf 0)))) = ()

let rec sub_size (a b:tm) : Lemma (requires sub a b) (ensures size a <= size b) (decreases (size b)) =
  match b with Leaf _ -> () | Node l r -> if a = b then () else if sub a l then sub_size a l else sub_size a r

let rec sub_strict (a b:tm) : Lemma (requires sub a b /\ a <> b) (ensures size a < size b) (decreases (size b)) =
  match b with Leaf _ -> () | Node l r -> if sub a l then sub_size a l else sub_size a r

(* O2: antisymmetry axiom ~(a⊑b) \/ ~(b⊑a) \/ a=b is valid. *)
let o2_antisym (a b:tm) : Lemma (sub a b /\ sub b a ==> a = b) =
  if a = b then ()
  else if sub a b && sub b a then (sub_strict a b; sub_strict b a)
  else ()

(* O3: reflexivity conflict: a ⊑ a holds, so ~(a⊑a) conflicts only under premise root(a)=root(b), i.e. a=b. *)
let o3_refl (a:tm) : Lemma (sub a a) = ()

(* O4: guarded not-subterm axiom: from ~(a⊑t), t=Node l r: a<>t and ~(a⊑l) and ~(a⊑r) (soundness of the asserted units). *)
let o4_not_sub (a l r:tm) : Lemma (not (sub a (Node l r)) ==> (a <> Node l r /\ not (sub a l) /\ not (sub a r))) = ()
