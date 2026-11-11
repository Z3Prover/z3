(* Portions adapted from the MIT-licensed Lean artifact.
   Copyright (c) 2026 Ian Erik Varatalu, Ekaterina Zhuchko, and Margus Veanes.
   See LICENSE.txt for the MIT permission and warranty notice. *)
module Z3PredicateAlgebra

(* Semantic counterpart of the alphabet interface in the Lean artifact
   (doi:10.5281/zenodo.23383207). Predicate equality is not semantic equality. *)
noeq type algebra (p a:Type) = {
  holds : p -> a -> bool;
  top : p;
  bottom : p;
  mk_and : p -> p -> p;
  mk_or : p -> p -> p;
  mk_not : p -> p
}

[@@"opaque_to_smt"]
let valid (#p #a:Type) (alg:algebra p a) : prop =
  (forall x. alg.holds alg.top x == true) /\
  (forall x. alg.holds alg.bottom x == false) /\
  (forall q x. alg.holds (alg.mk_not q) x == not (alg.holds q x)) /\
  (forall q r x. alg.holds (alg.mk_and q r) x ==
    (alg.holds q x && alg.holds r x)) /\
  (forall q r x. alg.holds (alg.mk_or q r) x ==
    (alg.holds q x || alg.holds r x))

(* false means "emptiness not established", including an unknown answer.
   Only a true answer permits pruning; completeness and witnesses are not needed. *)
[@@"opaque_to_smt"]
let empty_sound (#p #a:Type) (alg:algebra p a) (is_empty:p -> bool) : prop =
  forall q x. is_empty q ==> not (alg.holds q x)

let lemma_split (#p #a:Type) (alg:algebra p a) (path q:p) (x:a)
  : Lemma (requires valid alg)
          (ensures alg.holds (alg.mk_and path q) x ==
                     (alg.holds path x && alg.holds q x) /\
                   alg.holds (alg.mk_and path (alg.mk_not q)) x ==
                     (alg.holds path x && not (alg.holds q x))) =
  reveal_opaque (`%valid) (valid alg)

let lemma_top (#p #a:Type) (alg:algebra p a) (x:a)
  : Lemma (requires valid alg) (ensures alg.holds alg.top x) =
  reveal_opaque (`%valid) (valid alg)

let lemma_empty (#p #a:Type) (alg:algebra p a) (is_empty:p -> bool) (q:p) (x:a)
  : Lemma (requires empty_sound alg is_empty /\ is_empty q)
          (ensures not (alg.holds q x)) =
  reveal_opaque (`%empty_sound) (empty_sound alg is_empty)

let never_empty (#p:Type) (_:p) : bool = false

let lemma_never_empty_sound (#p #a:Type) (alg:algebra p a)
  : Lemma (empty_sound alg never_empty) =
  reveal_opaque (`%empty_sound) (empty_sound alg never_empty)

type predicate (p:Type) =
  | Atom : atom:p -> predicate p
  | Top : predicate p
  | Bottom : predicate p
  | Meet : lhs:predicate p -> rhs:predicate p -> predicate p
  | Join : lhs:predicate p -> rhs:predicate p -> predicate p
  | Compl : arg:predicate p -> predicate p

let rec denote (#p #a:Type) (atom:p -> a -> bool) (q:predicate p) (x:a)
  : Tot bool (decreases q) =
  match q with
  | Atom p -> atom p x
  | Top -> true
  | Bottom -> false
  | Meet q r -> denote atom q x && denote atom r x
  | Join q r -> denote atom q x || denote atom r x
  | Compl q -> not (denote atom q x)

let free_algebra (#p #a:Type) (atom:p -> a -> bool) : algebra (predicate p) a =
  { holds = denote atom; top = Top; bottom = Bottom;
    mk_and = (fun q r -> Meet q r); mk_or = (fun q r -> Join q r);
    mk_not = (fun q -> Compl q) }

let lemma_free_algebra_valid (#p #a:Type) (atom:p -> a -> bool)
  : Lemma (valid (free_algebra atom)) =
  reveal_opaque (`%valid) (valid (free_algebra atom))
