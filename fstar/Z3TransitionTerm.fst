(* Portions adapted from the MIT-licensed Lean artifact.
   Copyright (c) 2026 Ian Erik Varatalu, Ekaterina Zhuchko, and Margus Veanes.
   See LICENSE.txt for the MIT permission and warranty notice. *)
module Z3TransitionTerm

module A = Z3PredicateAlgebra
module L = FStar.List.Tot

(* Generic reference trees, independent of predicate ordering and DAG sharing. *)
type term (p b:Type) =
  | Leaf : value:b -> term p b
  | Node : guard:p -> yes:term p b -> no:term p b -> term p b

let rec eval (#p #a #b:Type) (holds:p -> a -> bool) (t:term p b) (x:a)
  : Tot b (decreases t) =
  match t with
  | Leaf b -> b
  | Node q l r -> if holds q x then eval holds l x else eval holds r x

let rec bind (#p #b #c:Type) (t:term p b) (f:b -> term p c)
  : Tot (term p c) (decreases t) =
  match t with
  | Leaf b -> f b
  | Node q l r -> Node q (bind l f) (bind r f)

let lift_unary (#p #b #c:Type) (op:b -> c) (t:term p b) : term p c =
  bind t (fun b -> Leaf (op b))

let lift_binary (#p #b #c #d:Type) (op:b -> c -> d)
                (l:term p b) (r:term p c) : term p d =
  bind l (fun b -> lift_unary (op b) r)

let rec lemma_eval_bind (#p #a #b #c:Type) (holds:p -> a -> bool)
    (t:term p b) (f:b -> term p c) (x:a)
  : Lemma (ensures eval holds (bind t f) x == eval holds (f (eval holds t x)) x)
          (decreases t) =
  match t with
  | Leaf _ -> ()
  | Node q l r ->
    if holds q x then lemma_eval_bind holds l f x
    else lemma_eval_bind holds r f x

let lemma_eval_lift_unary (#p #a #b #c:Type) (holds:p -> a -> bool)
    (op:b -> c) (t:term p b) (x:a)
  : Lemma (eval holds (lift_unary op t) x == op (eval holds t x)) =
  lemma_eval_bind holds t (fun b -> Leaf (op b)) x

let lemma_eval_lift_binary (#p #a #b #c #d:Type) (holds:p -> a -> bool)
    (op:b -> c -> d) (l:term p b) (r:term p c) (x:a)
  : Lemma (eval holds (lift_binary op l r) x ==
           op (eval holds l x) (eval holds r x)) =
  lemma_eval_bind holds l (fun b -> lift_unary (op b) r) x;
  lemma_eval_lift_unary holds (op (eval holds l x)) r x

let rec leaves (#p #b:Type) (t:term p b)
  : Tot (list b) (decreases t) =
  match t with
  | Leaf b -> [b]
  | Node _ l r -> L.append (leaves l) (leaves r)

let rec lemma_eval_mem_leaves (#p #a:Type) (#b:eqtype)
    (holds:p -> a -> bool) (t:term p b) (x:a)
  : Lemma (ensures L.mem (eval holds t x) (leaves t)) (decreases t) =
  match t with
  | Leaf _ -> ()
  | Node q l r ->
    FStar.List.Tot.Properties.append_mem (leaves l) (leaves r) (eval holds t x);
    if holds q x then lemma_eval_mem_leaves holds l x
    else lemma_eval_mem_leaves holds r x

let rec restrict (#p #a #b:Type) (alg:A.algebra p a) (is_empty:p -> bool)
    (t:term p b) (path:p) : Tot (term p b) (decreases t) =
  match t with
  | Leaf _ -> t
  | Node q l r ->
    let yes = alg.mk_and path q in
    let no = alg.mk_and path (alg.mk_not q) in
    if is_empty yes then restrict alg is_empty r no
    else if is_empty no then restrict alg is_empty l yes
    else Node q (restrict alg is_empty l yes) (restrict alg is_empty r no)

let rec lemma_eval_restrict (#p #a #b:Type) (alg:A.algebra p a)
    (is_empty:p -> bool) (t:term p b) (path:p) (x:a)
  : Lemma (requires A.valid alg /\ A.empty_sound alg is_empty /\ alg.holds path x)
          (ensures eval alg.holds (restrict alg is_empty t path) x ==
                   eval alg.holds t x)
          (decreases t) =
  match t with
  | Leaf _ -> ()
  | Node q l r ->
    let yes = alg.mk_and path q in
    let no = alg.mk_and path (alg.mk_not q) in
    A.lemma_split alg path q x;
    if is_empty yes then (
      A.lemma_empty alg is_empty yes x;
      assert (not (alg.holds q x));
      lemma_eval_restrict alg is_empty r no x)
    else if is_empty no then (
      A.lemma_empty alg is_empty no x;
      assert (alg.holds q x);
      lemma_eval_restrict alg is_empty l yes x)
    else if alg.holds q x then lemma_eval_restrict alg is_empty l yes x
    else lemma_eval_restrict alg is_empty r no x

(* Check every potentially reachable leaf. An incomplete emptiness checker may
   retain extra obligations, but cannot turn missing coverage into acceptance. *)
let rec check (#p #a #b:Type) (alg:A.algebra p a) (is_empty:p -> bool)
    (accept:b -> bool) (path:p) (t:term p b) : Tot bool (decreases t) =
  if is_empty path then true
  else match t with
  | Leaf b -> accept b
  | Node q l r ->
    check alg is_empty accept (alg.mk_and path q) l &&
    check alg is_empty accept (alg.mk_and path (alg.mk_not q)) r

let rec lemma_check_sound (#p #a #b:Type) (alg:A.algebra p a)
    (is_empty:p -> bool) (accept:b -> bool) (path:p) (t:term p b) (x:a)
  : Lemma (requires A.valid alg /\ A.empty_sound alg is_empty /\
                   alg.holds path x /\ check alg is_empty accept path t)
          (ensures accept (eval alg.holds t x))
          (decreases t) =
  if is_empty path then A.lemma_empty alg is_empty path x
  else match t with
  | Leaf _ -> ()
  | Node q l r ->
    A.lemma_split alg path q x;
    if alg.holds q x then
      lemma_check_sound alg is_empty accept (alg.mk_and path q) l x
    else
      lemma_check_sound alg is_empty accept (alg.mk_and path (alg.mk_not q)) r x
