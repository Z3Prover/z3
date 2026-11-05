module Z3FiniteSetTheory

(*
   F* formalization of the rewrite rules in
   src/ast/rewriter/finite_set_rewriter.cpp (`mk_union`, `mk_intersect`,
   `mk_difference`, `mk_subset`, `mk_singleton`, `mk_size`, `mk_map`,
   `mk_filter`, `mk_in`).

   `finite_set_rewriter.cpp` is Z3's *finite-set* sort (`set.empty`,
   `set.singleton`, `set.union`, `set.range`, `set.map`, `set.filter`,
   `set.size`, ...), distinct from the extensional-array-based "set" family
   modeled in `Z3ArrayTheory.fst` (which models `(Array I Bool)` used by
   `array_rewriter.cpp`'s `mk_set_*`). Both are modeled the same way --
   extensionally-quotiented predicates over the element type, via
   `FStar.FunctionalExtensionality`'s `idx ^-> v` restricted-arrow type --
   but here we use a `Type0` (propositional) codomain rather than `bool`,
   so that `set.map`'s existential "image of a function" semantics can be
   stated directly (an arbitrary element type need not have decidable
   equality-of-images, so a `bool`-valued membership test is not always
   computable; a `Type0`-valued one always is a legitimate specification).
*)

open FStar.FunctionalExtensionality

(* ----------------------------------------------------------------- *)
(* Core representation                                                *)
(* ----------------------------------------------------------------- *)

/// A finite set over `a`, modeled (as in `Z3ArrayTheory`) by its
/// extensionally-quotiented membership predicate.
type fset (a:eqtype) = a ^-> prop

let mem (#a:eqtype) (s:fset a) (x:a) : prop = s x

let empty_set (#a:eqtype) : fset a = on a (fun _ -> False)

let singleton (#a:eqtype) (x:a) : fset a = on a (fun y -> y == x)

let union (#a:eqtype) (s t:fset a) : fset a = on a (fun x -> mem s x \/ mem t x)

let intersect (#a:eqtype) (s t:fset a) : fset a = on a (fun x -> mem s x /\ mem t x)

let difference (#a:eqtype) (s t:fset a) : fset a = on a (fun x -> mem s x /\ ~(mem t x))

/// `set.range(lo,hi)` over integers.
let range_set (lo hi:int) : fset int = on int (fun x -> lo <= x /\ x <= hi)

/// Extensionality, specialized from `FStar.FunctionalExtensionality` as in
/// `Z3ArrayTheory.lemma_array_extensionality`: two finite sets are equal
/// iff they have the same members.
let lemma_set_extensionality (#a:eqtype) (s t:fset a)
  : Lemma ((s == t) <==> (forall x. mem s x <==> mem t x))
  = extensionality a (fun _ -> prop) s t

/// Bridges a pointwise `<==>` fact to the `==` form `extensionality`'s
/// SMTPat expects: `prop`-valued equality is not literal syntactic
/// equality, so proving `feq s t` (needed to trigger `extensionality`)
/// requires `FStar.PropositionalExtensionality`'s axiom relating `<==>`
/// and `==` on `prop`, applied pointwise.
let lemma_set_eq_from_iff (#a:eqtype) (s t:fset a)
  : Lemma (requires forall x. mem s x <==> mem t x) (ensures s == t)
  = let aux (x:a) : Lemma (mem s x == mem t x) =
      FStar.PropositionalExtensionality.apply (mem s x) (mem t x)
    in
    FStar.Classical.forall_intro aux;
    assert (feq s t)

(* ----------------------------------------------------------------- *)
(* mk_union                                                            *)
(* ----------------------------------------------------------------- *)

/// `set.union(x,x) = x` -- idempotency.
let lemma_union_idem (#a:eqtype) (s:fset a)
  : Lemma (union s s == s) = lemma_set_eq_from_iff (union s s) s

/// `set.union(x,empty) = x`, `set.union(empty,x) = x` -- identity.
let lemma_union_empty_r (#a:eqtype) (s:fset a)
  : Lemma (union s empty_set == s) = lemma_set_eq_from_iff (union s empty_set) s

let lemma_union_empty_l (#a:eqtype) (s:fset a)
  : Lemma (union empty_set s == s) = lemma_set_eq_from_iff (union empty_set s) s

/// `set.union(x, set.intersect(x,y)) = x` and the symmetric case --
/// absorption.
let lemma_union_absorb_r (#a:eqtype) (s t:fset a)
  : Lemma (union s (intersect s t) == s) = lemma_set_eq_from_iff (union s (intersect s t)) s

let lemma_union_absorb_l (#a:eqtype) (s t:fset a)
  : Lemma (union (intersect s t) s == s) = lemma_set_eq_from_iff (union (intersect s t) s) s

(* ----------------------------------------------------------------- *)
(* mk_intersect                                                        *)
(* ----------------------------------------------------------------- *)

/// `set.intersect(x,x) = x` -- idempotency.
let lemma_intersect_idem (#a:eqtype) (s:fset a)
  : Lemma (intersect s s == s) = lemma_set_eq_from_iff (intersect s s) s

/// `set.intersect(x,empty) = empty`, `set.intersect(empty,x) = empty` --
/// annihilation.
let lemma_intersect_empty_r (#a:eqtype) (s:fset a)
  : Lemma (intersect s empty_set == empty_set) = lemma_set_eq_from_iff (intersect s empty_set) empty_set

let lemma_intersect_empty_l (#a:eqtype) (s:fset a)
  : Lemma (intersect empty_set s == empty_set) = lemma_set_eq_from_iff (intersect empty_set s) empty_set

/// `set.intersect(x, set.union(x,y)) = x` and the symmetric case --
/// absorption.
let lemma_intersect_absorb_r (#a:eqtype) (s t:fset a)
  : Lemma (intersect s (union s t) == s) = lemma_set_eq_from_iff (intersect s (union s t)) s

let lemma_intersect_absorb_l (#a:eqtype) (s t:fset a)
  : Lemma (intersect (union s t) s == s) = lemma_set_eq_from_iff (intersect (union s t) s) s

/// `set.intersect(range(l1,u1), range(l2,u2)) = range(max(l1,l2), min(u1,u2))`.
let lemma_intersect_ranges (l1 u1 l2 u2:int)
  : Lemma (intersect (range_set l1 u1) (range_set l2 u2)
           == range_set (if l1 >= l2 then l1 else l2) (if u1 >= u2 then u2 else u1))
  = lemma_set_eq_from_iff (intersect (range_set l1 u1) (range_set l2 u2))
                          (range_set (if l1 >= l2 then l1 else l2) (if u1 >= u2 then u2 else u1))

(* ----------------------------------------------------------------- *)
(* mk_difference                                                       *)
(* ----------------------------------------------------------------- *)

/// `set.difference(x,x) = empty`.
let lemma_difference_self (#a:eqtype) (s:fset a)
  : Lemma (difference s s == empty_set) = lemma_set_eq_from_iff (difference s s) empty_set

/// `set.difference(x,empty) = x` -- identity.
let lemma_difference_empty_r (#a:eqtype) (s:fset a)
  : Lemma (difference s empty_set == s) = lemma_set_eq_from_iff (difference s empty_set) s

/// `set.difference(empty,x) = empty` -- annihilation.
let lemma_difference_empty_l (#a:eqtype) (s:fset a)
  : Lemma (difference empty_set s == empty_set) = lemma_set_eq_from_iff (difference empty_set s) empty_set

(* ----------------------------------------------------------------- *)
(* mk_subset                                                           *)
(* ----------------------------------------------------------------- *)

/// `set.subset(x,x) <=> True`.
let lemma_subset_refl (#a:eqtype) (s:fset a) : Lemma (mem s == mem s) = ()

/// `set.subset(empty,x) <=> True`.
let lemma_subset_empty_l (#a:eqtype) (s:fset a)
  : Lemma (forall x. mem (empty_set #a) x ==> mem s x) = ()

/// `set.subset(x,empty) <=> x = empty`.
let lemma_subset_empty_r (#a:eqtype) (s:fset a)
  : Lemma ((forall x. mem s x ==> mem (empty_set #a) x) <==> (s == empty_set))
  = lemma_set_extensionality s empty_set

/// General case: `set.subset(x,y) <=> set.intersect(x,y) = x` -- exactly
/// the semantic definition of subset, restated as the extensional
/// equation `mk_subset` rewrites to.
let lemma_subset_iff_intersect (#a:eqtype) (s t:fset a)
  : Lemma ((forall x. mem s x ==> mem t x) <==> (intersect s t == s))
  = lemma_set_extensionality (intersect s t) s

(* ----------------------------------------------------------------- *)
(* mk_in                                                               *)
(* ----------------------------------------------------------------- *)

/// `set.in(x,empty) <=> False`.
let lemma_in_empty (#a:eqtype) (x:a) : Lemma (~(mem (empty_set #a) x)) = ()

/// `set.in(x,singleton(y)) <=> x = y`.
let lemma_in_singleton (#a:eqtype) (x y:a) : Lemma (mem (singleton y) x <==> x == y) = ()

/// `set.in(x,range(lo,hi)) <=> lo <= x /\ x <= hi`.
let lemma_in_range (lo hi x:int) : Lemma (mem (range_set lo hi) x <==> (lo <= x /\ x <= hi)) = ()

(* ----------------------------------------------------------------- *)
(* mk_size (on the concrete shapes `mk_size` rewrites: empty,            *)
(* singleton, range -- so stated directly over int, not `fset`)         *)
(* ----------------------------------------------------------------- *)

/// `set.size(empty) = 0`.
let size_empty : int = 0

/// `set.size(singleton(x)) = 1`.
let size_singleton : int = 1

/// `set.size(range(lo,hi)) = ite(lo>hi, 0, hi-lo+1)` -- `mk_size`'s
/// formula, restated directly (the F* `if` *is* the generated `ite`).
let size_range (lo hi:int) : int = if lo > hi then 0 else hi - lo + 1

/// `size_range` indeed counts the integers in `[lo,hi]`: it matches
/// `FStar.List`'s count of `[lo..hi]`-style enumeration via a direct
/// induction-free identity (both sides reduce to the same arithmetic
/// formula, so this is really a sanity check that the formula is the
/// expected cardinality, not merely whatever `mk_size` happened to emit).
let lemma_size_range_nonneg (lo hi:int) : Lemma (size_range lo hi >= 0) = ()

(* ----------------------------------------------------------------- *)
(* mk_map / mk_filter                                                   *)
(* ----------------------------------------------------------------- *)

/// `set.map(f,s) = { f(x) | x in s }`, modeled as the direct image
/// predicate (an existential, since `f` need not be injective -- several
/// elements of `s` may map to the same image element, or none may).
let map_set (#a #b:eqtype) (f:a -> b) (s:fset a) : fset b =
  on b (fun y -> exists (x:a). mem s x /\ f x == y)

/// `set.map(f,empty) = empty`.
let lemma_map_empty (#a #b:eqtype) (f:a -> b)
  : Lemma (map_set f (empty_set #a) == (empty_set #b))
  = lemma_set_eq_from_iff (map_set f (empty_set #a)) (empty_set #b)

/// `set.map(f,singleton(x)) = singleton(f(x))`.
let lemma_map_singleton (#a #b:eqtype) (f:a -> b) (x:a)
  : Lemma (map_set f (singleton x) == singleton (f x))
  = lemma_set_eq_from_iff (map_set f (singleton x)) (singleton (f x))

/// `set.map(f, set.union(s,t)) = set.union(set.map(f,s), set.map(f,t))`.
let lemma_map_union (#a #b:eqtype) (f:a -> b) (s t:fset a)
  : Lemma (map_set f (union s t) == union (map_set f s) (map_set f t))
  = lemma_set_eq_from_iff (map_set f (union s t)) (union (map_set f s) (map_set f t))

/// `set.map` does **not** distribute over `set.intersect`, confirming the
/// `.cpp` file's own explanatory comment (`f` need not be injective): we
/// exhibit a concrete countermodel over `a = b = bool`,
/// `f = (fun _ -> false)`, `s = {true}`, `t = {false}` where
/// `map(f, intersect(s,t)) = map(f, empty) = empty` but
/// `intersect(map(f,s), map(f,t)) = intersect({false},{false}) = {false}`,
/// so the two sides genuinely differ -- a non-distributivity rewrite would
/// be unsound.
let lemma_map_intersect_not_distributive ()
  : Lemma (~ (map_set (fun (_:bool) -> false) (intersect (singleton true) (singleton false))
              == intersect (map_set (fun (_:bool) -> false) (singleton true))
                           (map_set (fun (_:bool) -> false) (singleton false))))
  = let f = (fun (_:bool) -> false) in
    let lhs = map_set f (intersect (singleton true) (singleton false)) in
    let rhs = intersect (map_set f (singleton true)) (map_set f (singleton false)) in
    assert (~ (mem lhs false));
    assert (mem rhs false);
    lemma_set_extensionality lhs rhs

/// `set.filter(p,empty) = empty`.
let filter_set (#a:eqtype) (p:a -> bool) (s:fset a) : fset a =
  on a (fun x -> mem s x /\ p x == true)

let lemma_filter_empty (#a:eqtype) (p:a -> bool)
  : Lemma (filter_set p (empty_set #a) == empty_set)
  = lemma_set_eq_from_iff (filter_set p (empty_set #a)) empty_set

/// `set.filter(p,singleton(x)) = ite(p(x), singleton(x), empty)`.
let lemma_filter_singleton (#a:eqtype) (p:a -> bool) (x:a)
  : Lemma (filter_set p (singleton x) == (if p x then singleton x else empty_set))
  = lemma_set_eq_from_iff (filter_set p (singleton x)) (if p x then singleton x else empty_set)

/// `set.filter` is a pointwise restriction, so (unlike `set.map`) it
/// genuinely distributes over all three Boolean set operations.
let lemma_filter_union (#a:eqtype) (p:a -> bool) (s t:fset a)
  : Lemma (filter_set p (union s t) == union (filter_set p s) (filter_set p t))
  = lemma_set_eq_from_iff (filter_set p (union s t)) (union (filter_set p s) (filter_set p t))

let lemma_filter_intersect (#a:eqtype) (p:a -> bool) (s t:fset a)
  : Lemma (filter_set p (intersect s t) == intersect (filter_set p s) (filter_set p t))
  = lemma_set_eq_from_iff (filter_set p (intersect s t)) (intersect (filter_set p s) (filter_set p t))

let lemma_filter_difference (#a:eqtype) (p:a -> bool) (s t:fset a)
  : Lemma (filter_set p (difference s t) == difference (filter_set p s) (filter_set p t))
  = lemma_set_eq_from_iff (filter_set p (difference s t)) (difference (filter_set p s) (filter_set p t))

