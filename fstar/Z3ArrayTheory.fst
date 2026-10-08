module Z3ArrayTheory

(*
   F star formalization of the rewrite rules in
   src/ast/rewriter/array_rewriter.cpp (`array_rewriter::mk_app_core`,
   `mk_store_core`, `mk_select_core`, `mk_select_same_store`,
   `mk_lambda_core`, `mk_map_core`, the `mk_set_*` family, and
   `mk_eq_core`).

   Z3 models an array sort `(Array I V)` as an *extensional* function from
   index to value: `select`/`store`/`const`/`map`/array-`lambda` are its
   function-application/update/constant/pointwise-lift/abstraction
   operations, and two arrays are equal iff they agree pointwise
   (extensionality). This is precisely what
   `FStar.FunctionalExtensionality`'s restricted-arrow type `idx ^-> v`
   provides: a function type whose `==` *is* pointwise equality (the
   `extensionality` axiom), together with `on`/`on_domain` as the
   "build a function value" (array `lambda`) operation. We therefore model
   arrays directly as `idx ^-> v` rather than building a separate
   discriminated-union/finite-map datatype, so that Z3's array
   extensionality axiom is not a lemma we have to add, but the library's
   own main axiom applied to our `select`.
*)

open FStar.FunctionalExtensionality

(* ----------------------------------------------------------------- *)
(* Core representation                                                *)
(* ----------------------------------------------------------------- *)

/// An array from `idx` to `v`: a restricted (extensionally-quotiented)
/// function, matching Z3's `(Array idx v)` sort.
type arr (idx:eqtype) (v:Type) = idx ^-> v

/// `(select a i)` -- function application.
let select (#idx:eqtype) (#v:Type) (a:arr idx v) (i:idx) : v = a i

/// `(store a i x)` -- functional update at `i`, matching `OP_STORE`.
let store (#idx:eqtype) (#v:Type) (a:arr idx v) (i:idx) (x:v) : arr idx v =
  on idx (fun j -> if j = i then x else a j)

/// `((as const (Array idx v)) c)` -- the constant array, matching
/// `OP_CONST_ARRAY`.
let const_arr (#idx:eqtype) (#v:Type) (c:v) : arr idx v = on idx (fun _ -> c)

/// `((_ map f) a1 a2)` -- pointwise lift of a binary function, matching
/// `OP_ARRAY_MAP`; n-ary maps are compositions of this (and the unary
/// `map1` below), which suffices to justify every map identity
/// `array_rewriter.cpp` proves (store-pushing, lambda-pushing, set
/// union/intersection/complement/difference, all of which are unary or
/// binary `f`).
let map1 (#idx:eqtype) (#v1 #v2:Type) (f:v1 -> v2) (a:arr idx v1) : arr idx v2 =
  on idx (fun i -> f (a i))

let map2 (#idx:eqtype) (#v1 #v2 #v3:Type) (f:v1 -> v2 -> v3) (a1:arr idx v1) (a2:arr idx v2) : arr idx v3 =
  on idx (fun i -> f (a1 i) (a2 i))

/// Term-level `ite` lifted to arrays (`mk_select_core`'s `select(ite c a1
/// a2, J) --> ite(c, select(a1,J), select(a2,J))` rewrite acts on an array
/// whose outermost constructor is a boolean `ite`; we model that `ite`
/// directly as an F* conditional on the two array *values*, since Z3's
/// term-level `ite` between two closed array terms denotes exactly one of
/// the two arrays depending on `c`).
let arr_ite (#idx:eqtype) (#v:Type) (c:bool) (a1 a2:arr idx v) : arr idx v = if c then a1 else a2

(* ----------------------------------------------------------------- *)
(* mk_select_core / mk_select_same_store / mk_store_core               *)
(* ----------------------------------------------------------------- *)

/// `select(store(a,I,v),I) = v` -- `mk_select_same_store`'s `l_true` case.
let lemma_select_store_same (#idx:eqtype) (#v:Type) (a:arr idx v) (i:idx) (x:v)
  : Lemma (select (store a i x) i == x) = ()

/// `select(store(a,I,v),J) = select(a,J)` for `I <> J` --
/// `mk_select_same_store`'s `l_false` case / `mk_select_core`'s main case.
let lemma_select_store_diff (#idx:eqtype) (#v:Type) (a:arr idx v) (i j:idx) (x:v)
  : Lemma (requires j <> i) (ensures select (store a i x) j == select a j) = ()

/// `select(const(c),I) = c` -- `mk_select_same_store`'s `is_const` case.
let lemma_select_const (#idx:eqtype) (#v:Type) (c:v) (i:idx)
  : Lemma (select (const_arr #idx c) i == c) = ()

/// `select(ite(c,a1,a2),J) = ite(c, select(a1,J), select(a2,J))` --
/// `mk_select_core`'s `is_ite` expansion.
let lemma_select_ite (#idx:eqtype) (#v:Type) (c:bool) (a1 a2:arr idx v) (i:idx)
  : Lemma (select (arr_ite c a1 a2) i == (if c then select a1 i else select a2 i)) = ()

/// `store(store(a,I,v),I,w) = store(a,I,w)` -- `mk_store_core`'s
/// `l_true`/duplicate-index case (and `squash_store`'s general n-level
/// dedup collapses to repeated applications of this one-step identity).
let lemma_store_same_twice (#idx:eqtype) (#v:Type) (a:arr idx v) (i:idx) (x y:v)
  : Lemma (store (store a i x) i y == store a i y)
  = assert (feq (store (store a i x) i y) (store a i y))

/// `store(store(a,I,v),J,w) = store(store(a,J,w),I,v)` for `I <> J` --
/// `mk_store_core`'s `l_false`/`m_sort_store` index-swap case.
let lemma_store_commute (#idx:eqtype) (#v:Type) (a:arr idx v) (i j:idx) (x y:v)
  : Lemma (requires i <> j) (ensures store (store a i x) j y == store (store a j y) i x)
  = assert (feq (store (store a i x) j y) (store (store a j y) i x))

/// `store(a,I,select(a,I)) = a` -- `mk_store_core`'s
/// "writing back the value already there" identity.
let lemma_store_redundant (#idx:eqtype) (#v:Type) (a:arr idx v) (i:idx)
  : Lemma (store a i (select a i) == a)
  = assert (feq (store a i (select a i)) a)

/// `store(const(v),I,v) = const(v)` -- `mk_store_core`'s
/// "storing the same constant" identity.
let lemma_store_const_same (#idx:eqtype) (#v:Type) (c:v) (i:idx)
  : Lemma (store (const_arr #idx c) i c == const_arr c)
  = assert (feq (store (const_arr #idx c) i c) (const_arr c))

(* ----------------------------------------------------------------- *)
(* mk_lambda_core : array eta-reduction and "lambda is select"         *)
(* ----------------------------------------------------------------- *)

/// `select(on(idx,f), I) = f(I)` -- "beta reduction": selecting an array
/// built from a lambda abstraction yields the body applied to the index
/// (`mk_select_same_store`'s `is_lambda` anywhere-reduction case).
let lemma_select_lambda (#idx:eqtype) (#v:Type) (f:idx -> v) (i:idx)
  : Lemma (select (on idx f) i == f i) = ()

/// `on(idx, fun i -> select(a,i)) = a` -- array eta-reduction:
/// `(lambda (x) (select a x)) --> a`, `mk_lambda_core`'s only rewrite,
/// sound here simply because `a` is already a restricted function (an
/// `arr idx v`), so abstracting-then-reapplying it is the identity.
let lemma_lambda_eta (#idx:eqtype) (#v:Type) (a:arr idx v)
  : Lemma (on idx (fun i -> select a i) == a)
  = assert (is_restricted idx a);
    assert (feq (on idx (fun i -> select a i)) a)

(* ----------------------------------------------------------------- *)
(* mk_map_core : pointwise-lift identities                             *)
(* ----------------------------------------------------------------- *)

/// `select(map_f(a1,a2), I) = f(select(a1,I), select(a2,I))` -- the
/// defining property of `map` that every `mk_map_core` rewrite relies on.
let lemma_select_map2 (#idx:eqtype) (#v1 #v2 #v3:Type) (f:v1 -> v2 -> v3) (a1:arr idx v1) (a2:arr idx v2) (i:idx)
  : Lemma (select (map2 f a1 a2) i == f (select a1 i) (select a2 i)) = ()

let lemma_select_map1 (#idx:eqtype) (#v1 #v2:Type) (f:v1 -> v2) (a:arr idx v1) (i:idx)
  : Lemma (select (map1 f a) i == f (select a i)) = ()

/// `map_f(store(a1,J,v1), store(a2,J,v2)) = store(map_f(a1,a2), J, f(v1,v2))`
/// -- `mk_map_core`'s "same store index" push-through-store rewrite.
let lemma_map2_store
    (#idx:eqtype) (#v1 #v2 #v3:Type) (f:v1 -> v2 -> v3)
    (a1:arr idx v1) (a2:arr idx v2) (j:idx) (x1:v1) (x2:v2)
  : Lemma (map2 f (store a1 j x1) (store a2 j x2) == store (map2 f a1 a2) j (f x1 x2))
  = assert (feq (map2 f (store a1 j x1) (store a2 j x2)) (store (map2 f a1 a2) j (f x1 x2)))

/// `map_f(const(c1), const(c2)) = const(f(c1,c2))` -- `mk_map_core`'s
/// all-constant-arguments case.
let lemma_map2_const (#idx:eqtype) (#v1 #v2 #v3:Type) (f:v1 -> v2 -> v3) (c1:v1) (c2:v2)
  : Lemma (map2 f (const_arr #idx c1) (const_arr c2) == const_arr (f c1 c2))
  = assert (feq (map2 f (const_arr #idx c1) (const_arr c2)) (const_arr (f c1 c2)))

/// `map_f(on(idx,g1), on(idx,g2)) = on(idx, fun i -> f(g1 i, g2 i))` --
/// `mk_map_core`'s "all arguments are lambdas" push-through-lambda case.
let lemma_map2_lambda (#idx:eqtype) (#v1 #v2 #v3:Type) (f:v1 -> v2 -> v3) (g1:idx -> v1) (g2:idx -> v2)
  : Lemma (map2 f (on idx g1) (on idx g2) == on idx (fun i -> f (g1 i) (g2 i)))
  = assert (feq (map2 f (on idx g1) (on idx g2)) (on idx (fun i -> f (g1 i) (g2 i))))

(* ----------------------------------------------------------------- *)
(* mk_eq_core : array extensionality                                   *)
(* ----------------------------------------------------------------- *)

/// `a = b <=> (forall i. select(a,i) = select(b,i))` -- Z3's array
/// extensionality axiom, which underlies every branch of `mk_eq_core`
/// (`const = const` reducing to value equality, `const = lambda` /
/// `lambda = lambda` reducing to a `forall`-quantified equation, and the
/// general `has_index_set` finite-domain expansion). This is exactly
/// `FStar.FunctionalExtensionality`'s `extensionality` axiom applied to
/// `select`.
let lemma_array_extensionality (#idx:eqtype) (#v:Type) (a b:arr idx v)
  : Lemma ((a == b) <==> (forall i. select a i == select b i))
  = extensionality idx (fun _ -> v) a b

(* ----------------------------------------------------------------- *)
(* mk_set_union / mk_set_intersect / mk_set_complement /               *)
(* mk_set_difference / mk_set_subset -- sets as boolean-valued arrays   *)
(* ----------------------------------------------------------------- *)

let set_t (idx:eqtype) = arr idx bool

/// `union(a,b) = map_or(a,b)` -- `mk_set_union`'s definition.
let set_union (#idx:eqtype) (a b:set_t idx) : set_t idx = map2 ( || ) a b

/// `intersect(a,b) = map_and(a,b)` -- `mk_set_intersect`'s definition.
let set_intersect (#idx:eqtype) (a b:set_t idx) : set_t idx = map2 ( && ) a b

/// `complement(a) = map_not(a)` -- `mk_set_complement`'s definition.
let set_complement (#idx:eqtype) (a:set_t idx) : set_t idx = map1 ( not ) a

/// `difference(a,b) = intersect(a, complement(b))` -- `mk_set_difference`'s
/// definition.
let set_difference (#idx:eqtype) (a b:set_t idx) : set_t idx = set_intersect a (set_complement b)

/// `subset(a,b) <=> difference(a,b) = empty` -- `mk_set_subset`'s
/// definition, proved equivalent to the expected pointwise subset relation.
let set_subset_iff
    (#idx:eqtype) (a b:set_t idx)
  : Lemma ((set_difference a b == const_arr false) <==> (forall i. select a i ==> select b i))
  = let aux (i:idx) : Lemma (select (set_difference a b) i == (select a i && not (select b i))) = () in
    FStar.Classical.forall_intro aux;
    lemma_array_extensionality (set_difference a b) (const_arr #idx false)

let lemma_set_complement_select (#idx:eqtype) (a:set_t idx) (i:idx)
  : Lemma (select (set_complement a) i == not (select a i)) = ()

let lemma_set_union_select (#idx:eqtype) (a b:set_t idx) (i:idx)
  : Lemma (select (set_union a b) i == (select a i || select b i)) = ()

let lemma_set_intersect_select (#idx:eqtype) (a b:set_t idx) (i:idx)
  : Lemma (select (set_intersect a b) i == (select a i && select b i)) = ()

(* ----------------------------------------------------------------- *)
(* mk_eq_core : array extensionality (continued)                       *)
(* ----------------------------------------------------------------- *)

/// `const(c1) = const(c2) <=> c1 = c2` -- `mk_eq_core`'s
/// "both sides are `const`" case. (SMT-LIB sorts are always non-empty,
/// so we take an index witness `i0` to rule out the vacuous case where
/// `idx` itself is uninhabited.)
let lemma_eq_const_const (#idx:eqtype) (#v:Type) (i0:idx) (c1 c2:v)
  : Lemma ((const_arr #idx c1 == const_arr c2) <==> c1 == c2)
  = lemma_array_extensionality (const_arr #idx c1) (const_arr c2)

/// `const(c) = on(idx,f) <=> (forall i. f(i) = c)` -- `mk_eq_core`'s
/// "one side `const`, the other a `lambda`" case (rewritten to
/// `forall x. body = v`).
let lemma_eq_const_lambda (#idx:eqtype) (#v:Type) (c:v) (f:idx -> v)
  : Lemma ((const_arr #idx c == on idx f) <==> (forall i. f i == c))
  = lemma_array_extensionality (const_arr #idx c) (on idx f)

/// `on(idx,f) = on(idx,g) <=> (forall i. f(i) = g(i))` -- `mk_eq_core`'s
/// "both sides `lambda`" case (array extensionality specialized to two
/// lambda-built arrays).
let lemma_eq_lambda_lambda (#idx:eqtype) (#v:Type) (f g:idx -> v)
  : Lemma ((on idx f == on idx g) <==> (forall i. f i == g i))
  = lemma_array_extensionality (on idx f) (on idx g)
