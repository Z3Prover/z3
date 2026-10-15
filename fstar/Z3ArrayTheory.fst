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

(* ----------------------------------------------------------------- *)
(* A general multi-level store-permutation theorem                     *)
(* ----------------------------------------------------------------- *)

(* `lemma_store_commute` above is the n=2 instance of a much more
   general fact: a *chain* of `store`s with pairwise-distinct indices
   denotes the same array no matter what order the individual
   `(index, value)` updates are applied in. This section proves that
   general theorem, modelling a store-chain
   `store(store(...store(a,i1,x1)...),i_{n-1},x_{n-1}),in,xn)` as
   folding a list of updates `[(i1,x1); ...; (in,xn)]` (head = applied
   first/innermost, matching how nested `store` expressions are built)
   onto a base array `a`. *)

/// Fold a list of `(index,value)` updates onto `a`, left-to-right,
/// exactly mirroring how nested `store(store(...store(a,i1,x1)...)
/// ,in,xn)` is built: the head of the list is the *innermost* (first
/// applied) `store`, so later entries can overwrite earlier ones at
/// the same index.
let rec apply_updates (#idx:eqtype) (#v:Type) (a:arr idx v) (us:list (idx & v)) : Tot (arr idx v) (decreases us) =
  match us with
  | [] -> a
  | (i, x) :: rest -> apply_updates (store a i x) rest

/// `apply_updates a us` is itself a well-formed (restricted) array
/// value, just like its base `a` -- needed to let the extensionality
/// axiom's SMT pattern fire on `apply_updates a us1`/`...us2` below,
/// since (unlike `store`/`const_arr`, which are literally one `on`
/// unfold away from that pattern) `apply_updates` is not syntactically
/// in `on_domain` form while `us` is an abstract list. Proved by
/// induction so each recursive call re-introduces its `a` argument as
/// a *fresh* binder (which does carry its restricted-type refinement,
/// via `lemma_on_domain_refl` below -- a `let rec`'s own parameters
/// otherwise don't expose their refinement to the SMT encoding the
/// way a plain function call's do).
let lemma_on_domain_refl (#idx:eqtype) (#v:Type) (a:arr idx v)
  : Lemma (on_domain idx a == a) = ()

let rec lemma_apply_updates_restricted (#idx:eqtype) (#v:Type) (a:arr idx v) (us:list (idx & v))
  : Lemma (ensures on_domain idx (apply_updates a us) == apply_updates a us)
          (decreases us)
  = lemma_on_domain_refl a;
    match us with
    | [] -> ()
    | (i, x) :: rest -> lemma_apply_updates_restricted (store a i x) rest

/// The value a key `k` ends up with after folding `us` onto some base
/// array: the *last* (most-overriding) entry of `us` whose index is
/// `k`, if any.
let rec last_match (#idx:eqtype) (#v:Type) (k:idx) (us:list (idx & v)) : option v =
  match us with
  | [] -> None
  | (i, x) :: rest ->
    (match last_match k rest with
     | Some x' -> Some x'
     | None -> if i = k then Some x else None)

/// Pointwise characterization of `apply_updates`: selecting at `k`
/// after folding `us` onto `a` gives `last_match k us`'s answer (or
/// falls back to `select a k` if no entry of `us` touches `k`). Holds
/// unconditionally -- no distinctness needed, this is simply the
/// semantics of fold-left `store`.
let rec lemma_select_apply_updates (#idx:eqtype) (#v:Type) (a:arr idx v) (us:list (idx & v)) (k:idx)
  : Lemma (ensures select (apply_updates a us) k ==
                   (match last_match k us with Some x -> x | None -> select a k))
          (decreases us)
  = match us with
    | [] -> ()
    | (i, x) :: rest ->
      lemma_select_apply_updates (store a i x) rest k;
      (match last_match k rest with
       | Some x' -> ()
       | None -> if i = k then () else ())

/// An explicit witness, for a fixed `us`, that every occurrence of a
/// given index in `us` carries the same value. Passed around as a
/// first-class lemma (rather than stated as a bare `forall`) so every
/// call site instantiates it explicitly instead of relying on the SMT
/// solver to guess a multi-variable quantifier instantiation.
let key_distinct_hyp (idx:eqtype) (v:eqtype) (us:list (idx & v)) =
  i:idx -> x1:v -> x2:v ->
  Lemma (requires FStar.List.Tot.mem (i, x1) us /\ FStar.List.Tot.mem (i, x2) us) (ensures x1 == x2)

/// Restrict a `key_distinct_hyp` for `(i0,x0) :: us` down to `us`
/// (dropping the head only shrinks the set of pairs the hypothesis is
/// asked about, so the same witness function works unchanged).
let restrict_key_distinct_hyp (#idx:eqtype) (#v:eqtype) (i0:idx) (x0:v) (us:list (idx & v))
                               (distinct: key_distinct_hyp idx v ((i0, x0) :: us))
  : key_distinct_hyp idx v us
  = fun i x1 x2 -> distinct i x1 x2

/// If `last_match k us` is defined, its value really occurs as a pair
/// in `us`. Unconditional.
let rec lemma_last_match_mem (#idx:eqtype) (#v:eqtype) (k:idx) (us:list (idx & v))
  : Lemma (ensures (match last_match k us with
                     | Some x -> FStar.List.Tot.mem (k, x) us
                     | None -> True))
          (decreases us)
  = match us with
    | [] -> ()
    | (i, x) :: rest -> lemma_last_match_mem k rest

/// Converse direction, under key-uniqueness: if `(k,x)` occurs
/// anywhere in `us`, `last_match k us` must be exactly `Some x`.
let rec lemma_mem_last_match (#idx:eqtype) (#v:eqtype) (us:list (idx & v))
                              (distinct: key_distinct_hyp idx v us) (k:idx) (x:v)
  : Lemma (requires FStar.List.Tot.mem (k, x) us) (ensures last_match k us == Some x)
          (decreases us)
  = match us with
    | [] -> ()
    | (i, y) :: rest ->
      if FStar.List.Tot.mem (k, x) rest
      then lemma_mem_last_match rest (restrict_key_distinct_hyp i y rest distinct) k x
      else begin
        (* (k,x) must then be the head pair, i.e. i == k /\ y == x. *)
        assert (i == k /\ y == x);
        lemma_last_match_mem k rest;
        (* If `last_match k rest = Some z`, then `mem (k,z) rest`; key-
           uniqueness of `us` at index `k` (via `distinct`) then forces
           `z == x`, contradicting `~(mem (k,x) rest)`. So `last_match
           k rest` must be `None`, and the result follows. *)
        match last_match k rest with
        | Some z -> distinct k z x
        | None -> ()
      end

/// If `us1` and `us2` contain the same set of `(index,value)` pairs
/// and each has pairwise-distinct keys, `last_match` agrees on every
/// key -- hence (by `lemma_select_apply_updates`) so does `select
/// (apply_updates a us1)`/`select (apply_updates a us2)`.
let lemma_last_match_eq (#idx:eqtype) (#v:eqtype) (us1 us2:list (idx & v))
                         (same_set: (p:(idx & v) -> Lemma (FStar.List.Tot.mem p us1 <==> FStar.List.Tot.mem p us2)))
                         (distinct1: key_distinct_hyp idx v us1)
                         (distinct2: key_distinct_hyp idx v us2)
                         (k:idx)
  : Lemma (last_match k us1 == last_match k us2)
  = match last_match k us1, last_match k us2 with
    | Some x1, Some x2 ->
      lemma_last_match_mem k us1; lemma_last_match_mem k us2;
      same_set (k, x1); same_set (k, x2);
      distinct2 k x1 x2
    | Some x1, None ->
      lemma_last_match_mem k us1;
      same_set (k, x1);
      lemma_mem_last_match us2 distinct2 k x1
    | None, Some x2 ->
      lemma_last_match_mem k us2;
      same_set (k, x2);
      lemma_mem_last_match us1 distinct1 k x2
    | None, None -> ()

/// **The general multi-level store-permutation theorem.** If `us1`
/// and `us2` are two orderings of the *same set* of `(index,value)`
/// updates, each internally key-distinct, folding either one onto any
/// base array `a` gives the same result. `lemma_store_commute` above
/// is the special case `us1 = [(i,x);(j,y)]`, `us2 = [(j,y);(i,x)]`.
let lemma_apply_updates_set_eq (#idx:eqtype) (#v:eqtype) (a:arr idx v) (us1 us2:list (idx & v))
                                (same_set: (p:(idx & v) -> Lemma (FStar.List.Tot.mem p us1 <==> FStar.List.Tot.mem p us2)))
                                (distinct1: key_distinct_hyp idx v us1)
                                (distinct2: key_distinct_hyp idx v us2)
  : Lemma (apply_updates a us1 == apply_updates a us2)
  = let pointwise (k:idx)
      : Lemma (select (apply_updates a us1) k == select (apply_updates a us2) k)
      = lemma_select_apply_updates a us1 k;
        lemma_select_apply_updates a us2 k;
        lemma_last_match_eq us1 us2 same_set distinct1 distinct2 k
    in
    FStar.Classical.forall_intro pointwise;
    let r1 = apply_updates a us1 in
    let r2 = apply_updates a us2 in
    lemma_apply_updates_restricted a us1;
    lemma_apply_updates_restricted a us2;
    assert (feq r1 r2);
    extensionality idx (fun _ -> v) r1 r2

/// `apply_updates a (us @ [(ik,xk)]) == store (apply_updates a us) ik
/// xk` -- unfolds one `store` layer off the *end* of an update chain,
/// the fact the matcher's structural recursion (which peels nested
/// `store`s from the *outside* in) needs to connect `eval` of a real
/// store-chain expression to `apply_updates`.
let rec lemma_apply_updates_append (#idx:eqtype) (#v:Type) (a:arr idx v) (us:list (idx & v)) (ik:idx) (xk:v)
  : Lemma (ensures apply_updates a (us @ [(ik, xk)]) == store (apply_updates a us) ik xk)
          (decreases us)
  = match us with
    | [] -> ()
    | (i, x) :: rest -> lemma_apply_updates_append (store a i x) rest ik xk

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

(* Ground instances emitted by src/smt/theory_array_base.cpp. An index
   may itself be a tuple, covering the multi-index array operators. *)
let lemma_store_axiom2 (#idx:eqtype) (#v:Type) (a:arr idx v) (i j:idx) (x:v)
  : Lemma (i == j \/ select (store a i x) j == select a j)
  = if i = j then () else lemma_select_store_diff a i j x

let lemma_store_axiom2_coordinate (#idx #coordinate:eqtype) (#v:Type)
                                 (project:idx -> coordinate)
                                 (a:arr idx v) (i j:idx) (x:v)
  : Lemma (requires project i <> project j)
          (ensures select (store a i x) j == select a j)
  = lemma_select_store_diff a i j x

let lemma_select_congruent (#idx:eqtype) (#v:Type) (a b:arr idx v) (i:idx)
  : Lemma (requires a == b) (ensures select a i == select b i)
  = ()

let lemma_extensionality_witness (#idx:eqtype) (#v:Type) (a b:arr idx v)
  : Lemma (a == b \/ (exists (k:idx). ~(select a k == select b k)))
  = lemma_array_extensionality a b

let extensionality_index (#idx:eqtype) (#v:Type) (a b:arr idx v) (k:idx) : prop =
  ~(a == b) ==> ~(select a k == select b k)

let lemma_extensionality_index_exists (#idx:eqtype) (#v:Type)
                                     (inhabitant:idx) (a b:arr idx v)
  : Lemma (exists (k:idx). extensionality_index a b k)
  = lemma_extensionality_witness a b;
    FStar.Classical.excluded_middle (a == b);
    if a == b then
      FStar.Classical.exists_intro (extensionality_index a b) inhabitant
    else ()

let lemma_extensionality_axiom (#idx:eqtype) (#v:Type) (a b:arr idx v) (k:idx)
  : Lemma (requires extensionality_index a b k)
          (ensures a == b \/ ~(select a k == select b k))
  = ()

(* Pointwise constructors used by theory_array_full.cpp. *)
let as_array (#idx:eqtype) (#v:Type) (f:idx -> v) : arr idx v = on idx f

let lemma_select_as_array (#idx:eqtype) (#v:Type) (f:idx -> v) (i:idx)
  : Lemma (select (as_array f) i == f i)
  = ()

let rec select_arrays (#idx:eqtype) (#v:Type) (arrays:list (arr idx v)) (i:idx)
  : Tot (list v) (decreases arrays) =
  match arrays with
  | [] -> []
  | a :: rest -> select a i :: select_arrays rest i

let map_n (#idx:eqtype) (#v #w:Type) (f:list v -> w) (arrays:list (arr idx v))
  : arr idx w = on idx (fun i -> f (select_arrays arrays i))

let lemma_select_map_n (#idx:eqtype) (#v #w:Type)
                       (f:list v -> w) (arrays:list (arr idx v)) (i:idx)
  : Lemma (select (map_n f arrays) i == f (select_arrays arrays i))
  = ()

(* Defaults at a shared epsilon give the finite-domain and lambda/map
   instances. Store invariance additionally needs epsilon to be fresh;
   it is not an identity at an arbitrary fixed index. *)
let array_default (#idx:eqtype) (#v:Type) (epsilon:idx) (a:arr idx v) : v =
  select a epsilon

let lemma_default_const (#idx:eqtype) (#v:Type) (epsilon:idx) (x:v)
  : Lemma (array_default epsilon (const_arr x) == x)
  = lemma_select_const x epsilon

let lemma_default_as_array (#idx:eqtype) (#v:Type) (epsilon:idx) (f:idx -> v)
  : Lemma (array_default epsilon (as_array f) == f epsilon)
  = lemma_select_as_array f epsilon

let lemma_default_lambda (#idx:eqtype) (#v:Type) (epsilon:idx) (body:idx -> v)
  : Lemma (array_default epsilon (on idx body) == body epsilon)
  = lemma_select_lambda body epsilon

let lemma_default_map_n (#idx:eqtype) (#v #w:Type) (epsilon:idx)
                        (f:list v -> w) (arrays:list (arr idx v))
  : Lemma (array_default epsilon (map_n f arrays) ==
           f (select_arrays arrays epsilon))
  = lemma_select_map_n f arrays epsilon

let lemma_default_store_fresh (#idx:eqtype) (#v:Type)
                             (epsilon:idx) (a:arr idx v) (i:idx) (x:v)
  : Lemma (requires epsilon <> i)
          (ensures array_default epsilon (store a i x) == array_default epsilon a)
  = lemma_select_store_diff a i epsilon x

let lemma_default_store_singleton (#idx:eqtype) (#v:Type)
                                 (epsilon:idx) (a:arr idx v) (i:idx) (x:v)
  : Lemma (requires forall (j:idx). j == i)
          (ensures array_default epsilon (store a i x) == x)
  = lemma_select_store_same a i x

let diagonal (#idx:eqtype) (p q i:idx) : idx = if i = p then q else p

let lemma_diagonal_fresh (#idx:eqtype) (p q i:idx)
  : Lemma (requires p <> q) (ensures diagonal p q i <> i)
  = ()

let lemma_default_store_finite (#idx:eqtype) (#v:Type)
                              (epsilon p q:idx) (a:arr idx v) (i:idx) (x:v)
  : Lemma (requires p <> q)
          (ensures
            array_default epsilon (store a i x) == select (store a i x) epsilon /\
            array_default epsilon a == select a epsilon /\
            select (store a i x) (diagonal p q i) == select a (diagonal p q i))
  = lemma_diagonal_fresh p q i;
    lemma_select_store_diff a i (diagonal p q i) x

let rec integer_epsilon (indices:list int) : Tot int (decreases indices) =
  match indices with
  | [] -> 0
  | i :: rest ->
    let bound = integer_epsilon rest in
    (if i > bound then i else bound) + 1

let rec lemma_integer_epsilon_fresh (indices:list int) (i:int)
  : Lemma (requires FStar.List.Tot.mem i indices)
          (ensures i < integer_epsilon indices)
          (decreases indices)
  = match indices with
    | [] -> ()
    | j :: rest -> if i = j then () else lemma_integer_epsilon_fresh rest i

let lemma_choice_witness (#idx:eqtype) (inhabitant:idx) (predicate:arr idx bool)
  : Lemma (exists (c:idx). forall (i:idx). select predicate i ==> select predicate c)
  = FStar.Classical.excluded_middle (exists (i:idx). select predicate i);
    if exists (i:idx). select predicate i then ()
    else
      FStar.Classical.exists_intro
        (fun c -> forall (i:idx). select predicate i ==> select predicate c) inhabitant

let lemma_choice_axiom (#idx:eqtype) (predicate:arr idx bool) (choice:idx) (i:idx)
  : Lemma (requires (exists (j:idx). select predicate j) ==> select predicate choice)
          (ensures select predicate i ==> select predicate choice)
  = ()
