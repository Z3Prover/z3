module Z3DatatypeTheory

(*
   F star formalization of the rewrite rules in
   src/ast/rewriter/datatype_rewriter.cpp (`datatype_rewriter::mk_app_core`
   and `datatype_rewriter::mk_eq_core`).

   Z3's algebraic datatypes are free algebras: a value of a datatype sort is
   a constructor tag together with the list of field values it was built
   from (`OP_DT_CONSTRUCTOR`), with no further identifications ("no junk, no
   confusion"). We model this directly: a value of an `nctors`-constructor
   datatype is a dependent pair of a tag `c < nctors` and a (flat) list of
   field values of an abstract type `a` -- flat/one-level because
   datatype_rewriter.cpp's rewrites are all *local*, firing on a single
   `mk_app_core`/`mk_eq_core` call rather than recursing into sub-structure;
   recursive descent through nested constructors is handled elsewhere by the
   generic `rewriter` engine applying these same local rules bottom-up, so a
   one-level model suffices to justify every rewrite below.

   `OP_DT_RECOGNISER`, `OP_DT_ACCESSOR`, `OP_DT_UPDATE_FIELD` and the
   constructor-based `mk_eq_core` short-circuit are all modeled and proved
   below; `OP_DT_SUBTERM` has no rewrite in datatype_rewriter.cpp (`return
   BR_FAILED`) and so needs no lemma.
*)

open FStar.List.Tot

(* ----------------------------------------------------------------- *)
(* Core representation                                                *)
(* ----------------------------------------------------------------- *)

/// A value of an `nctors`-constructor datatype: a tag identifying which
/// constructor built it, plus the list of field values passed to that
/// constructor (`OP_DT_CONSTRUCTOR`'s arguments).
type dtval (a:Type) (nctors:pos) = (n:nat{n < nctors} & list a)

let mk_dtval (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (args:list a) : dtval a nctors =
  (| c, args |)

let tag_of (#a:Type) (#nctors:pos) (v:dtval a nctors) : nat = dfst v
let args_of (#a:Type) (#nctors:pos) (v:dtval a nctors) : list a = dsnd v

/// Replace the element at index `i` of a list, leaving all others
/// unchanged -- the structural core of `OP_DT_UPDATE_FIELD`.
let rec list_set (#a:Type) (l:list a) (i:nat{i < length l}) (w:a) : list a =
  match l with
  | x :: xs -> if i = 0 then w :: xs else x :: list_set xs (i - 1) w

let rec list_set_length (#a:Type) (l:list a) (i:nat{i < length l}) (w:a)
  : Lemma (ensures length (list_set l i w) == length l) (decreases l)
          [SMTPat (length (list_set l i w))]
  = match l with
    | x :: xs -> if i = 0 then () else list_set_length xs (i - 1) w

let rec list_set_nth (#a:Type) (l:list a) (i:nat{i < length l}) (w:a) (j:nat)
  : Lemma (ensures nth (list_set l i w) j == (if j = i then Some w else nth l j))
          (decreases l)
  = match l with
    | x :: xs -> if i = 0 || j = 0 then () else list_set_nth xs (i - 1) w (j - 1)

/// Equal tag and equal (extensionally) argument lists is exactly value
/// equality for `dtval` (the datatype axiom of "no confusion": two
/// applications of the *same* constructor are equal iff all arguments are).
let lemma_dtval_eq (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (args1 args2:list a)
  : Lemma (mk_dtval #a #nctors c args1 == mk_dtval c args2 <==> args1 == args2)
  = ()

(* ----------------------------------------------------------------- *)
(* OP_DT_RECOGNISER / OP_DT_IS                                        *)
(* ----------------------------------------------------------------- *)

/// `is_c(v)` -- true iff `v` was built with constructor `c`.
let recognize (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (v:dtval a nctors) : bool =
  tag_of v = c

/// `mk_app_core`'s `OP_DT_RECOGNISER` case rewrites the "tester" form
/// `f(x)` (where `f`'s recognized constructor is `c`) to `is_c(x)` --
/// i.e. the two notations denote the very same predicate, by definition:
/// `recognize` *is* that predicate, so no separate lemma is needed.

/// `is_c(mk_c(args)) = true` -- `OP_DT_IS`'s matching-constructor branch.
let lemma_recognize_match (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (args:list a)
  : Lemma (recognize c (mk_dtval #a #nctors c args) == true) = ()

/// `is_c(mk_d(args)) = false` for `c <> d` -- `OP_DT_IS`'s
/// mismatched-constructor branch.
let lemma_recognize_mismatch
    (#a:Type) (#nctors:pos) (c d:nat{c < nctors /\ d < nctors}) (args:list a)
  : Lemma (requires c <> d) (ensures recognize c (mk_dtval #a #nctors d args) == false) = ()

/// `is_c(v) = true` unconditionally when the datatype has exactly one
/// constructor -- `OP_DT_IS`'s `get_datatype_num_constructors(...) == 1`
/// fast path.
let lemma_recognize_single_ctor (#a:Type) (v:dtval a 1) : Lemma (recognize 0 v == true) = ()

(* ----------------------------------------------------------------- *)
(* OP_DT_ACCESSOR                                                     *)
(* ----------------------------------------------------------------- *)

let rec index_is_nth (#a:Type) (l:list a) (i:nat{i < length l})
  : Lemma (ensures nth l i == Some (index l i)) (decreases l)
  = match l with
    | x :: xs -> if i = 0 then () else index_is_nth xs (i - 1)

/// `acc_{c,i}(mk_c(args)) = args[i]` -- `OP_DT_ACCESSOR`'s main case
/// (accessor applied to a matching constructor application selects the
/// corresponding argument).
let accessor (#a:Type) (#nctors:pos) (i:nat) (c:nat{c < nctors}) (v:dtval a nctors{tag_of v = c /\ i < length (args_of v)})
  : a = index (args_of v) i

let lemma_accessor_match
    (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (i:nat) (args:list a{i < length args})
  : Lemma (accessor i c (mk_dtval #a #nctors c args) == index args i) = ()

(* ----------------------------------------------------------------- *)
(* OP_DT_UPDATE_FIELD                                                 *)
(* ----------------------------------------------------------------- *)

/// `update_{c,i}(v, w)`: if `v`'s tag is `c`, replace field `i` by `w`;
/// otherwise `v` is returned unchanged -- `OP_DT_UPDATE_FIELD`'s
/// `c_decl != get_accessor_constructor(acc)` early-return (field `i` of
/// constructor `c` is not even present in a value of a different
/// constructor, so the update is a no-op).
let update_field
    (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (i:nat) (v:dtval a nctors) (w:a)
  : dtval a nctors =
  if tag_of v <> c then v
  else if i >= length (args_of v) then v
  else mk_dtval c (list_set (args_of v) i w)

/// Matching-constructor case: `update_{c,i}(mk_c(args), w) = mk_c(args[i:=w])`.
let lemma_update_match
    (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (i:nat) (args:list a{i < length args}) (w:a)
  : Lemma (update_field c i (mk_dtval #a #nctors c args) w == mk_dtval c (list_set args i w)) = ()

/// Mismatched-constructor case: updating a field that constructor `c` does
/// not own leaves the value unchanged.
let lemma_update_mismatch
    (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (i:nat) (v:dtval a nctors) (w:a)
  : Lemma (requires tag_of v <> c) (ensures update_field c i v w == v) = ()

/// `update_field` never changes which constructor built the value, in
/// *either* branch -- the key fact justifying `OP_DT_IS`'s
/// `is_cons(update_field(dt,val)) -> is_cons(dt)` rewrite for *every*
/// constructor `c'` being recognized, not just the single-constructor case.
let lemma_update_preserves_tag
    (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (i:nat) (v:dtval a nctors) (w:a)
  : Lemma (tag_of (update_field c i v w) == tag_of v) = ()

let lemma_is_update_field
    (#a:Type) (#nctors:pos) (c' c:nat{c' < nctors /\ c < nctors}) (i:nat) (v:dtval a nctors) (w:a)
  : Lemma (recognize c' (update_field c i v w) == recognize c' v) = ()

/// `acc_{c,i}(update_{c,i}(mk_c(args), w)) = w` -- reading back the field
/// that was just written (combines `lemma_update_match` with
/// `lemma_accessor_match`); this is the identity `OP_DT_ACCESSOR`'s
/// `update_field`/single-constructor branch relies on when `f == acc`.
let lemma_accessor_update_same
    (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (i:nat) (args:list a{i < length args}) (w:a)
  : Lemma (accessor i c (mk_dtval #a #nctors c (list_set args i w)) == w)
  = list_set_length args i w;
    list_set_nth args i w i;
    index_is_nth (list_set args i w) i

/// `acc_{c,j}(update_{c,i}(mk_c(args), w)) = acc_{c,j}(mk_c(args))` for
/// `j <> i` -- updating field `i` leaves every other field `j` unaffected;
/// this is the identity `OP_DT_ACCESSOR`'s `update_field`/
/// single-constructor branch relies on when `f <> acc` (`result = f(dt)`,
/// i.e. reading another field passes through to the pre-update value).
let lemma_accessor_update_other
    (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (i j:nat) (args:list a{i < length args /\ j < length args}) (w:a)
  : Lemma (requires j <> i)
          (ensures accessor j c (mk_dtval #a #nctors c (list_set args i w)) == accessor j c (mk_dtval #a #nctors c args))
  = list_set_length args i w;
    list_set_nth args i w j;
    index_is_nth (list_set args i w) j;
    index_is_nth args j

(* ----------------------------------------------------------------- *)
(* mk_eq_core : constructor (in)equality ("no confusion, no junk")    *)
(* ----------------------------------------------------------------- *)

/// `mk_c(args1) = mk_d(args2)` is `false` whenever `c <> d` --
/// `mk_eq_core`'s "different constructors" branch.
let lemma_eq_diff_ctor
    (#a:Type) (#nctors:pos) (c d:nat{c < nctors /\ d < nctors}) (args1 args2:list a)
  : Lemma (requires c <> d) (ensures mk_dtval #a #nctors c args1 =!= mk_dtval d args2) = ()

/// `mk_c(args1) = mk_c(args2)` iff `args1 = args2` pointwise --
/// `mk_eq_core`'s "same constructor" branch, which rewrites the equation
/// into the conjunction of the pairwise argument equalities
/// (`AND_i args1[i] = args2[i]`); list equality is exactly pointwise
/// equality plus equal length (`FStar.List.Tot.Properties`'s
/// extensionality for `list`, invoked implicitly through `==`).
let lemma_eq_same_ctor
    (#a:Type) (#nctors:pos) (c:nat{c < nctors}) (args1 args2:list a)
  : Lemma (mk_dtval #a #nctors c args1 == mk_dtval c args2 <==> args1 == args2) = ()
