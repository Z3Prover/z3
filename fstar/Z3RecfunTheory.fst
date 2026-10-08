module Z3RecfunTheory

(*
   F star formalization of the termination argument underlying
   src/ast/rewriter/recfun_rewriter.cpp's `is_decreasing_arg` /
   `mk_app_core`'s recursive-function unfolding.

   `recfun_rewriter::mk_app_core` unfolds a recursive-function call
   `f(args)` into its (capture-avoiding-substituted) body whenever either
   (a) every argument is already a fully evaluated value (`safe_to_subst`
   from `m.is_value`), or (b) some argument position `i` is a ground
   constructor application *and* `is_decreasing_arg(f, i, true)` confirms
   that, across every recursive call to `f` inside the body, position `i`
   is threaded only through a *strict chain of datatype accessors* applied
   to the very same formal parameter.

   Case (a) needs no dedicated lemma: unfolding a fully-evaluated call is
   simply evaluating the function's definition, sound by definition of
   what the recursive definition means (the same "sound by construction"
   status as numeral constant-folding in the bit-vector/arithmetic
   rewriters). The capture-avoiding substitution step itself (`var_subst`)
   is the generic ground-term substitution congruence already proved in
   `Z3SimplifierTheory.fst` (`lemma_subst_cong`/`lemma_subst_cong_args`).

   Case (b)'s *termination* guarantee is the genuinely new content
   formalized here: a ground datatype value's accessor-field is always
   *strictly smaller* (by constructor nesting depth) than the value
   itself, so no sequence of such accessor-guarded unfoldings can
   continue forever -- doing so would produce an infinite strictly
   decreasing sequence of natural numbers, which is impossible. This is
   exactly the invariant `is_decreasing_arg`'s `allow_any_accessor` branch
   is designed to enforce (and the property that motivated tightening it,
   per the comment in recfun_rewriter.cpp, to reject a decreasing
   argument that is merely *rebuilt* by the body from unrelated data,
   e.g. `(f (tail s) (mk (proj_1 t) ...))`).
*)

open FStar.List.Tot

(* ----------------------------------------------------------------- *)
(* Ground datatype values and their structural size                   *)
(* ----------------------------------------------------------------- *)

/// A ground value of some (unspecified, possibly mutually recursive)
/// family of algebraic datatypes: a constructor tag plus the list of
/// field values it was built from -- the same free-algebra view as
/// `Z3DatatypeTheory.fst`'s `dtval`, but recursive (field values are
/// themselves `dval`s) so that nested constructor structure, and hence a
/// meaningful notion of "strictly smaller sub-value", is visible.
noeq type dval =
  | DCon : tag:nat -> args:list dval -> dval

/// The number of constructor applications nested inside `v` (including
/// `v` itself) -- a structural size measure. `size_list` sums the sizes
/// of a field list; both are defined by mutual recursion over the
/// (finite, well-founded) term structure.
let rec size (v:dval) : nat =
  match v with
  | DCon _ args -> 1 + size_list args
and size_list (l:list dval) : nat =
  match l with
  | [] -> 0
  | x :: xs -> size x + size_list xs

/// `nth` of a field list contributes at most the whole list's size.
let rec lemma_size_list_nth (l:list dval) (i:nat{i < length l})
  : Lemma (ensures (match nth l i with
                     | Some w -> size w <= size_list l
                     | None -> True))
          (decreases l)
  = match l with
    | x :: xs -> if i = 0 then () else lemma_size_list_nth xs (i - 1)

/// **Accessor strictly decreases size**: projecting field `i` out of a
/// constructor application `DCon tag args` always yields a value with
/// strictly smaller size than the whole term -- the structural fact
/// underlying every datatype accessor (`OP_DT_ACCESSOR`) and the one
/// `is_decreasing_arg` relies on for termination.
let lemma_accessor_decreases (tag:nat) (args:list dval) (i:nat{i < length args})
  : Lemma (requires Some? (nth args i))
          (ensures size (Some?.v (nth args i)) < size (DCon tag args))
  = lemma_size_list_nth args i

(* ----------------------------------------------------------------- *)
(* Strict accessor chains                                              *)
(* ----------------------------------------------------------------- *)

/// A single accessor step: project field `i` of a constructor
/// application, or fail (`None`) if `v` is not shaped that way or the
/// index is out of range -- modeling `recfun_rewriter.cpp`'s
/// `is_decreasing_arg` loop (`while (is_app(a) && u.is_accessor(a)) a =
/// to_app(a)->get_arg(0)`) one step at a time.
let accessor_step (v:dval) (i:nat) : option dval =
  match v with
  | DCon _ args -> if i < length args then nth args i else None

let lemma_accessor_step_decreases (v:dval) (i:nat)
  : Lemma (requires Some? (accessor_step v i))
          (ensures size (Some?.v (accessor_step v i)) < size v)
  = match v with
    | DCon tag args -> lemma_accessor_decreases tag args i

/// One step of unfolding the chain-fold over a `hd :: tl` list is
/// definitionally the fold over `tl` started from the result of applying
/// `hd` -- pure unfolding of `fold_left`'s recursive equation.
let lemma_fold_step (v:dval) (i:nat) (rest:list nat)
  : Lemma (fold_left (fun acc j -> match acc with Some w -> accessor_step w j | None -> None)
                      (Some v) (i :: rest)
           == fold_left (fun acc j -> match acc with Some w -> accessor_step w j | None -> None)
                         (accessor_step v i) rest)
  = ()

/// Folding from `None` always stays `None`.
let rec lemma_fold_none (rest:list nat)
  : Lemma (ensures fold_left (fun acc j -> match acc with Some w -> accessor_step w j | None -> None)
                              None rest == None)
          (decreases rest)
  = match rest with
    | [] -> ()
    | _ :: tl -> lemma_fold_none tl

/// Applying a *nonempty* list of accessor steps (a "strict chain",
/// matching `is_decreasing_arg`'s `strict` flag) to `v`, when it
/// succeeds, yields a value strictly smaller than `v`.
let rec lemma_chain_decreases (v:dval) (steps:list nat{Cons? steps})
  : Lemma (requires Some? (fold_left (fun acc i -> match acc with
                                                     | Some w -> accessor_step w i
                                                     | None -> None)
                                      (Some v) steps))
          (ensures size (Some?.v (fold_left (fun acc i -> match acc with
                                                            | Some w -> accessor_step w i
                                                            | None -> None)
                                             (Some v) steps))
                   < size v)
          (decreases steps)
  = match steps with
    | [i] -> lemma_accessor_step_decreases v i
    | i :: rest ->
      lemma_fold_step v i rest;
      (match accessor_step v i with
       | None -> lemma_fold_none rest
       | Some w -> lemma_accessor_step_decreases v i; lemma_chain_decreases w rest)

(* ----------------------------------------------------------------- *)
(* No infinite strictly-decreasing chain of unfoldings                 *)
(* ----------------------------------------------------------------- *)

/// There is no function `nat -> nat` that strictly decreases at every
/// step: this is just well-foundedness of `<` on `nat`, stated in the
/// form directly usable below.
let rec lemma_no_infinite_descent (f:nat -> nat) (n:nat)
  : Lemma (requires (forall (i:nat). f (i + 1) < f i))
          (ensures False)
          (decreases (f n))
  = lemma_no_infinite_descent f (n + 1)

/// **Termination of accessor-guarded recursive unfolding.** If repeatedly
/// unfolding a recursive call produced an infinite sequence of ground
/// datatype values `val_at 0, val_at 1, ...` for the decreasing argument,
/// each obtained from the previous by a nonempty strict accessor chain
/// (exactly what `is_decreasing_arg(f, i, true)` certifies holds for
/// every recursive call in `f`'s body), this would give an infinite
/// strictly-decreasing sequence of sizes -- impossible. Hence no such
/// infinite unfolding sequence exists: the rewrite terminates.
let lemma_decreasing_arg_unfolding_terminates
    (val_at:nat -> dval)
    (step_at:nat -> (steps:list nat{Cons? steps}))
    (chain_connects:
       (n:nat -> Lemma
         (Some? (fold_left (fun acc i -> match acc with
                                          | Some w -> accessor_step w i
                                          | None -> None)
                            (Some (val_at n)) (step_at n)) /\
          Some?.v (fold_left (fun acc i -> match acc with
                                            | Some w -> accessor_step w i
                                            | None -> None)
                              (Some (val_at n)) (step_at n))
          == val_at (n + 1))))
  : Lemma False
  = let f (n:nat) : nat = size (val_at n) in
    let aux (n:nat) : Lemma (f (n + 1) < f n) =
      chain_connects n;
      lemma_chain_decreases (val_at n) (step_at n)
    in
    FStar.Classical.forall_intro aux;
    lemma_no_infinite_descent f 0
