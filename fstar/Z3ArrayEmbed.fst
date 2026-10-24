(*
   Z3ArrayEmbed.fst

   Task: "redo how rewrite proof steps are checked" -- instead of only
   *verifying* a given candidate pair `(s, t)` against a theory lemma
   (`Z3PatternMatchedProofChecker.fst`'s `match_x`/`lemma_x_leaf_sound`
   family), this file *synthesizes* the rewritten side from just one
   expression. For every array-theory equality lemma `lemma_x a = b`
   with side condition `cond(a,b)` already matched by that file, this
   module exports:

     apply_lemma_x : expr -> option expr

   such that `Some s = apply_lemma_x t` implies `cond(eval t, eval s)`
   holds and `eval t == eval s`, justified by `lemma_x` -- i.e.
   `apply_lemma_x` is a *verified rewrite-rule application*: feed it a
   term matching `lemma_x`'s left-hand schema, get back the
   right-hand side the theory lemma proves it equal to (or `None` if
   it doesn't match, or a required side condition like index
   disequality fails to syntactically discharge).

   Covers five of `Z3PatternMatchedProofChecker.fst`'s eleven array
   patterns -- `select_store_same`, `store_same_twice`,
   `store_redundant`, `select_store_diff`, `store_commute`. The
   twelfth, `store_perm`, is deliberately **not** given an
   `apply_lemma_store_perm` here: it is not a *function* of its input
   in the first place. Given an `n`-level nested `store` chain with
   pairwise-distinct indices, `Z3ArrayTheory.lemma_apply_updates_set_eq`
   proves it equal to *any* of the `n!` reorderings of the same
   updates, not a single canonical one, so there is no well-defined
   single `s` an `expr -> option expr` signature could return. (The
   two-level special case, `store_commute`, *is* a function: there is
   only one other order to swap to, so `apply_lemma_store_commute`
   below returns that unique swap.)
*)
module Z3ArrayEmbed
open Z3AstTheory
open Z3ValueTheory
open Z3InterpretedProofChecker
open Z3PatternMatchedProofChecker
open FStar.List.Tot

(* ----------------------------------------------------------------- *)
(* `select(store(a,i,x),i) = x` -- `Z3ArrayTheory.lemma_select_store_same`.
   `apply_lemma_select_store_same t` recognizes `t`'s shape and, when
   every side condition `select_store_same_leaf_ok` would also check
   (shape + sort + wf/closed/decls_ok/no_quant) holds, returns the
   matched `x`. *)

let apply_lemma_select_store_same (t:expr) : option expr =
  match t with
  | App f_sel [App f_sto [a; idx1; x]; idx2] ->
    if Some? f_sel.interp && Some?.v f_sel.interp = op_select &&
       Some? f_sto.interp && Some?.v f_sto.interp = op_store &&
       idx1 = idx2 &&
       wf t && closed t && decls_ok t && no_quant t &&
       sort_eq (get_sort a) arr_s && sort_eq (get_sort idx1) int_s && sort_eq (get_sort x) int_s
    then Some x
    else None
  | _ -> None

let lemma_apply_lemma_select_store_same_sound (t:expr) (rho:env value)
  : Lemma (requires Some? (apply_lemma_select_store_same t))
          (ensures eval the_interpretation t rho ==
                   eval the_interpretation (Some?.v (apply_lemma_select_store_same t)) rho)
  = match t with
    | App f_sel [App f_sto [a; idx1; x]; idx2] ->
      lemma_eval_shape a rho;
      lemma_eval_shape idx1 rho;
      lemma_eval_shape x rho;
      (match eval the_interpretation a rho, eval the_interpretation idx1 rho, eval the_interpretation x rho with
       | VArr av, VInt iv, VInt xv -> Z3ArrayTheory.lemma_select_store_same av iv xv
       | _, _, _ -> ())
    | _ -> ()

(* ----------------------------------------------------------------- *)
(* `store(store(a,i,x),i,y) = store(a,i,y)` --
   `Z3ArrayTheory.lemma_store_same_twice`. *)

let apply_lemma_store_same_twice (t:expr) : option expr =
  match t with
  | App f1 [App f2 [a; i1; x]; i2; y] ->
    if Some? f1.interp && Some?.v f1.interp = op_store &&
       Some? f2.interp && Some?.v f2.interp = op_store &&
       i1 = i2 &&
       wf t && closed t && decls_ok t && no_quant t &&
       sort_eq (get_sort a) arr_s && sort_eq (get_sort i1) int_s &&
       sort_eq (get_sort x) int_s && sort_eq (get_sort y) int_s
    then Some (App f1 [a; i1; y])
    else None
  | _ -> None

#push-options "--z3rlimit 50"
let lemma_apply_lemma_store_same_twice_sound (t:expr) (rho:env value)
  : Lemma (requires Some? (apply_lemma_store_same_twice t))
          (ensures eval the_interpretation t rho ==
                   eval the_interpretation (Some?.v (apply_lemma_store_same_twice t)) rho)
  = match t with
    | App f1 [App f2 [a; i1; x]; i2; y] ->
      lemma_eval_shape a rho;
      lemma_eval_shape i1 rho;
      lemma_eval_shape x rho;
      lemma_eval_shape y rho;
      (match eval the_interpretation a rho, eval the_interpretation i1 rho,
             eval the_interpretation x rho, eval the_interpretation y rho with
       | VArr av, VInt iv, VInt xv, VInt yv -> Z3ArrayTheory.lemma_store_same_twice av iv xv yv
       | _, _, _, _ -> ())
    | _ -> ()
#pop-options

(* ----------------------------------------------------------------- *)
(* `store(a,i,select(a,i)) = a` -- `Z3ArrayTheory.lemma_store_redundant`. *)

let apply_lemma_store_redundant (t:expr) : option expr =
  match t with
  | App f_sto [a; i; App f_sel [a2; i2]] ->
    if Some? f_sto.interp && Some?.v f_sto.interp = op_store &&
       Some? f_sel.interp && Some?.v f_sel.interp = op_select &&
       a = a2 && i = i2 &&
       wf t && closed t && decls_ok t && no_quant t &&
       sort_eq (get_sort a) arr_s && sort_eq (get_sort i) int_s
    then Some a
    else None
  | _ -> None

let lemma_apply_lemma_store_redundant_sound (t:expr) (rho:env value)
  : Lemma (requires Some? (apply_lemma_store_redundant t))
          (ensures eval the_interpretation t rho ==
                   eval the_interpretation (Some?.v (apply_lemma_store_redundant t)) rho)
  = match t with
    | App f_sto [a; i; App f_sel [a2; i2]] ->
      lemma_eval_shape a rho;
      lemma_eval_shape i rho;
      (match eval the_interpretation a rho, eval the_interpretation i rho with
       | VArr av, VInt iv -> Z3ArrayTheory.lemma_store_redundant av iv
       | _, _ -> ())
    | _ -> ()

(* ----------------------------------------------------------------- *)
(* `select(store(a,i,x),j) = select(a,j)` for `i <> j` --
   `Z3ArrayTheory.lemma_select_store_diff`. The side condition
   `cond(a,b)` here is the genuine semantic one, `i <> j`, discharged
   syntactically via `Z3PatternMatchedProofChecker.provably_distinct`
   (named-uninterpreted-constant or literal/unique-value
   disequality). *)

let apply_lemma_select_store_diff (t:expr) : option expr =
  match t with
  | App f_sel1 [App f_sto [a; i; x]; j] ->
    if Some? f_sel1.interp && Some?.v f_sel1.interp = op_select &&
       Some? f_sto.interp && Some?.v f_sto.interp = op_store &&
       wf t && closed t && decls_ok t && no_quant t &&
       sort_eq (get_sort a) arr_s && sort_eq (get_sort i) int_s &&
       sort_eq (get_sort x) int_s && sort_eq (get_sort j) int_s &&
       provably_distinct i j
    then Some (App f_sel1 [a; j])
    else None
  | _ -> None

#push-options "--z3rlimit 80"
let lemma_apply_lemma_select_store_diff_sound (t:expr) (rho:env value)
  : Lemma (requires Some? (apply_lemma_select_store_diff t))
          (ensures eval the_interpretation t rho ==
                   eval the_interpretation (Some?.v (apply_lemma_select_store_diff t)) rho)
  = match t with
    | App f_sel1 [App f_sto [a; i; x]; j] ->
      lemma_eval_shape a rho;
      lemma_eval_shape i rho;
      lemma_eval_shape x rho;
      lemma_eval_shape j rho;
      lemma_provably_distinct_sound i j rho;
      (match eval the_interpretation a rho, eval the_interpretation i rho,
             eval the_interpretation x rho, eval the_interpretation j rho with
       | VArr av, VInt iv, VInt xv, VInt jv -> Z3ArrayTheory.lemma_select_store_diff av iv jv xv
       | _, _, _, _ -> ())
    | _ -> ()
#pop-options

(* ----------------------------------------------------------------- *)
(* `store(store(a,i,x),j,y) = store(store(a,j,y),i,x)` for `i <> j` --
   `Z3ArrayTheory.lemma_store_commute`, the unique two-level swap
   (see the module docstring for why the general `store_perm` theorem
   is *not* given an `apply_lemma_x` here). *)

let apply_lemma_store_commute (t:expr) : option expr =
  match t with
  | App f_sto1 [App f_sto2 [a; i; x]; j; y] ->
    if Some? f_sto1.interp && Some?.v f_sto1.interp = op_store &&
       Some? f_sto2.interp && Some?.v f_sto2.interp = op_store &&
       wf t && closed t && decls_ok t && no_quant t &&
       sort_eq (get_sort a) arr_s && sort_eq (get_sort i) int_s &&
       sort_eq (get_sort x) int_s && sort_eq (get_sort j) int_s && sort_eq (get_sort y) int_s &&
       provably_distinct i j
    then Some (App f_sto1 [App f_sto2 [a; j; y]; i; x])
    else None
  | _ -> None

#push-options "--z3rlimit 100"
let lemma_apply_lemma_store_commute_sound (t:expr) (rho:env value)
  : Lemma (requires Some? (apply_lemma_store_commute t))
          (ensures eval the_interpretation t rho ==
                   eval the_interpretation (Some?.v (apply_lemma_store_commute t)) rho)
  = match t with
    | App f_sto1 [App f_sto2 [a; i; x]; j; y] ->
      lemma_eval_shape a rho;
      lemma_eval_shape i rho;
      lemma_eval_shape x rho;
      lemma_eval_shape j rho;
      lemma_eval_shape y rho;
      lemma_provably_distinct_sound i j rho;
      (match eval the_interpretation a rho, eval the_interpretation i rho,
             eval the_interpretation x rho, eval the_interpretation j rho,
             eval the_interpretation y rho with
       | VArr av, VInt iv, VInt xv, VInt jv, VInt yv ->
         Z3ArrayTheory.lemma_store_commute av iv jv xv yv
       | _, _, _, _, _ -> ())
    | _ -> ()
#pop-options

(* ----------------------------------------------------------------- *)
(* `apply_lemmas t`: every successful single-step rewrite of `t` by
   one of the five lemmas above. `is_rewrite t s`: whether some
   `apply_lemma_x` maps `t` to exactly `s`. *)

let apply_lemmas (t:expr) : list expr =
  (match apply_lemma_select_store_same t with Some s -> [s] | None -> []) @
  (match apply_lemma_store_same_twice t with Some s -> [s] | None -> []) @
  (match apply_lemma_store_redundant t with Some s -> [s] | None -> []) @
  (match apply_lemma_select_store_diff t with Some s -> [s] | None -> []) @
  (match apply_lemma_store_commute t with Some s -> [s] | None -> [])

(* `is_rewrite` is defined directly as "some `apply_lemma_x` maps `t`
   to `s`" -- a disjunction over the same five lemmas, rather than via
   `mem s (apply_lemmas t)` (list membership would still be logically
   equivalent, but proving the aggregate soundness lemma below is far
   more direct against this definition: each disjunct is immediately
   dischargeable by its own `lemma_apply_lemma_x_sound`, with no extra
   list/`mem`/`append` reasoning needed). *)
let is_rewrite (t s:expr) : bool =
  apply_lemma_select_store_same t = Some s ||
  apply_lemma_store_same_twice t = Some s ||
  apply_lemma_store_redundant t = Some s ||
  apply_lemma_select_store_diff t = Some s ||
  apply_lemma_store_commute t = Some s

(* Soundness of `is_rewrite`: whenever it holds, `t` and `s` are
   semantically equal under every environment -- by case split on
   which disjunct of `is_rewrite` fired, dispatching to that
   particular `apply_lemma_x`'s own soundness lemma. *)
let lemma_is_rewrite_sound (t s:expr) (rho:env value)
  : Lemma (requires is_rewrite t s)
          (ensures eval the_interpretation t rho == eval the_interpretation s rho)
  = if apply_lemma_select_store_same t = Some s then
      lemma_apply_lemma_select_store_same_sound t rho
    else if apply_lemma_store_same_twice t = Some s then
      lemma_apply_lemma_store_same_twice_sound t rho
    else if apply_lemma_store_redundant t = Some s then
      lemma_apply_lemma_store_redundant_sound t rho
    else if apply_lemma_select_store_diff t = Some s then
      lemma_apply_lemma_select_store_diff_sound t rho
    else
      lemma_apply_lemma_store_commute_sound t rho
