(*
   Z3RegexInfo.fst

   A formalization of `seq_util::rex::get_info`/`mk_info_rec`
   (src/ast/seq_decl_plugin.cpp, lines ~1690-2048) on top of
   Z3RegexTheory.fst's language semantics and Z3RegexExprTheory.fst's
   `to_lang` denotation. `compute_info` mirrors the C++ structural
   recursion over `App` nodes operator-by-operator, and
   `lemma_compute_info_sound` proves that its result is a sound
   summary of the actual denoted language, in the same sense the real
   `rex::info` is documented to be (over-approximation only: "a rule
   can cost precision, never soundness", util/len_abs.h).

   Scope and fidelity notes:

   - The `period`/`residues` semilinear length-set refinement
     (util/len_abs.h) is NOT modeled: `info` here only tracks
     `nullable`, `min_length`, and `max_length` (as a possibly-
     infinite `ebound`). This is a deliberate scope reduction -- the
     periodic abstraction is a separate, self-contained refinement
     layered on top of the same `[min_length, max_length]` interval,
     and formalizing it is future work. Every `min_length`/
     `max_length` computed here is a sound (if, in general, less
     tight than Z3's `len_abs`-based) bound on the same interval.
     `classical` is carried along for structural fidelity with the
     C++ `info` struct but no property is proved about it.

   - **`info::diff`'s `nullable` computation
     (seq_decl_plugin.cpp, `info::diff`) appears to be UNSOUND**, and
     `compute_info` below deliberately does NOT reproduce it as-is;
     see the long comment at `info_diff` for the full analysis and a
     concrete counterexample. A corresponding one-line fix has been
     applied to seq_decl_plugin.cpp (see the `diff` combinator in this
     file for the corrected formula, which is what is actually proved
     sound here).

   - `info.interpreted` (`rex::is_ground`) is modeled and proved
     sound by `lemma_compute_info_interpreted_sound`: whenever it is
     `true`, the expression denotes the same language under every
     `seq_lit` (Z3RegexExprTheory.fst) agreeing on which leaves are
     literal, i.e. the computed language really is model-independent.
     This directly captures the bug fixed by PR #11091/issue #11090:
     a symbolic `re.range` endpoint was unconditionally reported as
     `interpreted = true`. Reverting `compute_info`'s `Re_range` case
     to that unconditional `true` (instead of
     `is_ground_leaf sl lo && is_ground_leaf sl hi`) makes
     `lemma_compute_info_interpreted_sound` FAIL to verify (checked
     directly), confirming the formalization catches this bug class.
*)
module Z3RegexInfo

open Z3SeqTheory
open Z3RegexTheory
open Z3AstTheory
open Z3RegexExprTheory
module Classical = FStar.Classical

(* ----------------------------------------------------------------- *)
(* Auxiliary sequence facts not already in Z3RegexTheory               *)
(* ----------------------------------------------------------------- *)

(* `concat s t` is empty iff both `s` and `t` are: the key fact used
   throughout to reason about which repetitions of a loop/star/plus
   can possibly denote the empty word. *)
let rec lemma_concat_empty_iff (#a:eqtype) (s t:seq a)
  : Lemma (concat s t == empty <==> (s == empty /\ t == empty))
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_concat_empty_iff s' t

let rec lemma_len_concat (#a:eqtype) (s t:seq a)
  : Lemma (len (concat s t) == len s + len t)
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_len_concat s' t

let rec lemma_len_reverse (#a:eqtype) (s:seq a)
  : Lemma (len (reverse s) == len s)
  = match s with
    | [] -> ()
    | x :: s' -> lemma_len_reverse s'; lemma_len_concat (reverse s') (unit x)

(* `re_pow l n` for `n >= 1` denotes the empty word only if `l` does:
   the key fact used to show `plus`/`loop`'s `nullable = false` case
   is sound. *)
let lemma_pow_nullable_forces (#a:eqtype) (l:lang a) (n:nat{n >= 1})
  : Lemma (requires mem empty (re_pow l n)) (ensures mem empty l)
  = elim_concat l (re_pow l (n - 1)) empty (mem empty l) (fun w1 w2 ->
      lemma_concat_empty_iff w1 w2)

(* Conversely, if `l` contains the empty word, so does `re_pow l n`
   for every `n` (vacuously for `n = 0`): the key fact used to show
   `plus`/`loop`'s `nullable = true` case is sound. *)
let rec lemma_pow_nullable_intro (#a:eqtype) (l:lang a) (n:nat)
  : Lemma (requires mem empty l) (ensures mem empty (re_pow l n))
  = if n = 0 then ()
    else begin
      lemma_pow_nullable_intro l (n - 1);
      lemma_concat_empty_r (empty #a);
      intro_concat l (re_pow l (n - 1)) empty empty empty
    end

(* If every member of `l` has length `>= m`, then every member of
   `re_pow l n` has length `>= n * m`. *)
let rec lemma_pow_min_length (#a:eqtype) (l:lang a) (m:nat)
    (hmin: (w:seq a -> Lemma (requires mem w l) (ensures m <= len w)))
    (n:nat) (w:seq a)
  : Lemma (requires mem w (re_pow l n)) (ensures n * m <= len w)
  = if n = 0 then ()
    else
      elim_concat l (re_pow l (n - 1)) w (n * m <= len w) (fun w1 w2 ->
        hmin w1;
        lemma_pow_min_length l m hmin (n - 1) w2;
        lemma_len_concat w1 w2;
        FStar.Math.Lemmas.distributivity_add_left (n - 1) 1 m)

(* If every member of `l` has length `<= bnd`, then every member of
   `re_pow l n` has length `<= n * bnd`. *)
let rec lemma_pow_max_length (#a:eqtype) (l:lang a) (bnd:nat)
    (hmax: (w:seq a -> Lemma (requires mem w l) (ensures len w <= bnd)))
    (n:nat) (w:seq a)
  : Lemma (requires mem w (re_pow l n)) (ensures len w <= n * bnd)
  = if n = 0 then ()
    else
      elim_concat l (re_pow l (n - 1)) w (len w <= n * bnd) (fun w1 w2 ->
        hmax w1;
        lemma_pow_max_length l bnd hmax (n - 1) w2;
        lemma_len_concat w1 w2;
        FStar.Math.Lemmas.distributivity_add_left (n - 1) 1 bnd)

(* ----------------------------------------------------------------- *)
(* Possibly-infinite length bound                                      *)
(* ----------------------------------------------------------------- *)

type ebound =
  | Bound    : nat -> ebound
  | Infinite

let eb_le (n:nat) (b:ebound) : bool =
  match b with
  | Bound m -> n <= m
  | Infinite -> true

let eb_add (b1 b2:ebound) : ebound =
  match b1, b2 with
  | Bound m1, Bound m2 -> Bound (m1 + m2)
  | _, _ -> Infinite

let eb_max (b1 b2:ebound) : ebound =
  match b1, b2 with
  | Bound m1, Bound m2 -> Bound (if m1 >= m2 then m1 else m2)
  | _, _ -> Infinite

let eb_min (b1 b2:ebound) : ebound =
  match b1, b2 with
  | Bound m1, Bound m2 -> Bound (if m1 <= m2 then m1 else m2)
  | Bound m1, Infinite -> Bound m1
  | Infinite, Bound m2 -> Bound m2
  | Infinite, Infinite -> Infinite

let eb_scale (n:nat) (b:ebound) : ebound =
  match b with
  | Bound m -> Bound (n * m)
  | Infinite -> if n = 0 then Bound 0 else Infinite

(* ----------------------------------------------------------------- *)
(* Nullability (mirrors Z3's `lbool`)                                  *)
(* ----------------------------------------------------------------- *)

type lb =
  | LTrue
  | LFalse
  | LUndef

(* ----------------------------------------------------------------- *)
(* The info record (`seq_util::rex::info`, with `period`/`residues`    *)
(* out of scope, see the module header)                                *)
(* ----------------------------------------------------------------- *)

noeq type info = {
  nullable    : lb;
  min_length  : nat;
  max_length  : ebound;
  classical   : bool;
  (* Mirrors `seq_util::rex::info::interpreted` (exposed via
     `rex::is_ground`): true means the expression this `info`
     summarizes denotes a language that is completely determined --
     invariant across every interpretation/model of its (symbolic)
     leaves, because it in fact has none. See
     `lemma_compute_info_interpreted_sound` below for the formal
     contract, and the module header for PR #11091/issue #11090,
     where a symbolic `re.range` was incorrectly reported as
     `interpreted = true`. *)
  interpreted : bool;
}

(* "Soundness" of an `info` relative to a language `l`: exactly the
   contract `seq_util::rex::info` is documented to uphold (nullable
   correctly reports membership of the empty word when known, and
   [min_length, max_length] contains the length of every member). *)
let info_sound (#a:eqtype) (i:info) (l:lang a) : prop =
  (i.nullable == LTrue ==> mem empty l) /\
  (i.nullable == LFalse ==> ~(mem empty l)) /\
  (forall (w:seq a). mem w l ==> i.min_length <= len w /\ eb_le (len w) i.max_length)

(* ----------------------------------------------------------------- *)
(* Per-operator combinators (`seq_util::rex::info::*`)                 *)
(* ----------------------------------------------------------------- *)

let info_star (i1:info) : info =
  { nullable = LTrue; min_length = 0; max_length = Infinite; classical = i1.classical; interpreted = i1.interpreted }

let info_opt (i1:info) : info =
  { nullable = LTrue; min_length = 0; max_length = i1.max_length; classical = i1.classical; interpreted = i1.interpreted }

let info_plus (i1:info) : info =
  { nullable = i1.nullable; min_length = i1.min_length; max_length = Infinite; classical = i1.classical; interpreted = i1.interpreted }

let info_complement (i1:info) : info =
  let n = (match i1.nullable with LTrue -> LFalse | LFalse -> LTrue | LUndef -> LUndef) in
  let m = (match n with LFalse -> 1 | _ -> 0) in
  { nullable = n; min_length = m; max_length = Infinite; classical = false; interpreted = i1.interpreted }

let info_concat (i1 i2:info) : info =
  let n =
    if i1.nullable = LFalse || i2.nullable = LFalse then LFalse
    else if i1.nullable = LTrue && i2.nullable = LTrue then LTrue
    else LUndef
  in
  { nullable = n; min_length = i1.min_length + i2.min_length;
    max_length = eb_add i1.max_length i2.max_length; classical = i1.classical && i2.classical;
    interpreted = i1.interpreted && i2.interpreted }

let info_union (i1 i2:info) : info =
  let n =
    if i1.nullable = LTrue || i2.nullable = LTrue then LTrue
    else if i1.nullable = LFalse && i2.nullable = LFalse then LFalse
    else LUndef
  in
  { nullable = n; min_length = (if i1.min_length <= i2.min_length then i1.min_length else i2.min_length);
    max_length = eb_max i1.max_length i2.max_length; classical = i1.classical && i2.classical;
    interpreted = i1.interpreted && i2.interpreted }

let info_inter (i1 i2:info) : info =
  let n =
    if i1.nullable = LTrue && i2.nullable = LTrue then LTrue
    else if i1.nullable = LFalse || i2.nullable = LFalse then LFalse
    else LUndef
  in
  { nullable = n; min_length = (if i1.min_length >= i2.min_length then i1.min_length else i2.min_length);
    max_length = eb_min i1.max_length i2.max_length; classical = false;
    interpreted = i1.interpreted && i2.interpreted }

(*
  `info::diff` in seq_decl_plugin.cpp computes `nullable` as:

      (nullable == l_true && rhs.nullable == l_false) ? l_true
    : (nullable == l_false || rhs.nullable == l_false) ? l_false
    : l_undef

  This is UNSOUND at (nullable = l_undef, rhs.nullable = l_false):
  the formula declares the difference non-nullable, yet this does
  not follow. Counterexample: let `s` be a non-literal (symbolic)
  string of min_length 0 and unknown value, so `nullable(seq.to_re
  s) = l_undef` (seq_decl_plugin.cpp's `OP_SEQ_TO_RE` case: `is_value`
  is false, so nullable is `l_undef` whenever `min_length == 0`), and
  let `L2 = re.range('a','a')`, so `nullable(L2) = l_false`
  (OP_RE_RANGE is never nullable). If the model happens to assign `s`
  the empty string, then `L1 \ L2 = {epsilon} \ {"a"} = {epsilon}`,
  i.e. the difference *is* nullable here -- contradicting the
  `l_false` the formula reports. The bug is the redundant
  `rhs.nullable == l_false` disjunct: only `nullable == l_false`
  (lhs alone) soundly forces non-nullability of the difference,
  since if `epsilon` actually is in L1 and (by `rhs.nullable ==
  l_false`) genuinely not in L2, it survives into `L1 \ L2`.

  `compute_info`/`info_diff` below implement the corrected formula
  (dropping that disjunct), which is what is proved sound by
  `lemma_compute_info_sound`. The same one-line fix has been applied
  directly to `seq_util::rex::info::diff` in seq_decl_plugin.cpp.
*)
let info_diff (i1 i2:info) : info =
  let n =
    if i1.nullable = LTrue && i2.nullable = LFalse then LTrue
    else if i1.nullable = LFalse then LFalse
    else LUndef
  in
  { nullable = n; min_length = 0; max_length = i1.max_length; classical = false;
    interpreted = i1.interpreted && i2.interpreted }

let info_xor (i1 i2:info) : info =
  let n =
    match i1.nullable, i2.nullable with
    | LTrue, LTrue | LFalse, LFalse -> LFalse
    | LTrue, LFalse | LFalse, LTrue -> LTrue
    | _, _ -> LUndef
  in
  { nullable = n; min_length = 0; max_length = Infinite; classical = false;
    interpreted = i1.interpreted && i2.interpreted }

let info_loop (i1:info) (lo:nat) (hi:ebound) : info =
  let n = if i1.nullable = LTrue || lo = 0 then LTrue else i1.nullable in
  { nullable = n; min_length = lo * i1.min_length;
    max_length = (match hi with Bound h -> eb_scale h i1.max_length | Infinite -> Infinite);
    classical = i1.classical; interpreted = i1.interpreted }

(* ----------------------------------------------------------------- *)
(* compute_info: structural recursion over `App` nodes, mirroring      *)
(* `mk_info_rec`'s dispatch on `decl_kind` exactly, and `to_lang`'s     *)
(* own recursive shape (Z3RegexExprTheory.fst) so that the two can be  *)
(* related by a single structural induction below.                     *)
(* ----------------------------------------------------------------- *)

let rec compute_info (#a:eqtype) (sl:seq_lit a) (e:expr) : Tot (option info) (decreases e) =
  match e with
  | Var _ _ | Quantifier _ _ _ -> None
  | App f args ->
    if is_re_op f Re_empty_set then (match args with | [] -> Some ({ nullable = LFalse; min_length = 0; max_length = Bound 0; classical = false; interpreted = true }) | _ -> None)
    else if is_re_op f Re_full_seq_set then (match args with | [] -> Some ({ nullable = LTrue; min_length = 0; max_length = Infinite; classical = true; interpreted = true }) | _ -> None)
    else if is_re_op f Re_full_char_set then (match args with | [] -> Some ({ nullable = LFalse; min_length = 1; max_length = Bound 1; classical = false; interpreted = true }) | _ -> None)
    else if is_re_op f Re_of_pred then None
    else if is_re_op f Re_range then
      (match args with
       | [lo; hi] ->
         let wl = eval_leaf sl lo in
         let wh = eval_leaf sl hi in
         let cl = (match wl, wh with | [l], [h] -> sl.char_le l h | _, _ -> false) in
         (* `interpreted` is sound only when BOTH endpoints are actually
            ground/literal: this is the one-line fix for PR #11091 /
            issue #11090, where the real C++ code hardcoded `true`
            here regardless of whether `lo`/`hi` were symbolic. *)
         Some ({ nullable = LFalse; min_length = 1; max_length = Bound 1; classical = cl;
                 interpreted = is_ground_leaf sl lo && is_ground_leaf sl hi })
       | _ -> None)
    else if is_re_op f Re_seq_to_re then
      (match args with
       | [s] ->
         let w = eval_leaf sl s in
         let n = len w in
         Some ({ nullable = (if n = 0 then LTrue else LFalse); min_length = n; max_length = Bound n; classical = true;
                 interpreted = is_ground_leaf sl s })
       | _ -> None)
    else if is_re_op f Re_plus then
      (match args with
       | [r] -> (match compute_info sl r with Some i -> Some (info_plus i) | None -> None)
       | _ -> None)
    else if is_re_op f Re_star then
      (match args with
       | [r] -> (match compute_info sl r with Some i -> Some (info_star i) | None -> None)
       | _ -> None)
    else if is_re_op f Re_option then
      (match args with
       | [r] -> (match compute_info sl r with Some i -> Some (info_opt i) | None -> None)
       | _ -> None)
    else if is_re_op f Re_complement then
      (match args with
       | [r] -> (match compute_info sl r with Some i -> Some (info_complement i) | None -> None)
       | _ -> None)
    else if is_re_op f Re_reverse then
      (match args with
       | [r] -> compute_info sl r
       | _ -> None)
    else if is_re_op f Re_concat then
      (match args with
       | [r1; r2] ->
         (match compute_info sl r1, compute_info sl r2 with
          | Some i1, Some i2 -> Some (info_concat i1 i2)
          | _, _ -> None)
       | _ -> None)
    else if is_re_op f Re_union then
      (match args with
       | [r1; r2] ->
         (match compute_info sl r1, compute_info sl r2 with
          | Some i1, Some i2 -> Some (info_union i1 i2)
          | _, _ -> None)
       | _ -> None)
    else if is_re_op f Re_intersect then
      (match args with
       | [r1; r2] ->
         (match compute_info sl r1, compute_info sl r2 with
          | Some i1, Some i2 -> Some (info_inter i1 i2)
          | _, _ -> None)
       | _ -> None)
    else if is_re_op f Re_diff then
      (match args with
       | [r1; r2] ->
         (match compute_info sl r1, compute_info sl r2 with
          | Some i1, Some i2 -> Some (info_diff i1 i2)
          | _, _ -> None)
       | _ -> None)
    else if is_re_op f Re_xor then
      (match args with
       | [r1; r2] ->
         (match compute_info sl r1, compute_info sl r2 with
          | Some i1, Some i2 -> Some (info_xor i1 i2)
          | _, _ -> None)
       | _ -> None)
    else if is_re_op f Re_loop then
      (match args, f.int_params with
       | [r], [lo] ->
         if lo >= 0 then (match compute_info sl r with Some i -> Some (info_loop i lo Infinite) | None -> None)
         else None
       | [r], [lo; hi] ->
         if lo >= 0 && hi >= lo then (match compute_info sl r with Some i -> Some (info_loop i lo (Bound hi)) | None -> None)
         else None
       | _ -> None)
    else None

(* ----------------------------------------------------------------- *)
(* Per-operator soundness: `info_X i1 ... = info_sound (op l1 ...)`    *)
(* given `i1`/`l1`/... are already known to be sound of one another.  *)
(* These mirror compute_info's/to_lang's cases one-for-one and are    *)
(* assembled into the main structural induction below.                *)
(* ----------------------------------------------------------------- *)

let lemma_sound_star (#a:eqtype) (l:lang a) (i:info)
  : Lemma (requires info_sound i l) (ensures info_sound (info_star i) (re_star l))
  = lemma_star_nil l

let lemma_sound_opt (#a:eqtype) (l:lang a) (i:info)
  : Lemma (requires info_sound i l) (ensures info_sound (info_opt i) (re_opt l))
  = ()

(* Membership of the empty word in `re_plus l`, from membership in
   `l` (take the single-repetition witness). *)
let lemma_plus_nullable_intro (#a:eqtype) (l:lang a)
  : Lemma (requires mem empty l) (ensures mem empty (re_plus l))
  = lemma_concat_empty_r (empty #a);
    intro_concat l (re_pow l 0) empty empty empty;
    Classical.exists_intro (fun (n:nat{n >= 1}) -> mem empty (re_pow l n)) 1

let lemma_plus_not_nullable (#a:eqtype) (l:lang a)
  : Lemma (requires ~(mem empty l)) (ensures ~(mem empty (re_plus l)))
  = let aux (_:squash (mem empty (re_plus l))) : Lemma False =
      Classical.exists_elim False #(n:nat{n >= 1}) #(fun n -> mem empty (re_pow l n)) ()
        (fun n -> lemma_pow_nullable_forces l n)
    in
    Classical.impl_intro aux

let lemma_sound_plus (#a:eqtype) (l:lang a) (i:info)
  : Lemma (requires info_sound i l) (ensures info_sound (info_plus i) (re_plus l))
  = (if i.nullable = LTrue then lemma_plus_nullable_intro l);
    (if i.nullable = LFalse then lemma_plus_not_nullable l);
    let bound (w:seq a) : Lemma (requires mem w (re_plus l)) (ensures i.min_length <= len w) =
      Classical.exists_elim (i.min_length <= len w) #(n:nat{n >= 1}) #(fun n -> mem w (re_pow l n)) ()
        (fun n ->
          let hmin (w':seq a) : Lemma (requires mem w' l) (ensures i.min_length <= len w') = () in
          lemma_pow_min_length l i.min_length hmin n w;
          FStar.Math.Lemmas.lemma_mult_le_right i.min_length 1 n)
    in
    Classical.forall_intro (Classical.move_requires bound)

let lemma_sound_complement (#a:eqtype) (l:lang a) (i:info)
  : Lemma (requires info_sound i l) (ensures info_sound (info_complement i) (re_compl l))
  = ()

let lemma_sound_concat (#a:eqtype) (l1 l2:lang a) (i1 i2:info)
  : Lemma (requires info_sound i1 l1 /\ info_sound i2 l2)
          (ensures info_sound (info_concat i1 i2) (re_concat l1 l2))
  = let bound (w:seq a) : Lemma (requires mem w (re_concat l1 l2))
                                 (ensures i1.min_length + i2.min_length <= len w /\ eb_le (len w) (eb_add i1.max_length i2.max_length)) =
      elim_concat l1 l2 w (i1.min_length + i2.min_length <= len w /\ eb_le (len w) (eb_add i1.max_length i2.max_length)) (fun w1 w2 ->
        lemma_len_concat w1 w2)
    in
    Classical.forall_intro (Classical.move_requires bound);
    (if i1.nullable = LTrue && i2.nullable = LTrue then begin
       lemma_concat_empty_r (empty #a);
       intro_concat l1 l2 empty empty empty
     end);
    (if i1.nullable = LFalse || i2.nullable = LFalse then begin
       let aux (_:squash (mem empty (re_concat l1 l2))) : Lemma False =
         elim_concat l1 l2 empty False (fun w1 w2 -> lemma_concat_empty_iff w1 w2)
       in
       Classical.impl_intro aux
     end)

let lemma_sound_union (#a:eqtype) (l1 l2:lang a) (i1 i2:info)
  : Lemma (requires info_sound i1 l1 /\ info_sound i2 l2)
          (ensures info_sound (info_union i1 i2) (re_union l1 l2))
  = ()

let lemma_sound_inter (#a:eqtype) (l1 l2:lang a) (i1 i2:info)
  : Lemma (requires info_sound i1 l1 /\ info_sound i2 l2)
          (ensures info_sound (info_inter i1 i2) (re_inter l1 l2))
  = ()

let lemma_sound_diff (#a:eqtype) (l1 l2:lang a) (i1 i2:info)
  : Lemma (requires info_sound i1 l1 /\ info_sound i2 l2)
          (ensures info_sound (info_diff i1 i2) (re_diff l1 l2))
  = ()

let lemma_sound_xor (#a:eqtype) (l1 l2:lang a) (i1 i2:info)
  : Lemma (requires info_sound i1 l1 /\ info_sound i2 l2)
          (ensures info_sound (info_xor i1 i2) (re_xor l1 l2))
  = ()

let lemma_sound_reverse (#a:eqtype) (l:lang a) (i:info)
  : Lemma (requires info_sound i l) (ensures info_sound i (re_reverse l))
  = let bound (w:seq a) : Lemma (requires mem w (re_reverse l)) (ensures i.min_length <= len w /\ eb_le (len w) i.max_length) =
      lemma_len_reverse w
    in
    Classical.forall_intro (Classical.move_requires bound)

let lemma_sound_loop_bounded (#a:eqtype) (l:lang a) (i:info) (lo hi:nat{lo <= hi})
  : Lemma (requires info_sound i l) (ensures info_sound (info_loop i lo (Bound hi)) (re_loop l lo hi))
  = (if i.nullable = LTrue || lo = 0 then begin
       if lo = 0 then Classical.exists_intro (fun (n:nat{lo <= n /\ n <= hi}) -> mem empty (re_pow l n)) 0
       else begin
         lemma_pow_nullable_intro l lo;
         Classical.exists_intro (fun (n:nat{lo <= n /\ n <= hi}) -> mem empty (re_pow l n)) lo
       end
     end);
    (if i.nullable = LFalse && lo > 0 then begin
       let aux (_:squash (mem empty (re_loop l lo hi))) : Lemma False =
         Classical.exists_elim False #(n:nat{lo <= n /\ n <= hi}) #(fun n -> mem empty (re_pow l n)) ()
           (fun n -> lemma_pow_nullable_forces l n)
       in
       Classical.impl_intro aux
     end);
    let bound (w:seq a) : Lemma (requires mem w (re_loop l lo hi))
                                 (ensures lo * i.min_length <= len w /\ eb_le (len w) (eb_scale hi i.max_length)) =
      Classical.exists_elim (lo * i.min_length <= len w /\ eb_le (len w) (eb_scale hi i.max_length))
        #(n:nat{lo <= n /\ n <= hi}) #(fun n -> mem w (re_pow l n)) ()
        (fun n ->
          let hmin (w':seq a) : Lemma (requires mem w' l) (ensures i.min_length <= len w') = () in
          lemma_pow_min_length l i.min_length hmin n w;
          FStar.Math.Lemmas.lemma_mult_le_right i.min_length lo n;
          (match i.max_length with
           | Bound m ->
             let hmax (w':seq a) : Lemma (requires mem w' l) (ensures len w' <= m) = () in
             lemma_pow_max_length l m hmax n w;
             FStar.Math.Lemmas.lemma_mult_le_right m n hi
           | Infinite -> ()))
    in
    Classical.forall_intro (Classical.move_requires bound)

let lemma_sound_loop_lo (#a:eqtype) (l:lang a) (i:info) (lo:nat)
  : Lemma (requires info_sound i l) (ensures info_sound (info_loop i lo Infinite) (re_loop_lo l lo))
  = (if i.nullable = LTrue || lo = 0 then begin
     (if lo > 0 then lemma_pow_nullable_intro l lo);
       lemma_star_nil l;
       lemma_concat_empty_r (empty #a);
       intro_concat (re_pow l lo) (re_star l) empty empty empty
     end);
    (if i.nullable = LFalse && lo > 0 then begin
       let aux (_:squash (mem empty (re_loop_lo l lo))) : Lemma False =
         elim_concat (re_pow l lo) (re_star l) empty False (fun w1 w2 ->
           lemma_concat_empty_iff w1 w2;
           lemma_pow_nullable_forces l lo)
       in
       Classical.impl_intro aux
     end);
    let bound (w:seq a) : Lemma (requires mem w (re_loop_lo l lo)) (ensures lo * i.min_length <= len w) =
      elim_concat (re_pow l lo) (re_star l) w (lo * i.min_length <= len w) (fun w1 w2 ->
        let hmin (w':seq a) : Lemma (requires mem w' l) (ensures i.min_length <= len w') = () in
        lemma_pow_min_length l i.min_length hmin lo w1;
        lemma_len_concat w1 w2)
    in
    Classical.forall_intro (Classical.move_requires bound)

(* ----------------------------------------------------------------- *)
(* Main theorem: `compute_info` is a sound summary of `to_lang`        *)
(* ----------------------------------------------------------------- *)

(* The relation that `lemma_compute_info_sound` establishes between
   `compute_info`'s and `to_lang`'s results on the same expression:
   either both recognize `e` (as a regex expression) and the computed
   `info` soundly summarizes the computed language, or neither does. *)
let info_matches (#a:eqtype) (oi:option info) (ol:option (lang a)) : prop =
  match oi, ol with
  | Some i, Some l -> info_sound i l
  | None, None -> True
  | _, _ -> False

(* `compute_info sl e` is always a sound summary of `to_lang sl e`,
   for every expression `e`: the formal counterpart of `get_info`'s
   documented contract. The induction mirrors `compute_info`'s/
   `to_lang`'s own dispatch exactly, case for case, invoking the
   corresponding `lemma_sound_X` on the recursively-obtained
   induction hypotheses. *)
let rec lemma_compute_info_sound (#a:eqtype) (sl:seq_lit a) (e:expr)
  : Lemma (ensures info_matches #a (compute_info sl e) (to_lang sl e))
          (decreases e)
  = match e with
    | Var _ _ | Quantifier _ _ _ -> ()
    | App f args ->
      if is_re_op f Re_empty_set then ()
      else if is_re_op f Re_full_seq_set then ()
      else if is_re_op f Re_full_char_set then ()
      else if is_re_op f Re_of_pred then ()
      else if is_re_op f Re_range then ()
      else if is_re_op f Re_seq_to_re then ()
      else if is_re_op f Re_plus then
        (match args with
         | [r] ->
           lemma_compute_info_sound sl r;
           (match compute_info sl r, to_lang sl r with
            | Some i, Some l -> lemma_sound_plus l i
            | _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_star then
        (match args with
         | [r] ->
           lemma_compute_info_sound sl r;
           (match compute_info sl r, to_lang sl r with
            | Some i, Some l -> lemma_sound_star l i
            | _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_option then
        (match args with
         | [r] ->
           lemma_compute_info_sound sl r;
           (match compute_info sl r, to_lang sl r with
            | Some i, Some l -> lemma_sound_opt l i
            | _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_complement then
        (match args with
         | [r] ->
           lemma_compute_info_sound sl r;
           (match compute_info sl r, to_lang sl r with
            | Some i, Some l -> lemma_sound_complement l i
            | _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_reverse then
        (match args with
         | [r] ->
           lemma_compute_info_sound sl r;
           (match compute_info sl r, to_lang sl r with
            | Some i, Some l -> lemma_sound_reverse l i
            | _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_concat then
        (match args with
         | [r1; r2] ->
           lemma_compute_info_sound sl r1;
           lemma_compute_info_sound sl r2;
           (match compute_info sl r1, to_lang sl r1, compute_info sl r2, to_lang sl r2 with
            | Some i1, Some l1, Some i2, Some l2 -> lemma_sound_concat l1 l2 i1 i2
            | _, _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_union then
        (match args with
         | [r1; r2] ->
           lemma_compute_info_sound sl r1;
           lemma_compute_info_sound sl r2;
           (match compute_info sl r1, to_lang sl r1, compute_info sl r2, to_lang sl r2 with
            | Some i1, Some l1, Some i2, Some l2 -> lemma_sound_union l1 l2 i1 i2
            | _, _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_intersect then
        (match args with
         | [r1; r2] ->
           lemma_compute_info_sound sl r1;
           lemma_compute_info_sound sl r2;
           (match compute_info sl r1, to_lang sl r1, compute_info sl r2, to_lang sl r2 with
            | Some i1, Some l1, Some i2, Some l2 -> lemma_sound_inter l1 l2 i1 i2
            | _, _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_diff then
        (match args with
         | [r1; r2] ->
           lemma_compute_info_sound sl r1;
           lemma_compute_info_sound sl r2;
           (match compute_info sl r1, to_lang sl r1, compute_info sl r2, to_lang sl r2 with
            | Some i1, Some l1, Some i2, Some l2 -> lemma_sound_diff l1 l2 i1 i2
            | _, _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_xor then
        (match args with
         | [r1; r2] ->
           lemma_compute_info_sound sl r1;
           lemma_compute_info_sound sl r2;
           (match compute_info sl r1, to_lang sl r1, compute_info sl r2, to_lang sl r2 with
            | Some i1, Some l1, Some i2, Some l2 -> lemma_sound_xor l1 l2 i1 i2
            | _, _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_loop then
        (match args, f.int_params with
         | [r], [lo] ->
           if lo >= 0 then begin
             lemma_compute_info_sound sl r;
             (match compute_info sl r, to_lang sl r with
              | Some i, Some l -> lemma_sound_loop_lo l i lo
              | _, _ -> ())
           end
         | [r], [lo; hi] ->
           if lo >= 0 && hi >= lo then begin
             lemma_compute_info_sound sl r;
             (match compute_info sl r, to_lang sl r with
              | Some i, Some l -> lemma_sound_loop_bounded l i lo hi
              | _, _ -> ())
           end
         | _, _ -> ())
      else ()

(* ----------------------------------------------------------------- *)
(* Congruence of Z3RegexTheory's combinators under `equiv`             *)
(* -- needed below to show that `interpreted = true` really does      *)
(* mean "denotes the same language regardless of which `seq_lit` is   *)
(* used for the (now absent) symbolic leaves".                        *)
(* ----------------------------------------------------------------- *)

let lemma_union_cong (#a:eqtype) (l1 l1' l2 l2':lang a)
  : Lemma (requires equiv l1 l1' /\ equiv l2 l2') (ensures equiv (re_union l1 l2) (re_union l1' l2'))
  = ()

let lemma_inter_cong (#a:eqtype) (l1 l1' l2 l2':lang a)
  : Lemma (requires equiv l1 l1' /\ equiv l2 l2') (ensures equiv (re_inter l1 l2) (re_inter l1' l2'))
  = ()

let lemma_compl_cong (#a:eqtype) (l l':lang a)
  : Lemma (requires equiv l l') (ensures equiv (re_compl l) (re_compl l'))
  = ()

let lemma_diff_cong (#a:eqtype) (l1 l1' l2 l2':lang a)
  : Lemma (requires equiv l1 l1' /\ equiv l2 l2') (ensures equiv (re_diff l1 l2) (re_diff l1' l2'))
  = lemma_compl_cong l2 l2'

let lemma_xor_cong (#a:eqtype) (l1 l1' l2 l2':lang a)
  : Lemma (requires equiv l1 l1' /\ equiv l2 l2') (ensures equiv (re_xor l1 l2) (re_xor l1' l2'))
  = ()

let lemma_concat_cong (#a:eqtype) (l1 l1' l2 l2':lang a)
  : Lemma (requires equiv l1 l1' /\ equiv l2 l2') (ensures equiv (re_concat l1 l2) (re_concat l1' l2'))
  = let fwd (w:seq a) : Lemma (requires mem w (re_concat l1 l2)) (ensures mem w (re_concat l1' l2')) =
      Classical.exists_elim (mem w (re_concat l1' l2')) #(seq a & seq a)
        #(fun p -> w == concat (fst p) (snd p) /\ mem (fst p) l1 /\ mem (snd p) l2) ()
        (fun p -> Classical.exists_intro
           (fun (p':(seq a & seq a)) -> w == concat (fst p') (snd p') /\ mem (fst p') l1' /\ mem (snd p') l2') p)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_concat l1' l2')) (ensures mem w (re_concat l1 l2)) =
      Classical.exists_elim (mem w (re_concat l1 l2)) #(seq a & seq a)
        #(fun p -> w == concat (fst p) (snd p) /\ mem (fst p) l1' /\ mem (snd p) l2') ()
        (fun p -> Classical.exists_intro
           (fun (p':(seq a & seq a)) -> w == concat (fst p') (snd p') /\ mem (fst p') l1 /\ mem (snd p') l2) p)
    in
    Classical.forall_intro (Classical.move_requires fwd);
    Classical.forall_intro (Classical.move_requires bwd)

let rec lemma_pow_cong (#a:eqtype) (l l':lang a) (n:nat)
  : Lemma (requires equiv l l') (ensures equiv (re_pow l n) (re_pow l' n))
  = if n = 0 then ()
    else begin
      lemma_pow_cong l l' (n - 1);
      lemma_concat_cong l l' (re_pow l (n - 1)) (re_pow l' (n - 1))
    end

let lemma_star_cong (#a:eqtype) (l l':lang a)
  : Lemma (requires equiv l l') (ensures equiv (re_star l) (re_star l'))
  = let fwd (w:seq a) : Lemma (requires mem w (re_star l)) (ensures mem w (re_star l')) =
      Classical.exists_elim (mem w (re_star l')) #nat #(fun n -> mem w (re_pow l n)) ()
        (fun n -> lemma_pow_cong l l' n; Classical.exists_intro (fun n -> mem w (re_pow l' n)) n)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_star l')) (ensures mem w (re_star l)) =
      Classical.exists_elim (mem w (re_star l)) #nat #(fun n -> mem w (re_pow l' n)) ()
        (fun n -> lemma_pow_cong l l' n; Classical.exists_intro (fun n -> mem w (re_pow l n)) n)
    in
    Classical.forall_intro (Classical.move_requires fwd);
    Classical.forall_intro (Classical.move_requires bwd)

let lemma_plus_cong (#a:eqtype) (l l':lang a)
  : Lemma (requires equiv l l') (ensures equiv (re_plus l) (re_plus l'))
  = let fwd (w:seq a) : Lemma (requires mem w (re_plus l)) (ensures mem w (re_plus l')) =
      Classical.exists_elim (mem w (re_plus l')) #(n:nat{n >= 1}) #(fun n -> mem w (re_pow l n)) ()
        (fun n -> lemma_pow_cong l l' n; Classical.exists_intro (fun (n:nat{n >= 1}) -> mem w (re_pow l' n)) n)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_plus l')) (ensures mem w (re_plus l)) =
      Classical.exists_elim (mem w (re_plus l)) #(n:nat{n >= 1}) #(fun n -> mem w (re_pow l' n)) ()
        (fun n -> lemma_pow_cong l l' n; Classical.exists_intro (fun (n:nat{n >= 1}) -> mem w (re_pow l n)) n)
    in
    Classical.forall_intro (Classical.move_requires fwd);
    Classical.forall_intro (Classical.move_requires bwd)

let lemma_opt_cong (#a:eqtype) (l l':lang a)
  : Lemma (requires equiv l l') (ensures equiv (re_opt l) (re_opt l'))
  = lemma_union_cong (re_to_re empty) (re_to_re empty) l l'

let lemma_reverse_cong (#a:eqtype) (l l':lang a)
  : Lemma (requires equiv l l') (ensures equiv (re_reverse l) (re_reverse l'))
  = ()

let lemma_loop_cong (#a:eqtype) (l l':lang a) (lo hi:nat)
  : Lemma (requires equiv l l') (ensures equiv (re_loop l lo hi) (re_loop l' lo hi))
  = let fwd (w:seq a) : Lemma (requires mem w (re_loop l lo hi)) (ensures mem w (re_loop l' lo hi)) =
      Classical.exists_elim (mem w (re_loop l' lo hi)) #(n:nat{lo <= n /\ n <= hi}) #(fun n -> mem w (re_pow l n)) ()
        (fun n -> lemma_pow_cong l l' n; Classical.exists_intro (fun (n:nat{lo <= n /\ n <= hi}) -> mem w (re_pow l' n)) n)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_loop l' lo hi)) (ensures mem w (re_loop l lo hi)) =
      Classical.exists_elim (mem w (re_loop l lo hi)) #(n:nat{lo <= n /\ n <= hi}) #(fun n -> mem w (re_pow l' n)) ()
        (fun n -> lemma_pow_cong l l' n; Classical.exists_intro (fun (n:nat{lo <= n /\ n <= hi}) -> mem w (re_pow l n)) n)
    in
    Classical.forall_intro (Classical.move_requires fwd);
    Classical.forall_intro (Classical.move_requires bwd)

let lemma_loop_lo_cong (#a:eqtype) (l l':lang a) (lo:nat)
  : Lemma (requires equiv l l') (ensures equiv (re_loop_lo l lo) (re_loop_lo l' lo))
  = lemma_pow_cong l l' lo;
    lemma_star_cong l l';
    lemma_concat_cong (re_pow l lo) (re_pow l' lo) (re_star l) (re_star l')

(* ----------------------------------------------------------------- *)
(* `interpreted` soundness: ground (`interpreted = true`) expressions  *)
(* denote the same language under every `seq_lit` agreeing on which   *)
(* leaves are literal -- the formal counterpart of `rex::is_ground`,  *)
(* and precisely what PR #11091/issue #11090 found violated by the    *)
(* old (unfixed) `OP_RE_RANGE` case, which reported `interpreted =    *)
(* true` for a symbolic range unconditionally.                        *)
(* ----------------------------------------------------------------- *)

(* Two `seq_lit`s that cannot be told apart by `compute_info`/
   `to_lang`'s leaf-recognition logic: same literal/symbolic
   classification of every expression, and the same element order
   (so `re.range`'s denotation cannot differ for reasons other than a
   genuinely different model of a symbolic leaf). *)
let compatible (#a:eqtype) (sl sl':seq_lit a) : prop =
  same_classification sl sl' /\ sl.char_le == sl'.char_le

let same_interpreted (oi oi':option info) : prop =
  match oi, oi' with
  | Some i, Some i' -> i.interpreted == i'.interpreted
  | None, None -> True
  | _, _ -> False

let langs_equiv_opt (#a:eqtype) (ol ol':option (lang a)) : prop =
  match ol, ol' with
  | Some l, Some l' -> equiv l l'
  | None, None -> True
  | _, _ -> False

let is_interpreted (oi:option info) : bool =
  match oi with
  | Some i -> i.interpreted
  | None -> false

(* The main groundness theorem: for `compatible` `sl`/`sl'`,
   `compute_info`'s `interpreted` flag agrees between them (it only
   ever depends on `classify`), and whenever that flag is `true`,
   `to_lang sl e` and `to_lang sl' e` denote the same (equivalent)
   language -- i.e. `interpreted` really does certify
   model-independence, exactly the property `rex::is_ground` is
   relied on for in `seq_rewriter.cpp`'s ground-regex bisimulation
   shortcut (`mk_eq_core`). The induction mirrors `compute_info`'s/
   `to_lang`'s dispatch exactly, as in `lemma_compute_info_sound`. *)
let rec lemma_compute_info_interpreted_sound (#a:eqtype) (sl sl':seq_lit a) (e:expr)
  : Lemma (requires compatible sl sl')
          (ensures same_interpreted (compute_info sl e) (compute_info sl' e) /\
                   (is_interpreted (compute_info sl e) ==> langs_equiv_opt #a (to_lang sl e) (to_lang sl' e)))
          (decreases e)
  = match e with
    | Var _ _ | Quantifier _ _ _ -> ()
    | App f args ->
      if is_re_op f Re_empty_set then ()
      else if is_re_op f Re_full_seq_set then ()
      else if is_re_op f Re_full_char_set then ()
      else if is_re_op f Re_of_pred then ()
      else if is_re_op f Re_range then
        (match args with
         | [lo; hi] ->
           if is_ground_leaf sl lo && is_ground_leaf sl hi then begin
             lemma_eval_leaf_ground sl sl' lo;
             lemma_eval_leaf_ground sl sl' hi
           end
         | _ -> ())
      else if is_re_op f Re_seq_to_re then
        (match args with
         | [s] -> if is_ground_leaf sl s then lemma_eval_leaf_ground sl sl' s
         | _ -> ())
      else if is_re_op f Re_plus then
        (match args with
         | [r] ->
           lemma_compute_info_interpreted_sound sl sl' r;
           (match compute_info sl r, to_lang sl r, to_lang sl' r with
            | Some i, Some l, Some l' -> if i.interpreted then lemma_plus_cong l l'
            | _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_star then
        (match args with
         | [r] ->
           lemma_compute_info_interpreted_sound sl sl' r;
           (match compute_info sl r, to_lang sl r, to_lang sl' r with
            | Some i, Some l, Some l' -> if i.interpreted then lemma_star_cong l l'
            | _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_option then
        (match args with
         | [r] ->
           lemma_compute_info_interpreted_sound sl sl' r;
           (match compute_info sl r, to_lang sl r, to_lang sl' r with
            | Some i, Some l, Some l' -> if i.interpreted then lemma_opt_cong l l'
            | _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_complement then
        (match args with
         | [r] ->
           lemma_compute_info_interpreted_sound sl sl' r;
           (match compute_info sl r, to_lang sl r, to_lang sl' r with
            | Some i, Some l, Some l' -> if i.interpreted then lemma_compl_cong l l'
            | _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_reverse then
        (match args with
         | [r] ->
           lemma_compute_info_interpreted_sound sl sl' r;
           (match compute_info sl r, to_lang sl r, to_lang sl' r with
            | Some i, Some l, Some l' -> if i.interpreted then lemma_reverse_cong l l'
            | _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_concat then
        (match args with
         | [r1; r2] ->
           lemma_compute_info_interpreted_sound sl sl' r1;
           lemma_compute_info_interpreted_sound sl sl' r2;
           (match compute_info sl r1, compute_info sl r2, to_lang sl r1, to_lang sl' r1, to_lang sl r2, to_lang sl' r2 with
            | Some i1, Some i2, Some l1, Some l1', Some l2, Some l2' ->
              if i1.interpreted && i2.interpreted then lemma_concat_cong l1 l1' l2 l2'
            | _, _, _, _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_union then
        (match args with
         | [r1; r2] ->
           lemma_compute_info_interpreted_sound sl sl' r1;
           lemma_compute_info_interpreted_sound sl sl' r2;
           (match compute_info sl r1, compute_info sl r2, to_lang sl r1, to_lang sl' r1, to_lang sl r2, to_lang sl' r2 with
            | Some i1, Some i2, Some l1, Some l1', Some l2, Some l2' ->
              if i1.interpreted && i2.interpreted then lemma_union_cong l1 l1' l2 l2'
            | _, _, _, _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_intersect then
        (match args with
         | [r1; r2] ->
           lemma_compute_info_interpreted_sound sl sl' r1;
           lemma_compute_info_interpreted_sound sl sl' r2;
           (match compute_info sl r1, compute_info sl r2, to_lang sl r1, to_lang sl' r1, to_lang sl r2, to_lang sl' r2 with
            | Some i1, Some i2, Some l1, Some l1', Some l2, Some l2' ->
              if i1.interpreted && i2.interpreted then lemma_inter_cong l1 l1' l2 l2'
            | _, _, _, _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_diff then
        (match args with
         | [r1; r2] ->
           lemma_compute_info_interpreted_sound sl sl' r1;
           lemma_compute_info_interpreted_sound sl sl' r2;
           (match compute_info sl r1, compute_info sl r2, to_lang sl r1, to_lang sl' r1, to_lang sl r2, to_lang sl' r2 with
            | Some i1, Some i2, Some l1, Some l1', Some l2, Some l2' ->
              if i1.interpreted && i2.interpreted then lemma_diff_cong l1 l1' l2 l2'
            | _, _, _, _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_xor then
        (match args with
         | [r1; r2] ->
           lemma_compute_info_interpreted_sound sl sl' r1;
           lemma_compute_info_interpreted_sound sl sl' r2;
           (match compute_info sl r1, compute_info sl r2, to_lang sl r1, to_lang sl' r1, to_lang sl r2, to_lang sl' r2 with
            | Some i1, Some i2, Some l1, Some l1', Some l2, Some l2' ->
              if i1.interpreted && i2.interpreted then lemma_xor_cong l1 l1' l2 l2'
            | _, _, _, _, _, _ -> ())
         | _ -> ())
      else if is_re_op f Re_loop then
        (match args, f.int_params with
         | [r], [lo] ->
           if lo >= 0 then begin
             lemma_compute_info_interpreted_sound sl sl' r;
             (match compute_info sl r, to_lang sl r, to_lang sl' r with
              | Some i, Some l, Some l' -> if i.interpreted then lemma_loop_lo_cong l l' lo
              | _, _, _ -> ())
           end
         | [r], [lo; hi] ->
           if lo >= 0 && hi >= lo then begin
             lemma_compute_info_interpreted_sound sl sl' r;
             (match compute_info sl r, to_lang sl r, to_lang sl' r with
              | Some i, Some l, Some l' -> if i.interpreted then lemma_loop_cong l l' lo hi
              | _, _, _ -> ())
           end
         | _, _ -> ())
      else ()

