(*
   Z3RegexBounds.fst

   Shared length-bound machinery used by both `Z3RegexInfo.fst`
   (the plain `[min_length, max_length]` interval tracked by
   `seq_util::rex::info`) and `Z3LenAbsTheory.fst` (the richer
   periodic `len_abs` refinement, `src/util/len_abs.h`): the
   possibly-infinite bound type `ebound`, its interval arithmetic
   (`eb_add`/`eb_max`/`eb_min`/`eb_scale`/`eb_le`), and the generic
   facts about `re_pow`'s length (`lemma_pow_min_length`,
   `lemma_pow_max_length`, `lemma_pow_nullable_intro`/`_forces`) that
   both files' `star`/`plus`/`loop` soundness proofs are built on.

   This file exists purely to break what would otherwise be a
   circular module dependency: `Z3RegexInfo.fst`'s `info` record
   gained a `len_abs` field (see its own header), so it now needs
   `Z3LenAbsTheory.fst`'s definitions, while `Z3LenAbsTheory.fst` in
   turn needs this bound machinery that used to live directly in
   `Z3RegexInfo.fst`. Factoring it out here lets both depend on it
   without depending on each other.
*)
module Z3RegexBounds

open Z3SeqTheory
open Z3RegexTheory
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

(* A word has length 0 iff it is the empty word. *)
let lemma_len_zero (#a:eqtype) (w:seq a) : Lemma (len w == 0 <==> w == empty) =
  match w with
  | [] -> ()
  | _ :: _ -> ()

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
