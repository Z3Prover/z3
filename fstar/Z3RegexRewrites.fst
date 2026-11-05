(*
   Z3RegexRewrites.fst

   Semantic-preservation (language-equivalence) proofs for the
   `mk_re_*` regex-rewrite functions dispatched from
   `seq_rewriter::mk_app_core` (src/ast/rewriter/seq_rewriter.cpp:154-369,
   the `OP_RE_*` cases). Each theorem below states, at the `lang a`
   level of Z3RegexTheory.fst, that one syntactic rewrite rule from the
   named C++ function is sound: `equiv` (same accepted words) holds
   between the pre-rewrite and post-rewrite shapes.

   Scope: the structural/algebraic rewrite rules of each `mk_re_*`
   function that do not depend on `rex::info`/`min_length`/`max_length`
   static analysis (already the subject of REGEX_REPORT.md) or on the
   heuristic subset/range-predicate search machinery
   (`is_subset`/`merge_regex_sets`/`try_collapse_re_union`/
   `try_collapse_re_inter`/`range_predicate` algebra). Those are listed
   explicitly as "Not covered" per function below, mirroring the
   scoping convention used throughout SEQ_REWRITER_REPORT.md.

   See SEQ_REWRITER_REPORT.md, Part 3, for the per-function coverage
   table this file is the proof companion to.
*)
module Z3RegexRewrites

open Z3SeqTheory
open Z3RegexTheory
open Z3SeqRewrites
module Classical = FStar.Classical

(* ================================================================= *)
(* Foundational lemmas (reused by several `mk_re_*` theorems below)   *)
(* ================================================================= *)

(* w1 in L^i, w2 in L^j ==> w1++w2 in L^(i+j). The "easy" (subset)
   direction of pow-addition; used wherever a rewrite rule *combines*
   two bounded-repetition languages (e.g. the `mk_re_loop`/
   `mk_re_concat` loop-addition rules below). *)
let rec lemma_pow_concat_intro (#a:eqtype) (l:lang a) (i j:nat) (w1 w2:seq a)
  : Lemma (requires mem w1 (re_pow l i) /\ mem w2 (re_pow l j))
          (ensures mem (concat w1 w2) (re_pow l (i + j)))
          (decreases i)
  = if i = 0 then lemma_concat_empty_l w2
    else
      elim_concat l (re_pow l (i - 1)) w1 (mem (concat w1 w2) (re_pow l (i + j))) (fun u1 u2 ->
        lemma_pow_concat_intro l (i - 1) j u2 w2;
        lemma_concat_assoc u1 u2 w2;
        intro_concat l (re_pow l (i - 1 + j)) (concat w1 w2) u1 (concat u2 w2))

(* L^(m+k) == L^m . L^k, as languages. The full (both-directions)
   pow-addition law; the forward (easy/subset) direction restates
   `lemma_pow_concat_intro`, the backward direction decomposes an
   (m+k)-fold repetition at the m-th repetition boundary. *)
let rec lemma_pow_add (#a:eqtype) (l:lang a) (m k:nat)
  : Lemma (equiv (re_pow l (m + k)) (re_concat (re_pow l m) (re_pow l k)))
          (decreases m)
  = if m = 0 then begin
      let fwd (w:seq a) : Lemma (requires mem w (re_pow l k)) (ensures mem w (re_concat (re_pow l 0) (re_pow l k))) =
        intro_concat (re_pow l 0) (re_pow l k) w empty w
      in
      let bwd (w:seq a) : Lemma (requires mem w (re_concat (re_pow l 0) (re_pow l k))) (ensures mem w (re_pow l k)) =
        elim_concat (re_pow l 0) (re_pow l k) w (mem w (re_pow l k)) (fun w1 w2 -> ())
      in
      let proof (w:seq a) : Lemma (mem w (re_pow l k) <==> mem w (re_concat (re_pow l 0) (re_pow l k))) =
        Classical.move_requires fwd w;
        Classical.move_requires bwd w
      in
      Classical.forall_intro proof
    end
    else begin
      lemma_pow_add l (m - 1) k;
      let fwd (w:seq a)
        : Lemma (requires mem w (re_pow l (m + k)))
                (ensures mem w (re_concat (re_pow l m) (re_pow l k))) =
        elim_concat l (re_pow l (m - 1 + k)) w (mem w (re_concat (re_pow l m) (re_pow l k))) (fun w1 w2 ->
          elim_concat (re_pow l (m - 1)) (re_pow l k) w2 (mem w (re_concat (re_pow l m) (re_pow l k))) (fun w2a w2b ->
            lemma_concat_assoc w1 w2a w2b;
            intro_concat l (re_pow l (m - 1)) (concat w1 w2a) w1 w2a;
            intro_concat (re_pow l m) (re_pow l k) w (concat w1 w2a) w2b))
      in
      let bwd (w:seq a)
        : Lemma (requires mem w (re_concat (re_pow l m) (re_pow l k)))
                (ensures mem w (re_pow l (m + k))) =
        elim_concat (re_pow l m) (re_pow l k) w (mem w (re_pow l (m + k))) (fun w1a w2 ->
          elim_concat l (re_pow l (m - 1)) w1a (mem w (re_pow l (m + k))) (fun w1 w1b ->
            lemma_concat_assoc w1 w1b w2;
            lemma_pow_concat_intro l (m - 1) k w1b w2;
            intro_concat l (re_pow l (m - 1 + k)) w w1 (concat w1b w2)))
      in
      let proof (w:seq a)
        : Lemma (mem w (re_pow l (m + k)) <==> mem w (re_concat (re_pow l m) (re_pow l k))) =
        Classical.move_requires fwd w;
        Classical.move_requires bwd w
      in
      Classical.forall_intro proof
    end

(* L^n, for L = re_allchar, is exactly the set of words of length n. *)
let rec lemma_pow_allchar_len (#a:eqtype) (n:nat) (w:seq a)
  : Lemma (ensures mem w (re_pow re_allchar n) <==> len w = n)
          (decreases n)
  = if n = 0 then ()
    else begin
      let fwd () : Lemma (requires mem w (re_pow re_allchar n)) (ensures len w = n) =
        elim_concat re_allchar (re_pow re_allchar (n - 1)) w (len w = n) (fun w1 w2 ->
          lemma_pow_allchar_len (n - 1) w2;
          lemma_len_concat w1 w2)
      in
      let bwd () : Lemma (requires len w = n) (ensures mem w (re_pow re_allchar n)) =
        match w with
        | x :: s' ->
          lemma_pow_allchar_len (n - 1) s';
          intro_concat re_allchar (re_pow re_allchar (n - 1)) w (unit x) s'
      in
      Classical.move_requires fwd ();
      Classical.move_requires bwd ()
    end

(* L+ for L = re_allchar is exactly the set of nonempty words. *)
let lemma_plus_allchar_eq_nonempty (#a:eqtype)
  : Lemma (equiv (re_plus re_allchar) (re_compl (re_to_re empty)))
  = let fwd (w:seq a) : Lemma (requires mem w (re_plus re_allchar)) (ensures mem w (re_compl (re_to_re empty))) =
      Classical.exists_elim (mem w (re_compl (re_to_re empty)))
        #(n:nat{n >= 1}) #(fun n -> mem w (re_pow re_allchar n)) ()
        (fun n -> lemma_pow_allchar_len n w; lemma_len_empty #a)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_compl (re_to_re empty))) (ensures mem w (re_plus re_allchar)) =
      lemma_pow_allchar_len (len w) w;
      Classical.exists_intro (fun (n:nat{n >= 1}) -> mem w (re_pow re_allchar n)) (len w)
    in
    let proof (w:seq a) : Lemma (mem w (re_plus re_allchar) <==> mem w (re_compl (re_to_re empty))) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* ================================================================= *)
(* Plus/star closure under concatenation and idempotence               *)
(* ================================================================= *)

(* L+ is closed under concatenation: concatenating two nonempty-
   repetition words stays in L+ (the total repetition count only
   grows). Used by `lemma_re_plus_plus_idem` below. *)
let lemma_plus_closed_concat (#a:eqtype) (l:lang a) (w1 w2:seq a)
  : Lemma (requires mem w1 (re_plus l) /\ mem w2 (re_plus l))
          (ensures mem (concat w1 w2) (re_plus l))
  = Classical.exists_elim (mem (concat w1 w2) (re_plus l))
      #(i:nat{i >= 1}) #(fun i -> mem w1 (re_pow l i)) ()
      (fun i ->
        Classical.exists_elim (mem (concat w1 w2) (re_plus l))
          #(j:nat{j >= 1}) #(fun j -> mem w2 (re_pow l j)) ()
          (fun j ->
            lemma_pow_concat_intro l i j w1 w2;
            Classical.exists_intro (fun (n:nat{n >= 1}) -> mem (concat w1 w2) (re_pow l n)) (i + j)))

(* (L+)^n (n >= 1 reps of L+) is contained in L+ itself: L+ absorbs
   any further repetition. *)
let rec lemma_pow_plus_closed (#a:eqtype) (l:lang a) (n:nat{n >= 1}) (w:seq a)
  : Lemma (requires mem w (re_pow (re_plus l) n))
          (ensures mem w (re_plus l))
          (decreases n)
  = if n = 1 then
      elim_concat (re_plus l) (re_pow (re_plus l) 0) w (mem w (re_plus l)) (fun w1 w2 ->
        lemma_concat_empty_r w1)
    else
      elim_concat (re_plus l) (re_pow (re_plus l) (n - 1)) w (mem w (re_plus l)) (fun w1 w2 ->
        lemma_pow_plus_closed l (n - 1) w2;
        lemma_plus_closed_concat l w1 w2)

(* (L+)+ == L+ : repeating "one or more reps of L" one-or-more times
   adds nothing new. Z3: `mk_re_plus`, "a++ = a+" (seq_rewriter.cpp,
   see doc comment above `mk_re_plus`). *)
let lemma_re_plus_plus_idem (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_plus (re_plus l)) (re_plus l))
  = let fwd (w:seq a) : Lemma (requires mem w (re_plus (re_plus l))) (ensures mem w (re_plus l)) =
      Classical.exists_elim (mem w (re_plus l))
        #(n:nat{n >= 1}) #(fun n -> mem w (re_pow (re_plus l) n)) ()
        (fun n -> lemma_pow_plus_closed l n w)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_plus l)) (ensures mem w (re_plus (re_plus l))) =
      lemma_concat_empty_r w;
      intro_concat (re_plus l) (re_pow (re_plus l) 0) w w empty;
      Classical.exists_intro (fun (n:nat{n >= 1}) -> mem w (re_pow (re_plus l) n)) 1
    in
    let proof (w:seq a) : Lemma (mem w (re_plus (re_plus l)) <==> mem w (re_plus l)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* L* is closed under concatenation (a weaker, always-true analogue of
   `lemma_plus_closed_concat` -- here `n = 0` is also allowed). *)
let lemma_star_closed_concat (#a:eqtype) (l:lang a) (w1 w2:seq a)
  : Lemma (requires mem w1 (re_star l) /\ mem w2 (re_star l))
          (ensures mem (concat w1 w2) (re_star l))
  = Classical.exists_elim (mem (concat w1 w2) (re_star l))
      #nat #(fun i -> mem w1 (re_pow l i)) ()
      (fun i ->
        Classical.exists_elim (mem (concat w1 w2) (re_star l))
          #nat #(fun j -> mem w2 (re_pow l j)) ()
          (fun j ->
            lemma_pow_concat_intro l i j w1 w2;
            Classical.exists_intro (fun (n:nat) -> mem (concat w1 w2) (re_pow l n)) (i + j)))

(* (L-star)^n (n reps of L-star) is contained in L-star itself. *)
let rec lemma_pow_star_closed (#a:eqtype) (l:lang a) (n:nat) (w:seq a)
  : Lemma (requires mem w (re_pow (re_star l) n))
          (ensures mem w (re_star l))
          (decreases n)
  = if n = 0 then lemma_star_nil l
    else
      elim_concat (re_star l) (re_pow (re_star l) (n - 1)) w (mem w (re_star l)) (fun w1 w2 ->
        lemma_pow_star_closed l (n - 1) w2;
        lemma_star_closed_concat l w1 w2)

(* (L-star)-star == L-star : a classic Kleene-star idempotence fact. Z3: `mk_re_star`,
   "a** = a*" (doc comment above `mk_re_star`). *)
let lemma_re_star_star_idem (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_star (re_star l)) (re_star l))
  = let fwd (w:seq a) : Lemma (requires mem w (re_star (re_star l))) (ensures mem w (re_star l)) =
      Classical.exists_elim (mem w (re_star l))
        #nat #(fun n -> mem w (re_pow (re_star l) n)) ()
        (fun n -> lemma_pow_star_closed l n w)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_star l)) (ensures mem w (re_star (re_star l))) =
      lemma_star_contains_self (re_star l) w
    in
    let proof (w:seq a) : Lemma (mem w (re_star (re_star l)) <==> mem w (re_star l)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* ================================================================= *)
(* mk_re_plus (seq_rewriter.cpp:4319-4349)                             *)
(*                                                                      *)
(* Doc comment:  emp+ = emp / all+ = all / a*+ = a* / a++ = a+ /       *)
(*               a+ = a.a*                                              *)
(* ================================================================= *)

(* emp+ = emp. *)
let lemma_re_plus_empty (#a:eqtype)
  : Lemma (equiv (re_plus (re_empty #a)) re_empty)
  = ()

(* all+ = all (Sigma-star is already closed under "one or more reps";
   e.g. witness n = 1 shows any word is in Sigma-star-plus). *)
let lemma_re_plus_full (#a:eqtype)
  : Lemma (equiv (re_plus (re_full #a)) re_full)
  = let bwd (w:seq a) : Lemma (ensures mem w (re_plus re_full)) =
      lemma_concat_empty_r w;
      intro_concat re_full (re_pow re_full 0) w w empty;
      Classical.exists_intro (fun (n:nat{n >= 1}) -> mem w (re_pow re_full n)) 1
    in
    Classical.forall_intro bwd

(* mem w (to_re epsilon)^n <==> w == empty, for all n (every repetition
   of the empty word contributes nothing). *)
let rec lemma_pow_epsilon (#a:eqtype) (n:nat) (w:seq a)
  : Lemma (ensures mem w (re_pow (re_to_re empty) n) <==> w == empty)
          (decreases n)
  = if n = 0 then ()
    else begin
      let fwd () : Lemma (requires mem w (re_pow (re_to_re empty) n)) (ensures w == empty) =
        elim_concat (re_to_re empty) (re_pow (re_to_re empty) (n - 1)) w (w == empty) (fun w1 w2 ->
          lemma_pow_epsilon (n - 1) w2)
      in
      let bwd () : Lemma (requires w == empty) (ensures mem w (re_pow (re_to_re empty) n)) =
        lemma_pow_epsilon (n - 1) (empty #a);
        intro_concat (re_to_re empty) (re_pow (re_to_re empty) (n - 1)) w empty empty
      in
      Classical.move_requires fwd ();
      Classical.move_requires bwd ()
    end

(* epsilon+ = epsilon. *)
let lemma_re_plus_epsilon (#a:eqtype)
  : Lemma (equiv (re_plus (re_to_re #a empty)) (re_to_re empty))
  = let fwd (w:seq a) : Lemma (requires mem w (re_plus (re_to_re empty))) (ensures mem w (re_to_re empty)) =
      Classical.exists_elim (mem w (re_to_re empty))
        #(n:nat{n >= 1}) #(fun n -> mem w (re_pow (re_to_re empty) n)) ()
        (fun n -> lemma_pow_epsilon n w)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_to_re empty)) (ensures mem w (re_plus (re_to_re empty))) =
      lemma_pow_epsilon 1 w;
      Classical.exists_intro (fun (n:nat{n >= 1}) -> mem w (re_pow (re_to_re empty) n)) 1
    in
    let proof (w:seq a) : Lemma (mem w (re_plus (re_to_re empty)) <==> mem w (re_to_re empty)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* (L-star)+ == L-star : repeating L-star "one or more times" is the same as L-star,
   since L-star already absorbs any extra repetitions (`lemma_star_closed_concat`).
   Z3: `mk_re_plus`, "a*+ = a*". *)
let lemma_re_plus_star_idem (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_plus (re_star l)) (re_star l))
  = let fwd (w:seq a) : Lemma (requires mem w (re_plus (re_star l))) (ensures mem w (re_star l)) =
      Classical.exists_elim (mem w (re_star l))
        #(n:nat{n >= 1}) #(fun n -> mem w (re_pow (re_star l) n)) ()
        (fun n -> lemma_pow_star_closed l n w)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_star l)) (ensures mem w (re_plus (re_star l))) =
      lemma_concat_empty_r w;
      intro_concat (re_star l) (re_pow (re_star l) 0) w w empty;
      Classical.exists_intro (fun (n:nat{n >= 1}) -> mem w (re_pow (re_star l) n)) 1
    in
    let proof (w:seq a) : Lemma (mem w (re_plus (re_star l)) <==> mem w (re_star l)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* ----------------------------------------------------------------------- *)
(* Generic monotonicity helpers.                                           *)
(* These let us lift a pointwise language containment through `re_pow`,    *)
(* `re_star`, and `re_concat`, which is the key technique for proving the  *)
(* "absorption" rewrite rules of `mk_re_star` (e.g. folding `a* | b` or    *)
(* `a* . b*` back into `(a|b)*`). *)
(* ----------------------------------------------------------------------- *)

let rec lemma_pow_mono (#a:eqtype) (l1 l2:lang a) (n:nat) (w:seq a)
  : Lemma (requires (forall (u:seq a). mem u l1 ==> mem u l2) /\ mem w (re_pow l1 n))
          (ensures mem w (re_pow l2 n))
          (decreases n)
  = if n = 0 then ()
    else
      elim_concat l1 (re_pow l1 (n - 1)) w (mem w (re_pow l2 n))
        (fun w1 w2 ->
          lemma_pow_mono l1 l2 (n - 1) w2;
          intro_concat l2 (re_pow l2 (n - 1)) w w1 w2)

let lemma_star_mono (#a:eqtype) (l1 l2:lang a) (w:seq a)
  : Lemma (requires (forall (u:seq a). mem u l1 ==> mem u l2) /\ mem w (re_star l1))
          (ensures mem w (re_star l2))
  = Classical.exists_elim (mem w (re_star l2)) #nat #(fun n -> mem w (re_pow l1 n)) ()
      (fun n ->
        lemma_pow_mono l1 l2 n w;
        Classical.exists_intro (fun (m:nat) -> mem w (re_pow l2 m)) n)

let lemma_concat_mono (#a:eqtype) (l1 l2 l1' l2':lang a) (w:seq a)
  : Lemma (requires (forall (u:seq a). mem u l1 ==> mem u l1')
                   /\ (forall (u:seq a). mem u l2 ==> mem u l2')
                   /\ mem w (re_concat l1 l2))
          (ensures mem w (re_concat l1' l2'))
  = elim_concat l1 l2 w (mem w (re_concat l1' l2'))
      (fun w1 w2 -> intro_concat l1' l2' w w1 w2)

(* L ⊆ L+ : every element of L is already a one-fold repetition. *)
let lemma_l_subset_plus (#a:eqtype) (l:lang a) (w:seq a)
  : Lemma (requires mem w l) (ensures mem w (re_plus l))
  = lemma_concat_empty_r w;
    intro_concat l (re_pow l 0) w w empty;
    Classical.exists_intro (fun (n:nat{n >= 1}) -> mem w (re_pow l n)) 1

(* L+ ⊆ L* : "one or more" repetitions is a special case of "zero or more". *)
let lemma_plus_subset_star (#a:eqtype) (l:lang a) (w:seq a)
  : Lemma (requires mem w (re_plus l)) (ensures mem w (re_star l))
  = Classical.exists_elim (mem w (re_star l))
      #(n:nat{n >= 1}) #(fun n -> mem w (re_pow l n)) ()
      (fun n -> Classical.exists_intro (fun (m:nat) -> mem w (re_pow l m)) n)

(* ----------------------------------------------------------------------- *)
(* `mk_re_star` (seq_rewriter.cpp:4165-4242).                              *)
(* ----------------------------------------------------------------------- *)

(* a* for a = empty-set, full-set, allchar, epsilon : definitional/closed-
   form base cases, Z3's early special-case branches of `mk_re_star`. *)

let lemma_re_star_full (#a:eqtype) : Lemma (equiv (re_star (re_full #a)) re_full)
  = let bwd (w:seq a) : Lemma (ensures mem w (re_star re_full)) =
      lemma_concat_empty_r w;
      intro_concat re_full (re_pow re_full 0) w w empty;
      Classical.exists_intro (fun (n:nat) -> mem w (re_pow re_full n)) 1
    in
    Classical.forall_intro bwd

let lemma_re_star_allchar (#a:eqtype) : Lemma (equiv (re_star (re_allchar #a)) re_full)
  = let bwd (w:seq a) : Lemma (ensures mem w (re_star re_allchar)) =
      lemma_pow_allchar_len (len w) w;
      Classical.exists_intro (fun (n:nat) -> mem w (re_pow re_allchar n)) (len w)
    in
    Classical.forall_intro bwd

let lemma_re_star_empty (#a:eqtype) : Lemma (equiv (re_star (re_empty #a)) (re_to_re empty))
  = let fwd (w:seq a) : Lemma (requires mem w (re_star re_empty)) (ensures mem w (re_to_re empty)) =
      Classical.exists_elim (mem w (re_to_re empty)) #nat #(fun n -> mem w (re_pow re_empty n)) ()
        (fun n ->
          if n = 0 then ()
          else
            elim_concat re_empty (re_pow re_empty (n - 1)) w (mem w (re_to_re empty))
              (fun w1 w2 -> ()))
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_to_re empty)) (ensures mem w (re_star re_empty)) =
      Classical.exists_intro (fun (n:nat) -> mem w (re_pow re_empty n)) 0
    in
    let proof (w:seq a) : Lemma (mem w (re_star re_empty) <==> mem w (re_to_re empty)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

let lemma_re_star_epsilon (#a:eqtype) : Lemma (equiv (re_star (re_to_re #a empty)) (re_to_re empty))
  = let fwd (w:seq a) : Lemma (requires mem w (re_star (re_to_re empty))) (ensures mem w (re_to_re empty)) =
      Classical.exists_elim (mem w (re_to_re empty)) #nat #(fun n -> mem w (re_pow (re_to_re empty) n)) ()
        (fun n -> lemma_pow_epsilon n w)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_to_re empty)) (ensures mem w (re_star (re_to_re empty))) =
      Classical.exists_intro (fun (n:nat) -> mem w (re_pow (re_to_re empty) n)) 0
    in
    let proof (w:seq a) : Lemma (mem w (re_star (re_to_re empty)) <==> mem w (re_to_re empty)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* (a+)* == a* : Z3's `mk_re_star`, "a+* = a*" (the dual of `mk_re_plus`'s
   "a*+ = a*" proved above as `lemma_re_plus_star_idem`). *)
let lemma_re_star_plus_idem (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_star (re_plus l)) (re_star l))
  = let fwd (w:seq a) : Lemma (requires mem w (re_star (re_plus l))) (ensures mem w (re_star l)) =
      Classical.forall_intro (Classical.move_requires (lemma_plus_subset_star l));
      Classical.exists_elim (mem w (re_star l)) #nat #(fun n -> mem w (re_pow (re_plus l) n)) ()
        (fun n ->
          lemma_pow_mono (re_plus l) (re_star l) n w;
          lemma_pow_star_closed l n w)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_star l)) (ensures mem w (re_star (re_plus l))) =
      Classical.forall_intro (Classical.move_requires (lemma_l_subset_plus l));
      Classical.exists_elim (mem w (re_star (re_plus l))) #nat #(fun n -> mem w (re_pow l n)) ()
        (fun n -> lemma_pow_mono l (re_plus l) n w)
    in
    let proof (w:seq a) : Lemma (mem w (re_star (re_plus l)) <==> mem w (re_star l)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* (ε | a)* == a* : adding the empty word to a language doesn't change its
   Kleene star, since ε is already a "free" repetition. Z3's `mk_re_star`
   folds `union(b,c)` into `mk_star(c)` when `b` is epsilon. *)
let lemma_re_star_union_epsilon (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_star (re_union (re_to_re empty) l)) (re_star l))
  = let rec fwd_n (n:nat) (w:seq a)
      : Lemma (requires mem w (re_pow (re_union (re_to_re empty) l) n))
              (ensures mem w (re_star l))
              (decreases n)
      = if n = 0 then ()
        else
          elim_concat (re_union (re_to_re empty) l) (re_pow (re_union (re_to_re empty) l) (n - 1))
            w (mem w (re_star l))
            (fun w1 w2 ->
              fwd_n (n - 1) w2;
              if mem w1 (re_to_re empty)
              then lemma_concat_empty_l w2
              else begin
                lemma_star_contains_self l w1;
                lemma_star_closed_concat l w1 w2
              end)
    in
    let fwd (w:seq a) : Lemma (requires mem w (re_star (re_union (re_to_re empty) l))) (ensures mem w (re_star l)) =
      Classical.exists_elim (mem w (re_star l)) #nat #(fun n -> mem w (re_pow (re_union (re_to_re empty) l) n)) ()
        (fun n -> fwd_n n w)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_star l)) (ensures mem w (re_star (re_union (re_to_re empty) l))) =
      lemma_star_mono l (re_union (re_to_re empty) l) w
    in
    let proof (w:seq a) : Lemma (mem w (re_star (re_union (re_to_re empty) l)) <==> mem w (re_star l)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* (a-star | b)-star == (a | b)-star : Z3's `mk_re_star`, the "fold a nested
   star back into the union before re-starring" rule (the symmetric case
   with `a-star` on the right of the union is obtained by precomposing
   with `lemma_union_comm`). *)
let lemma_re_star_union_star_absorb (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_star (re_union (re_star l1) l2)) (re_star (re_union l1 l2)))
  = let c1 (w:seq a) : Lemma (requires mem w (re_union (re_star l1) l2))
                             (ensures mem w (re_star (re_union l1 l2))) =
      if mem w (re_star l1)
      then lemma_star_mono l1 (re_union l1 l2) w
      else begin
        lemma_l_subset_plus (re_union l1 l2) w;
        lemma_plus_subset_star (re_union l1 l2) w
      end
    in
    let c2 (w:seq a) : Lemma (requires mem w (re_union l1 l2))
                             (ensures mem w (re_union (re_star l1) l2)) =
      if mem w l1
      then begin
        lemma_l_subset_plus l1 w;
        lemma_plus_subset_star l1 w
      end
    in
    let fwd (w:seq a) : Lemma (requires mem w (re_star (re_union (re_star l1) l2)))
                              (ensures mem w (re_star (re_union l1 l2))) =
      Classical.exists_elim (mem w (re_star (re_union l1 l2)))
        #nat #(fun n -> mem w (re_pow (re_union (re_star l1) l2) n)) ()
        (fun n ->
          Classical.forall_intro (Classical.move_requires c1);
          lemma_pow_mono (re_union (re_star l1) l2) (re_star (re_union l1 l2)) n w;
          lemma_pow_star_closed (re_union l1 l2) n w)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_star (re_union l1 l2)))
                              (ensures mem w (re_star (re_union (re_star l1) l2))) =
      Classical.exists_elim (mem w (re_star (re_union (re_star l1) l2)))
        #nat #(fun n -> mem w (re_pow (re_union l1 l2) n)) ()
        (fun n ->
          Classical.forall_intro (Classical.move_requires c2);
          lemma_pow_mono (re_union l1 l2) (re_union (re_star l1) l2) n w;
          Classical.exists_intro (fun (m:nat) -> mem w (re_pow (re_union (re_star l1) l2) m)) n)
    in
    let proof (w:seq a) : Lemma (mem w (re_star (re_union (re_star l1) l2)) <==> mem w (re_star (re_union l1 l2))) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* (a-star . b-star)-star == (a | b)-star : Z3's `mk_re_star`, folding a
   concatenation of two starred sub-languages back into a union before
   re-starring. *)
let lemma_re_star_concat_star_star (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_star (re_concat (re_star l1) (re_star l2))) (re_star (re_union l1 l2)))
  =   let c1 (w:seq a) : Lemma (requires mem w (re_concat (re_star l1) (re_star l2)))
                           (ensures mem w (re_star (re_union l1 l2))) =
    elim_concat (re_star l1) (re_star l2) w (mem w (re_star (re_union l1 l2)))
        (fun w1 w2 ->
          lemma_star_mono l1 (re_union l1 l2) w1;
          lemma_star_mono l2 (re_union l1 l2) w2;
          lemma_star_closed_concat (re_union l1 l2) w1 w2)
    in
    let c2 (w:seq a) : Lemma (requires mem w (re_union l1 l2))
                             (ensures mem w (re_concat (re_star l1) (re_star l2))) =
      if mem w l1
      then begin
        lemma_concat_empty_r w;
        lemma_star_contains_self l1 w;
        lemma_star_nil #a l2;
        intro_concat (re_star l1) (re_star l2) w w empty
      end else begin
        lemma_concat_empty_l w;
        lemma_star_nil #a l1;
        lemma_star_contains_self l2 w;
        intro_concat (re_star l1) (re_star l2) w empty w
      end
    in
    let fwd (w:seq a) : Lemma (requires mem w (re_star (re_concat (re_star l1) (re_star l2))))
                              (ensures mem w (re_star (re_union l1 l2))) =
      Classical.exists_elim (mem w (re_star (re_union l1 l2)))
        #nat #(fun n -> mem w (re_pow (re_concat (re_star l1) (re_star l2)) n)) ()
        (fun n ->
          Classical.forall_intro (Classical.move_requires c1);
          lemma_pow_mono (re_concat (re_star l1) (re_star l2)) (re_star (re_union l1 l2)) n w;
          lemma_pow_star_closed (re_union l1 l2) n w)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_star (re_union l1 l2)))
                              (ensures mem w (re_star (re_concat (re_star l1) (re_star l2)))) =
      Classical.exists_elim (mem w (re_star (re_concat (re_star l1) (re_star l2))))
        #nat #(fun n -> mem w (re_pow (re_union l1 l2) n)) ()
        (fun n ->
          Classical.forall_intro (Classical.move_requires c2);
          lemma_pow_mono (re_union l1 l2) (re_concat (re_star l1) (re_star l2)) n w;
          Classical.exists_intro (fun (m:nat) -> mem w (re_pow (re_concat (re_star l1) (re_star l2)) m)) n)
    in
    let proof (w:seq a) : Lemma (mem w (re_star (re_concat (re_star l1) (re_star l2))) <==> mem w (re_star (re_union l1 l2))) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* Not covered (mk_re_star): the `rex::info`-driven `min_length`/
   `max_length` special cases, and any branch relying on `is_subset` /
   `merge_regex_sets` to detect semantic (as opposed to syntactic)
   containment between the union/concat arguments above. *)

(* ----------------------------------------------------------------------- *)
(* `mk_re_opt` (seq_rewriter.cpp:4349-end).                                *)
(* `mk_re_opt(a)` is literally *defined* as `mk_re_union(to_re(epsilon), a)`
   in seq_rewriter.cpp, i.e. `re_opt` is definitionally
   `re_union (re_to_re empty) l` in `Z3RegexTheory.fst` already
   (`lemma_opt_is_loop_0_1` relates it to `re_loop l 0 1`); no further
   per-branch proof obligation arises here beyond what `Z3RegexTheory.fst`
   already establishes. *)

(* ----------------------------------------------------------------------- *)
(* `mk_re_reverse` (seq_rewriter.cpp:2876-2969).                           *)
(* Reverse pushes through every regex connective. The concat/double-       *)
(* reverse cases are already proved in `Z3RegexTheory.fst`                *)
(* (`lemma_reverse_concat_lang`, `lemma_reverse_reverse_lang`); the        *)
(* union/inter/diff/xor/complement cases are pure propositional unfolding *)
(* of `re_reverse`'s definition (no induction needed); the star/plus/loop  *)
(* cases need pushing reverse through `re_pow`, proved below via           *)
(* `lemma_reverse_pow`. *)
(* ----------------------------------------------------------------------- *)

(* Congruence: concatenation respects language equivalence in both
   arguments. Used to push `equiv` facts about sub-languages (e.g. an
   inductive hypothesis) through `re_concat`/`re_pow`. *)
let lemma_concat_congr (#a:eqtype) (l1 l2 l1' l2':lang a)
  : Lemma (requires equiv l1 l1' /\ equiv l2 l2')
          (ensures equiv (re_concat l1 l2) (re_concat l1' l2'))
  = let fwd (w:seq a) : Lemma (requires mem w (re_concat l1 l2)) (ensures mem w (re_concat l1' l2')) =
      elim_concat l1 l2 w (mem w (re_concat l1' l2')) (fun w1 w2 -> intro_concat l1' l2' w w1 w2)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_concat l1' l2')) (ensures mem w (re_concat l1 l2)) =
      elim_concat l1' l2' w (mem w (re_concat l1 l2)) (fun w1 w2 -> intro_concat l1 l2 w w1 w2)
    in
    let proof (w:seq a) : Lemma (mem w (re_concat l1 l2) <==> mem w (re_concat l1' l2')) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* reverse(L^n) == (reverse L)^n : the key lemma generalizing
   `lemma_reverse_concat_lang` from one concatenation to `n` repetitions. *)
let rec lemma_reverse_pow (#a:eqtype) (l:lang a) (n:nat)
  : Lemma (ensures equiv (re_reverse (re_pow l n)) (re_pow (re_reverse l) n))
          (decreases n)
  = if n = 0 then begin
      let proof (w:seq a) : Lemma (mem w (re_reverse (re_pow l 0)) <==> mem w (re_pow (re_reverse l) 0)) =
        lemma_reverse_reverse w
      in
      Classical.forall_intro proof
    end else begin
      lemma_reverse_pow l (n - 1);
      let fwd (w:seq a) : Lemma (requires mem w (re_reverse (re_pow l n)))
                                (ensures mem w (re_pow (re_reverse l) n)) =
        elim_concat l (re_pow l (n - 1)) (reverse w) (mem w (re_pow (re_reverse l) n))
          (fun w1 w2 ->
            lemma_reverse_concat w1 w2;
            lemma_reverse_reverse w;
            lemma_reverse_reverse w1;
            lemma_reverse_reverse w2;
            intro_concat (re_pow (re_reverse l) (n - 1)) (re_reverse l) w (reverse w2) (reverse w1);
            lemma_pow_add (re_reverse l) (n - 1) 1;
            lemma_concat_unit_r (re_reverse l);
            lemma_concat_congr (re_pow (re_reverse l) (n - 1)) (re_reverse l)
                                (re_pow (re_reverse l) (n - 1)) (re_pow (re_reverse l) 1))
      in
      let bwd (w:seq a) : Lemma (requires mem w (re_pow (re_reverse l) n))
                                (ensures mem w (re_reverse (re_pow l n))) =
        lemma_pow_add (re_reverse l) (n - 1) 1;
        lemma_concat_unit_r (re_reverse l);
        lemma_concat_congr (re_pow (re_reverse l) (n - 1)) (re_reverse l)
                            (re_pow (re_reverse l) (n - 1)) (re_pow (re_reverse l) 1);
        elim_concat (re_pow (re_reverse l) (n - 1)) (re_reverse l) w (mem w (re_reverse (re_pow l n)))
          (fun w1 w2 ->
            lemma_reverse_concat w1 w2;
            intro_concat l (re_pow l (n - 1)) (reverse w) (reverse w2) (reverse w1))
      in
      let proof (w:seq a) : Lemma (mem w (re_reverse (re_pow l n)) <==> mem w (re_pow (re_reverse l) n)) =
        Classical.move_requires fwd w;
        Classical.move_requires bwd w
      in
      Classical.forall_intro proof
    end

(* reverse(L-star) == (reverse L)-star : Z3's `mk_re_reverse`, "star" case. *)
let lemma_reverse_star (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_reverse (re_star l)) (re_star (re_reverse l)))
  = let fwd (w:seq a) : Lemma (requires mem w (re_reverse (re_star l))) (ensures mem w (re_star (re_reverse l))) =
      Classical.exists_elim (mem w (re_star (re_reverse l))) #nat #(fun n -> mem (reverse w) (re_pow l n)) ()
        (fun n ->
          lemma_reverse_pow l n;
          Classical.exists_intro (fun (m:nat) -> mem w (re_pow (re_reverse l) m)) n)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_star (re_reverse l))) (ensures mem w (re_reverse (re_star l))) =
      Classical.exists_elim (mem w (re_reverse (re_star l))) #nat #(fun n -> mem w (re_pow (re_reverse l) n)) ()
        (fun n ->
          lemma_reverse_pow l n;
          Classical.exists_intro (fun (m:nat) -> mem (reverse w) (re_pow l m)) n)
    in
    let proof (w:seq a) : Lemma (mem w (re_reverse (re_star l)) <==> mem w (re_star (re_reverse l))) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* reverse(L+) == (reverse L)+ : Z3's `mk_re_reverse`, "plus" case. *)
let lemma_reverse_plus (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_reverse (re_plus l)) (re_plus (re_reverse l)))
  = let fwd (w:seq a) : Lemma (requires mem w (re_reverse (re_plus l))) (ensures mem w (re_plus (re_reverse l))) =
      Classical.exists_elim (mem w (re_plus (re_reverse l)))
        #(n:nat{n >= 1}) #(fun n -> mem (reverse w) (re_pow l n)) ()
        (fun n ->
          lemma_reverse_pow l n;
          Classical.exists_intro (fun (m:nat{m >= 1}) -> mem w (re_pow (re_reverse l) m)) n)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_plus (re_reverse l))) (ensures mem w (re_reverse (re_plus l))) =
      Classical.exists_elim (mem w (re_reverse (re_plus l)))
        #(n:nat{n >= 1}) #(fun n -> mem w (re_pow (re_reverse l) n)) ()
        (fun n ->
          lemma_reverse_pow l n;
          Classical.exists_intro (fun (m:nat{m >= 1}) -> mem (reverse w) (re_pow l m)) n)
    in
    let proof (w:seq a) : Lemma (mem w (re_reverse (re_plus l)) <==> mem w (re_plus (re_reverse l))) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* reverse(union a b) == union (reverse a) (reverse b), and likewise for
   inter/diff/xor/complement: pure propositional unfolding of
   `re_reverse`'s definition, no induction required. Z3's `mk_re_reverse`
   "union"/"intersection"/"diff"/"xor"/"complement" cases. *)
let lemma_reverse_union (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_reverse (re_union l1 l2)) (re_union (re_reverse l1) (re_reverse l2)))
  = ()

let lemma_reverse_inter (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_reverse (re_inter l1 l2)) (re_inter (re_reverse l1) (re_reverse l2)))
  = ()

let lemma_reverse_diff (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_reverse (re_diff l1 l2)) (re_diff (re_reverse l1) (re_reverse l2)))
  = ()

let lemma_reverse_xor (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_reverse (re_xor l1 l2)) (re_xor (re_reverse l1) (re_reverse l2)))
  = ()

let lemma_reverse_complement (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_reverse (re_compl l)) (re_compl (re_reverse l)))
  = ()

(* reverse(opt a) == opt(reverse a) : `re_opt l = re_union (re_to_re empty) l`,
   and `re_reverse (re_to_re empty)` accepts exactly `empty` (reverse of the
   empty word is itself), so this reduces to `lemma_reverse_union`. *)
let lemma_reverse_opt (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_reverse (re_opt l)) (re_opt (re_reverse l)))
  = lemma_reverse_union (re_to_re empty) l

(* reverse(loop a lo hi) == loop (reverse a) lo hi, and the unbounded
   `re_loop_lo` variant: both reduce to `lemma_reverse_pow` pointwise.
   Z3's `mk_re_reverse` "loop" cases (both the 1-arg and 2-arg `re.loop`
   overloads). *)
let lemma_reverse_loop (#a:eqtype) (l:lang a) (lo hi:nat)
  : Lemma (equiv (re_reverse (re_loop l lo hi)) (re_loop (re_reverse l) lo hi))
  = let fwd (w:seq a) : Lemma (requires mem w (re_reverse (re_loop l lo hi)))
                              (ensures mem w (re_loop (re_reverse l) lo hi)) =
      Classical.exists_elim (mem w (re_loop (re_reverse l) lo hi))
        #(n:nat{lo <= n /\ n <= hi}) #(fun n -> mem (reverse w) (re_pow l n)) ()
        (fun n ->
          lemma_reverse_pow l n;
          Classical.exists_intro (fun (m:nat{lo <= m /\ m <= hi}) -> mem w (re_pow (re_reverse l) m)) n)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_loop (re_reverse l) lo hi))
                              (ensures mem w (re_reverse (re_loop l lo hi))) =
      Classical.exists_elim (mem w (re_reverse (re_loop l lo hi)))
        #(n:nat{lo <= n /\ n <= hi}) #(fun n -> mem w (re_pow (re_reverse l) n)) ()
        (fun n ->
          lemma_reverse_pow l n;
          Classical.exists_intro (fun (m:nat{lo <= m /\ m <= hi}) -> mem (reverse w) (re_pow l m)) n)
    in
    let proof (w:seq a) : Lemma (mem w (re_reverse (re_loop l lo hi)) <==> mem w (re_loop (re_reverse l) lo hi)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* L* . L^n == L^n . L* (as languages, not as syntactic terms): both sides
   describe exactly "n or more repetitions of L". The key fact needed to
   relate `re_loop_lo` (defined `pow lo . star`) to its reverse, which
   naturally produces the opposite concatenation order `star . pow lo`. *)
let lemma_star_pow_comm (#a:eqtype) (l:lang a) (n:nat)
  : Lemma (equiv (re_concat (re_star l) (re_pow l n)) (re_concat (re_pow l n) (re_star l)))
  = let fwd (w:seq a) : Lemma (requires mem w (re_concat (re_star l) (re_pow l n)))
                              (ensures mem w (re_concat (re_pow l n) (re_star l))) =
      elim_concat (re_star l) (re_pow l n) w (mem w (re_concat (re_pow l n) (re_star l)))
        (fun w1 w2 ->
          Classical.exists_elim (mem w (re_concat (re_pow l n) (re_star l)))
            #nat #(fun k -> mem w1 (re_pow l k)) ()
            (fun k ->
              intro_concat (re_pow l k) (re_pow l n) w w1 w2;
              lemma_pow_add l k n;
              lemma_pow_add l n k;
              elim_concat (re_pow l n) (re_pow l k) w (mem w (re_concat (re_pow l n) (re_star l)))
                (fun u1 u2 ->
                  Classical.exists_intro (fun (m:nat) -> mem u2 (re_pow l m)) k;
                  intro_concat (re_pow l n) (re_star l) w u1 u2)))
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_concat (re_pow l n) (re_star l)))
                              (ensures mem w (re_concat (re_star l) (re_pow l n))) =
      elim_concat (re_pow l n) (re_star l) w (mem w (re_concat (re_star l) (re_pow l n)))
        (fun w1 w2 ->
          Classical.exists_elim (mem w (re_concat (re_star l) (re_pow l n)))
            #nat #(fun k -> mem w2 (re_pow l k)) ()
            (fun k ->
              intro_concat (re_pow l n) (re_pow l k) w w1 w2;
              lemma_pow_add l n k;
              lemma_pow_add l k n;
              elim_concat (re_pow l k) (re_pow l n) w (mem w (re_concat (re_star l) (re_pow l n)))
                (fun u1 u2 ->
                  Classical.exists_intro (fun (m:nat) -> mem u1 (re_pow l m)) k;
                  intro_concat (re_star l) (re_pow l n) w u1 u2)))
    in
    let proof (w:seq a) : Lemma (mem w (re_concat (re_star l) (re_pow l n)) <==> mem w (re_concat (re_pow l n) (re_star l))) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

let lemma_reverse_loop_lo (#a:eqtype) (l:lang a) (lo:nat)
  : Lemma (equiv (re_reverse (re_loop_lo l lo)) (re_loop_lo (re_reverse l) lo))
  = lemma_reverse_concat_lang (re_pow l lo) (re_star l);
    lemma_reverse_pow l lo;
    lemma_reverse_star l;
    lemma_concat_congr (re_reverse (re_star l)) (re_reverse (re_pow l lo))
                        (re_star (re_reverse l)) (re_pow (re_reverse l) lo);
    lemma_star_pow_comm (re_reverse l) lo

(* reverse(to_re s) for a literal `s` already stored as a plain Z3 string
   is a definitional identity, not a language-level theorem: this file's
   `lang a` model has no native string-literal type to mirror
   `str().mk_string(zs.reverse())`, so this branch is out of scope here
   (it is pure data manipulation, not a semantic rewrite). Likewise the
   `to_re(unit x)` and `to_re(concat s1 s2)` branches of `mk_re_reverse`
   reduce, at the `lang a` level, to instances of `lemma_reverse_pow`
   (n=1) and `lemma_reverse_concat_lang` respectively, already covered
   above. *)

(* Not covered (mk_re_reverse): the `ite`-tree branch (mirrors
   `Z3BasicExprTheory`'s `ite` case, not a regex-specific rewrite), and the
   `is_full_seq`/`is_empty`/`is_range`/`is_full_char`/`is_of_pred`
   self-reverse-invariant branches (these require the extra assumption
   that the underlying predicate/range is symmetric under reversal of a
   length-1 word, which is trivially true for single-symbol languages
   but needs `len w = 1 ==> reverse w == w`, not yet formalized here). *)

(* ----------------------------------------------------------------------- *)
(* `mk_re_union0` / `mk_re_union` (seq_rewriter.cpp:3814-3872).            *)
(* Most branches are pure propositional unfoldings of `re_union`'s          *)
(* definition (`\/`), discharged by the SMT backend with `()` just like   *)
(* `lemma_union_comm` in `Z3RegexTheory.fst`. *)
(* ----------------------------------------------------------------------- *)

let lemma_union_idem (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_union l l) l)
  = ()

let lemma_union_empty_l (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_union (re_empty #a) l) l)
  = ()

let lemma_union_empty_r (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_union l (re_empty #a)) l)
  = ()

let lemma_union_full_l (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_union (re_full #a) l) re_full)
  = ()

let lemma_union_full_r (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_union l (re_full #a)) re_full)
  = ()

(* If l2 is already contained in l1, unioning it in changes nothing.
   Z3: `mk_re_union0`'s "a* | epsilon = a*" rule is the special case
   `l1 = re_star x`, `l2 = re_to_re empty` (via `lemma_star_nil`). *)
let lemma_union_absorb_subset (#a:eqtype) (l1 l2:lang a)
  : Lemma (requires (forall (w:seq a). mem w l2 ==> mem w l1))
          (ensures equiv (re_union l1 l2) l1)
  = ()

let lemma_re_union_star_epsilon (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_union (re_star l) (re_to_re empty)) (re_star l))
  = lemma_star_nil l;
    lemma_union_absorb_subset (re_star l) (re_to_re empty)

(* r | ~r == Sigma-star : complement absorption, Z3's `are_complements`
   branch of `mk_re_union0`. (Classical excluded middle, same style as
   `lemma_compl_compl` above.) *)
let lemma_union_compl_full (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_union l (re_compl l)) re_full)
  = ()

(* Not covered (mk_re_union0/mk_re_union): the ite-hoisting branches (pure
   term restructuring, no new semantic law), `try_collapse_re_union` /
   `mk_regex_union_normalize` (AC-normalization and syntactic subset
   detection via `is_subset`/`merge_regex_sets`, heuristic and
   combinatorial, out of scope). *)

(* ----------------------------------------------------------------------- *)
(* `mk_re_complement` (seq_rewriter.cpp:3880-3924).                        *)
(* ----------------------------------------------------------------------- *)

(* The dual De Morgan law, completing `lemma_union_inter_compl_demorgan`
   from `Z3RegexTheory.fst` (which only states the union/intersection
   direction). Z3: `mk_re_complement`'s "intersection" branch. *)
let lemma_inter_union_compl_demorgan (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_compl (re_inter l1 l2)) (re_union (re_compl l1) (re_compl l2)))
  = ()

let lemma_compl_empty (#a:eqtype) : Lemma (equiv (re_compl (re_empty #a)) re_full)
  = ()

let lemma_compl_full (#a:eqtype) : Lemma (equiv (re_compl (re_full #a)) re_empty)
  = ()

(* ~(epsilon) == Sigma-char+ : Z3's `mk_re_complement`'s "to_re(epsilon)"
   branch; this is exactly `lemma_plus_allchar_eq_nonempty` read
   right-to-left (equivalence is symmetric). *)
let lemma_compl_epsilon_is_plus_allchar (#a:eqtype)
  : Lemma (equiv (re_compl (re_to_re #a empty)) (re_plus re_allchar))
  = lemma_plus_allchar_eq_nonempty #a

(* Not covered (mk_re_complement): the `ite`-hoisting branch (term
   restructuring, not a new semantic law). *)

(* ----------------------------------------------------------------------- *)
(* `mk_re_inter0` / `mk_re_inter` (seq_rewriter.cpp:3924-3981).            *)
(* Dual of the `mk_re_union0`/`mk_re_union` section above. *)
(* ----------------------------------------------------------------------- *)

let lemma_inter_idem (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_inter l l) l)
  = ()

let lemma_inter_empty_l (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_inter (re_empty #a) l) re_empty)
  = ()

let lemma_inter_empty_r (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_inter l (re_empty #a)) re_empty)
  = ()

let lemma_inter_full_l (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_inter (re_full #a) l) l)
  = ()

let lemma_inter_full_r (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_inter l (re_full #a)) l)
  = ()

(* r & ~r == emptyset : complement absorption, Z3's `are_complements`
   branch of `mk_re_inter0`. *)
let lemma_inter_compl_empty (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_inter l (re_compl l)) re_empty)
  = ()

(* Not covered (mk_re_inter0/mk_re_inter): the ite-hoisting branches, and
   `try_collapse_re_inter`/`mk_regex_inter_normalize` (same combinatorial
   caveat as the union case above). *)

(* ----------------------------------------------------------------------- *)
(* `mk_re_diff` (seq_rewriter.cpp:3981-4010).                              *)
(* The fallback `a \ b = a & ~b` is exactly `lemma_diff_is_inter_compl` in *)
(* `Z3RegexTheory.fst` -- already proved, cited directly, no new lemma     *)
(* needed. *)
(* Not covered: the `range_predicate_to_regex`/`regex_to_range_predicate`  *)
(* fast path, which needs the `mk_re_range` element-ordering model (see   *)
(* below) and is deferred there. *)
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
(* `mk_re_xor0` / `mk_re_xor` (seq_rewriter.cpp:4010-4080).                *)
(* All branches are propositional unfoldings of `re_xor`'s symmetric-      *)
(* difference definition. *)
(* ----------------------------------------------------------------------- *)

let lemma_xor_self_empty (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_xor l l) re_empty)
  = ()

let lemma_xor_empty_l (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_xor (re_empty #a) l) l)
  = ()

let lemma_xor_empty_r (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_xor l (re_empty #a)) l)
  = ()

let lemma_xor_full_l (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_xor (re_full #a) l) (re_compl l))
  = ()

let lemma_xor_full_r (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_xor l (re_full #a)) (re_compl l))
  = ()

(* comp(a) XOR comp(b) == a XOR b. *)
let lemma_xor_compl_compl (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_xor (re_compl l1) (re_compl l2)) (re_xor l1 l2))
  = ()

(* comp(a) XOR b == comp(a XOR b). *)
let lemma_xor_compl_l (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_xor (re_compl l1) l2) (re_compl (re_xor l1 l2)))
  = ()

(* a XOR comp(b) == comp(a XOR b). *)
let lemma_xor_compl_r (#a:eqtype) (l1 l2:lang a)
  : Lemma (equiv (re_xor l1 (re_compl l2)) (re_compl (re_xor l1 l2)))
  = ()

(* Not covered (mk_re_xor0/mk_re_xor): the expression-id-based AC
   normalization (`a->get_id() > b->get_id()`), a term-ordering
   implementation detail with no language-level content. *)

(* ----------------------------------------------------------------------- *)
(* `mk_re_loop` (seq_rewriter.cpp:4080-4148) and `mk_re_power`             *)
(* (seq_rewriter.cpp:4148-4165). *)
(* ----------------------------------------------------------------------- *)

(* lo > hi : an empty repetition-count range accepts nothing. *)
let lemma_loop_empty_inverted (#a:eqtype) (l:lang a) (lo hi:nat)
  : Lemma (requires lo > hi) (ensures equiv (re_loop l lo hi) re_empty)
  = ()

(* (loop a 0 0) = "" : zero repetitions, any number of times, is epsilon.
   Immediate corollary of `lemma_loop_exact` (`re_pow l 0` unfolds
   definitionally to `re_to_re empty`). *)
let lemma_loop_0_0 (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_loop l 0 0) (re_to_re empty))
  = lemma_loop_exact l 0

(* (loop a 1 1) = a : exactly one repetition is just `a` itself. *)
let lemma_loop_1_1 (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_loop l 1 1) l)
  = lemma_loop_exact l 1;
    lemma_concat_unit_r l

(* (loop a 0 unbounded) = a* : Z3's `mk_re_loop` "np == 1 && lo2 == 0"
   branch (`re_loop_lo l 0` models the unbounded-upper-bound overload). *)
let lemma_loop_lo_zero_is_star (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_loop_lo l 0) (re_star l))
  = lemma_loop_lo_def l 0;
    lemma_concat_unit_l (re_star l)

(* mk_re_power(a, p) is literally defined as `loop(a, p, p)`, so its
   soundness is exactly `lemma_loop_exact` above; no separate theorem is
   needed. *)

(* Not covered (mk_re_loop): the nested-loop combination rules
   ("(loop (loop a lo) lo2) = (loop a lo*lo2)" and its bounded
   "(loop (loop a l l) h h) = (loop a l*h l*h)" variant) -- these need a
   `pow`-multiplication lemma (`equiv (re_pow l (m * n)) (re_pow (re_pow l m) n)`)
   which has not yet been formalized; and the `UINT_MAX` overflow-guard
   branches, which are pure machine-arithmetic side conditions with no
   language-level content. *)

(* ----------------------------------------------------------------------- *)
(* `mk_re_range` (seq_rewriter.cpp:4242-4319).                             *)
(* `Z3RegexTheory.fst`'s `re_range` is already parameterized by an        *)
(* abstract `in_range : a -> bool` predicate rather than committing to a   *)
(* concrete element order, so both of `mk_re_range`'s algebraic rewrites   *)
(* are stated directly against that predicate (no character-order theory  *)
(* is needed): an always-false predicate models an inverted range, and a   *)
(* predicate equivalent to `(= _ c)` models a singleton range. *)
(* ----------------------------------------------------------------------- *)

(* An inverted range (clo > chi, i.e. `in_range` is unsatisfiable) is
   empty. *)
let lemma_range_empty_of_unsat (#a:eqtype) (in_range:a -> bool)
  : Lemma (requires (forall (x:a). in_range x = false))
          (ensures equiv (re_range in_range) re_empty)
  = ()

(* A singleton range (clo == chi, i.e. `in_range` picks out exactly one
   element `c`) is the same language as the literal `to_re(unit c)`. *)
let lemma_range_singleton (#a:eqtype) (in_range:a -> bool) (c:a)
  : Lemma (requires (forall (x:a). (in_range x = true) <==> x == c))
          (ensures equiv (re_range in_range) (re_to_re (unit c)))
  = ()

(* Not covered (mk_re_range): reading concrete character bounds out of
   `zstring`/`str().is_unit`/`m_util.is_const_char` literal terms, and the
   `min_length`/`max_length` provable-emptiness side conditions for
   symbolic bounds -- both are term-inspection/arithmetic side conditions
   on Z3's concrete string/char representation, not language-level facts
   about `re_range` itself. *)

(* ----------------------------------------------------------------------- *)
(* `mk_re_concat` (seq_rewriter.cpp:3588-3813): the "easy algebraic"       *)
(* subset of its ~25 branches. *)
(* ----------------------------------------------------------------------- *)

(* Sigma-star . Sigma-star == Sigma-star. *)
let lemma_concat_full_full (#a:eqtype) : Lemma (equiv (re_concat (re_full #a) re_full) re_full)
  = let bwd (w:seq a) : Lemma (ensures mem w (re_concat re_full re_full)) =
      lemma_concat_empty_r w;
      intro_concat re_full re_full w w empty
    in
    Classical.forall_intro bwd

(* emptyset . b == emptyset, a . emptyset == emptyset : Z3's `mk_re_concat`
   `is_empty(a)` / `is_empty(b)` branches. *)
let lemma_concat_empty_lang_l (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_concat (re_empty #a) l) re_empty)
  = let fwd (w:seq a) : Lemma (requires mem w (re_concat (re_empty #a) l)) (ensures mem w re_empty) =
      elim_concat re_empty l w (mem w re_empty) (fun w1 w2 -> ())
    in
    Classical.forall_intro (Classical.move_requires fwd)

let lemma_concat_empty_lang_r (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_concat l (re_empty #a)) re_empty)
  = let fwd (w:seq a) : Lemma (requires mem w (re_concat l (re_empty #a))) (ensures mem w re_empty) =
      elim_concat l re_empty w (mem w re_empty) (fun w1 w2 -> ())
    in
    Classical.forall_intro (Classical.move_requires fwd)

(* epsilon . b == b, a . epsilon == a : Z3's `mk_re_concat`
   `is_epsilon(a)` / `is_epsilon(b)` branches -- exactly
   `lemma_concat_unit_l`/`lemma_concat_unit_r` from `Z3RegexTheory.fst`,
   already proved, cited directly (no new lemma needed). *)

(* (to_re s) . (to_re t) == to_re (s ++ t) : literal-string concatenation,
   `mk_re_concat`'s `is_to_re(a)&&is_to_re(b)` branch. *)
let lemma_concat_to_re (#a:eqtype) (s t:seq a)
  : Lemma (equiv (re_concat (re_to_re s) (re_to_re t)) (re_to_re (concat s t)))
  = let fwd (w:seq a) : Lemma (requires mem w (re_concat (re_to_re s) (re_to_re t)))
                              (ensures mem w (re_to_re (concat s t))) =
      elim_concat (re_to_re s) (re_to_re t) w (mem w (re_to_re (concat s t))) (fun w1 w2 -> ())
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_to_re (concat s t)))
                              (ensures mem w (re_concat (re_to_re s) (re_to_re t))) =
      intro_concat (re_to_re s) (re_to_re t) w s t
    in
    let proof (w:seq a) : Lemma (mem w (re_concat (re_to_re s) (re_to_re t)) <==> mem w (re_to_re (concat s t))) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* a* . a* == a* : Z3's `mk_re_concat` "is_star(a,a1) && is_star(b,b1) &&
   a1 == b1" branch. *)
let lemma_concat_star_star_self (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_concat (re_star l) (re_star l)) (re_star l))
  = let fwd (w:seq a) : Lemma (requires mem w (re_concat (re_star l) (re_star l)))
                              (ensures mem w (re_star l)) =
      elim_concat (re_star l) (re_star l) w (mem w (re_star l))
        (fun w1 w2 -> lemma_star_closed_concat l w1 w2)
    in
    let bwd (w:seq a) : Lemma (requires mem w (re_star l))
                              (ensures mem w (re_concat (re_star l) (re_star l))) =
      lemma_star_nil l;
      intro_concat (re_star l) (re_star l) w empty w
    in
    let proof (w:seq a) : Lemma (mem w (re_concat (re_star l) (re_star l)) <==> mem w (re_star l)) =
      Classical.move_requires fwd w;
      Classical.move_requires bwd w
    in
    Classical.forall_intro proof

(* a* . a == a . a* : Z3's `mk_re_concat` "is_star(a,a1) && a1 == b"
   branch (`result = mk_re_append(b, a)`, i.e. rotates `a*.a` to `a.a*`).
   Special case (n=1) of `lemma_star_pow_comm`. *)
let lemma_concat_star_self_comm (#a:eqtype) (l:lang a)
  : Lemma (equiv (re_concat (re_star l) l) (re_concat l (re_star l)))
  = lemma_star_pow_comm l 1;
    lemma_concat_unit_r l;
    lemma_concat_congr (re_star l) l (re_star l) (re_pow l 1);
    lemma_concat_congr (re_pow l 1) (re_star l) l (re_star l)

(* Not covered (mk_re_concat): the `rex::info`/`accepts_empty_word`/
   `starts_with_full_seq`/`ends_with_full_seq`/`all_inter_arms_end_with_full_seq`
   branches (depend on `rex::info`'s `nullable`/`min_length` analysis, not
   yet formalized here); the loop-addition combination rules
   (`(loop a lo1 hi1).(loop a lo2 hi2) = (loop a lo1+lo2 hi1+hi2)` and its
   one-sided variants) -- the "subset" direction follows from
   `lemma_pow_concat_intro` generalized to ranges, but the converse
   ("any n in the summed range splits as n1+n2 with n1,n2 in the
   respective sub-ranges") needs extra nat-arithmetic case splitting not
   yet written; the `ite`-hoisting branch; and the final flattening
   branch (`is_concat(a,a1,a2)` re-association, a normal-form bookkeeping
   step, not a new semantic law). *)
