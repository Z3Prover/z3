(*
   Z3SeqDerive.fst

   Formalizes the mathematical content of src/ast/rewriter/seq_derive.cpp:
   symbolic (Brzozowski) derivatives of regular languages, and the
   membership-via-derivative-chase theorem that `seq_rewriter.cpp`'s
   `mk_str_in_regexp` relies on for ground strings.

   `seq_derive.cpp`'s `derive::derive_core` computes, for a regex `r`
   and a (possibly symbolic, de-Bruijn-var-0) character `ele`, an
   ITE-tree representation of the derivative -- evaluating the tree at
   a concrete character `a` yields the classical Brzozowski derivative
   `delta_a(r)`. This module works purely at the denotational `lang a`
   level (`Z3RegexTheory.fst`): `deriv c l` is *defined* as the
   residual language `{ w | c::w in L(l) }`, and the lemmas below show
   this semantic operator satisfies exactly the recursive equations
   `derive_core` dispatches on (one lemma per `if re().is_X(r, ...)`
   branch, cited by `seq_derive.cpp` line number). This certifies the
   *mathematical content* of `derive_core`'s case split is sound; the
   ITE-tree hoisting, path/interval pruning, cofactor enumeration, and
   memoization machinery built on top of it (the bulk of
   `seq_derive.cpp`'s code) is a performance/representation layer and
   is not modeled here -- see REGEX_REPORT.md's addendum for the full
   covered/not-covered breakdown.
*)
module Z3SeqDerive

open Z3SeqTheory
open Z3RegexTheory
module Classical = FStar.Classical

(* ----------------------------------------------------------------- *)
(* The semantic derivative and nullability                            *)
(* ----------------------------------------------------------------- *)

(* The (left) derivative/residual of `l` with respect to `c`: the
   words that, prefixed by `c`, are in `l`. This is the ground-truth
   specification `derive_core` computes a syntactic representation
   of. *)
let deriv (#a:eqtype) (c:a) (l:lang a) : lang a = fun w -> mem (c :: w) l

(* `r` accepts the empty word -- `seq_derive.cpp`'s `is_nullable`,
   restricted to its Boolean (non-symbolic) outcome; this is also
   exactly `Z3RegexInfo.fst`'s `info.nullable == LTrue` condition. *)
let is_nullable (#a:eqtype) (l:lang a) : prop = mem empty l

(* Iterated derivative along a whole word: `derivs w l` is the
   language reached after consuming `w` one character at a time via
   `deriv`, mirroring `mk_str_in_regexp`'s loop `r := mk_derivative(ch, r)`
   over each character of a ground string (seq_rewriter.cpp, the
   "Just check membership" block). *)
let rec derivs (#a:eqtype) (w:seq a) (l:lang a) : Tot (lang a) (decreases w) =
  match w with
  | [] -> l
  | c :: rest -> derivs rest (deriv c l)

(* The key correctness theorem for the ground-string `str.in_re`
   rewrite: `w` is in `l` iff the language reached by chasing `l`'s
   derivative along every character of `w` is nullable. This is
   exactly what justifies replacing `(str.in_re w b)` for a concrete
   `w` by `true`/`false` after iterating `mk_derivative` and consulting
   `re().get_info(r).nullable` (seq_rewriter.cpp's `mk_str_in_regexp`). *)
let rec lemma_derivs_correct (#a:eqtype) (w:seq a) (l:lang a)
  : Lemma (ensures (mem w l <==> is_nullable (derivs w l))) (decreases w)
  = match w with
    | [] -> ()
    | c :: rest -> lemma_derivs_correct rest (deriv c l)

(* ----------------------------------------------------------------- *)
(* Base cases (seq_derive.cpp lines 176-198)                          *)
(* ----------------------------------------------------------------- *)

(* delta(empty) = empty -- seq_derive.cpp:177-178. *)
let lemma_deriv_empty (#a:eqtype) (c:a)
  : Lemma (equiv (deriv c re_empty) re_empty)
  = ()

(* delta(epsilon) = empty, where epsilon = (str.to_re "") -- seq_derive.cpp:177-178. *)
let lemma_deriv_epsilon (#a:eqtype) (c:a)
  : Lemma (equiv (deriv c (re_to_re empty)) re_empty)
  = ()

(* delta(Sigma-star) = Sigma-star -- seq_derive.cpp:181-182. *)
let lemma_deriv_full (#a:eqtype) (c:a)
  : Lemma (equiv (deriv c re_full) re_full)
  = ()

(* delta(.) = epsilon (full-char accepts exactly one, arbitrary, character)
   -- seq_derive.cpp:185-186. *)
let lemma_deriv_allchar (#a:eqtype) (c:a)
  : Lemma (equiv (deriv c re_allchar) (re_to_re empty))
  = ()

(* delta(re.of_pred p) = if p(c) then epsilon else empty -- seq_derive.cpp:197-198
   (`re.range` is also an `of_pred` instance, via `Z3RegexExprTheory.re_range`). *)
let lemma_deriv_of_pred (#a:eqtype) (p:a -> bool) (c:a)
  : Lemma (equiv (deriv c (re_of_pred p))
                 (if p c then re_to_re empty else re_empty))
  = ()

(* delta(str.to_re s) = if s = c::s' then (str.to_re s') else empty
   -- seq_derive.cpp:189-190/`derive_to_re`: a literal word's derivative
   peels its head character if it matches, otherwise rejects. *)
let lemma_deriv_to_re (#a:eqtype) (s:seq a) (c:a)
  : Lemma (equiv (deriv c (re_to_re s))
                 (match s with
                  | c' :: s' -> if c' = c then re_to_re s' else re_empty
                  | [] -> re_empty))
  = ()

(* ----------------------------------------------------------------- *)
(* Boolean combinators (seq_derive.cpp lines 228-267, 318-324)        *)
(* ----------------------------------------------------------------- *)

(* delta(r1 | r2) = delta(r1) | delta(r2) -- seq_derive.cpp:228-233. *)
let lemma_deriv_union (#a:eqtype) (l1 l2:lang a) (c:a)
  : Lemma (equiv (deriv c (re_union l1 l2)) (re_union (deriv c l1) (deriv c l2)))
  = ()

(* delta(r1 xor r2) = delta(r1) xor delta(r2) -- seq_derive.cpp:235-240. *)
let lemma_deriv_xor (#a:eqtype) (l1 l2:lang a) (c:a)
  : Lemma (equiv (deriv c (re_xor l1 l2)) (re_xor (deriv c l1) (deriv c l2)))
  = ()

(* delta(r1 & r2) = delta(r1) & delta(r2) -- seq_derive.cpp:242-247. *)
let lemma_deriv_inter (#a:eqtype) (l1 l2:lang a) (c:a)
  : Lemma (equiv (deriv c (re_inter l1 l2)) (re_inter (deriv c l1) (deriv c l2)))
  = ()

(* delta(~r1) = ~delta(r1) -- seq_derive.cpp:262-266. *)
let lemma_deriv_complement (#a:eqtype) (l:lang a) (c:a)
  : Lemma (equiv (deriv c (re_compl l)) (re_compl (deriv c l)))
  = ()

(* delta(r1 \ r2) = delta(r1) & ~delta(r2) -- seq_derive.cpp:318-324
   (`re_diff` is itself defined as `re_inter l1 (re_compl l2)`, so this
   is immediate from `lemma_deriv_inter`/`lemma_deriv_complement`, but
   is stated directly since `mk_str_in_regexp`/`derive_core` treat
   `OP_RE_DIFF` as its own case rather than expanding it first). *)
let lemma_deriv_diff (#a:eqtype) (l1 l2:lang a) (c:a)
  : Lemma (equiv (deriv c (re_diff l1 l2)) (re_inter (deriv c l1) (re_compl (deriv c l2))))
  = ()

(* ----------------------------------------------------------------- *)
(* Concatenation (seq_derive.cpp lines 201-224)                       *)
(* ----------------------------------------------------------------- *)

(* A language gated by a side condition `p`: accepts exactly `l`'s
   words when `p` holds, nothing otherwise. Used to state the
   three-way (true/false/symbolic) `is_nullable` branch of
   `derive_core`'s concat case (seq_derive.cpp:213-224) as a single
   equation, uniformly over whether `p` happens to be decided. *)
let guarded (#a:eqtype) (p:prop) (l:lang a) : lang a = fun w -> p /\ mem w l

(* delta(r1 . r2) = delta(r1).r2 | (guarded (nullable r1) delta(r2))
   -- seq_derive.cpp:201-224: when `is_nullable(r1)` is concretely
   true/false this reduces to the `mk_union(d1_r2, derive_rec(r2))` /
   plain `d1_r2` branches; the `mk_ite(nullable_r1, d2, nothing())`
   branch (nullable_r1 symbolic) is exactly `guarded`. *)
let lemma_deriv_concat (#a:eqtype) (l1 l2:lang a) (c:a) (w:seq a)
  : Lemma (mem w (deriv c (re_concat l1 l2)) <==>
           (mem w (re_concat (deriv c l1) l2) \/ (is_nullable l1 /\ mem w (deriv c l2))))
  = let fwd ()
      : Lemma (requires mem w (deriv c (re_concat l1 l2)))
              (ensures mem w (re_concat (deriv c l1) l2) \/ (is_nullable l1 /\ mem w (deriv c l2)))
      = elim_concat l1 l2 (c :: w)
          (mem w (re_concat (deriv c l1) l2) \/ (is_nullable l1 /\ mem w (deriv c l2)))
          (fun w1 w2 ->
            match w1 with
            | c1 :: w1' ->
              (* c::w = w1 . w2 with w1 nonempty: c = c1, w = w1' . w2 *)
              intro_concat (deriv c l1) l2 w w1' w2
            | [] ->
              (* w1 = [], so w2 = c::w and l1 accepts the empty word *)
              ())
    in
    let bwd ()
      : Lemma (requires mem w (re_concat (deriv c l1) l2) \/ (is_nullable l1 /\ mem w (deriv c l2)))
              (ensures mem w (deriv c (re_concat l1 l2)))
      = Classical.or_elim
          #(mem w (re_concat (deriv c l1) l2))
          #(is_nullable l1 /\ mem w (deriv c l2))
          #(fun _ -> mem w (deriv c (re_concat l1 l2)))
          (fun _ ->
            elim_concat (deriv c l1) l2 w (mem w (deriv c (re_concat l1 l2))) (fun w1 w2 ->
              intro_concat l1 l2 (c :: w) (c :: w1) w2))
          (fun _ -> intro_concat l1 l2 (c :: w) [] (c :: w))
    in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

(* ----------------------------------------------------------------- *)
(* Star / plus / opt (seq_derive.cpp lines 268-284)                   *)
(* ----------------------------------------------------------------- *)

(* Helper: unwinding `re_pow l n` one repetition at a time, splitting
   off the leading repetition that actually consumes `c` (earlier
   repetitions, if any, must have matched the empty word). This is
   the structural induction underlying the star/plus derivative
   equation -- `re_star l`'s own existential-over-`n` definition is
   not amenable to a single `elim_concat` unfold the way `re_concat`
   is, since `re_star l` is not *definitionally* a concatenation. *)
let rec lemma_deriv_pow_star (#a:eqtype) (l:lang a) (c:a) (n:nat) (w:seq a)
  : Lemma (requires mem (c :: w) (re_pow l n))
          (ensures mem w (re_concat (deriv c l) (re_star l)))
          (decreases n)
  = if n = 0 then ()
    else
      elim_concat l (re_pow l (n - 1)) (c :: w)
        (mem w (re_concat (deriv c l) (re_star l))) (fun w1 w2 ->
          match w1 with
          | c1 :: w1' ->
            Classical.exists_intro (fun (m:nat) -> mem w2 (re_pow l m)) (n - 1);
            intro_concat (deriv c l) (re_star l) w w1' w2
          | [] -> lemma_deriv_pow_star l c (n - 1) w)

(* delta(r1-star) = delta(r1) . r1-star -- seq_derive.cpp:268-273. *)
let lemma_deriv_star (#a:eqtype) (l:lang a) (c:a)
  : Lemma (equiv (deriv c (re_star l)) (re_concat (deriv c l) (re_star l)))
  = let proof (w:seq a)
      : Lemma (mem w (deriv c (re_star l)) <==> mem w (re_concat (deriv c l) (re_star l)))
      = let fwd ()
          : Lemma (requires mem w (deriv c (re_star l))) (ensures mem w (re_concat (deriv c l) (re_star l)))
          = Classical.exists_elim (mem w (re_concat (deriv c l) (re_star l)))
              #nat #(fun n -> mem (c :: w) (re_pow l n)) ()
              (fun n -> lemma_deriv_pow_star l c n w)
        in
        let bwd ()
          : Lemma (requires mem w (re_concat (deriv c l) (re_star l))) (ensures mem w (deriv c (re_star l)))
          = elim_concat (deriv c l) (re_star l) w (mem w (deriv c (re_star l))) (fun w1 w2 ->
              Classical.exists_elim (mem w (deriv c (re_star l))) #nat #(fun m -> mem w2 (re_pow l m)) ()
                (fun m ->
                  intro_concat l (re_pow l m) (c :: w) (c :: w1) w2;
                  Classical.exists_intro (fun (k:nat) -> mem (c :: w) (re_pow l k)) (m + 1)))
        in
        Classical.move_requires fwd ();
        Classical.move_requires bwd ()
    in
    Classical.forall_intro proof

(* delta(r1+) = delta(r1) . r1-star -- seq_derive.cpp:275-280 (identical
   formula to star's, since `r1+ == r1 . r1-star`: expanding via
   `lemma_deriv_concat` gives an extra `(is_nullable l /\ mem w (deriv
   c (re_star l)))` disjunct, but `lemma_deriv_star` shows that disjunct
   is already subsumed by the first one, so it collapses to exactly
   the star formula). *)
let lemma_deriv_plus (#a:eqtype) (l:lang a) (c:a)
  : Lemma (equiv (deriv c (re_plus l)) (re_concat (deriv c l) (re_star l)))
  = lemma_plus_is_concat_star l;
    let proof (w:seq a) : Lemma (mem w (deriv c (re_plus l)) <==> mem w (re_concat (deriv c l) (re_star l))) =
      lemma_deriv_concat l (re_star l) c w;
      lemma_deriv_star l c
    in
    Classical.forall_intro proof

(* delta(r1?) = delta(r1) -- seq_derive.cpp:282-284 (r1? == epsilon | r1,
   and delta(epsilon) = empty, so delta(r1?) = empty | delta(r1) = delta(r1)). *)
let lemma_deriv_opt (#a:eqtype) (l:lang a) (c:a)
  : Lemma (equiv (deriv c (re_opt l)) (deriv c l))
  = ()
