(*
   Z3RegexMembership.fst

   Formalizes `(str.in_re s r)` (`OP_SEQ_IN_RE`, seq_decl_plugin.h:56)
   -- the one place a string and a regular expression meet as a
   constraint -- and certifies a representative set of the algebraic
   rewrite rules `seq_rewriter.cpp`'s `mk_str_in_regexp` (the
   `OP_SEQ_IN_RE` handler, seq_rewriter.cpp:3396-3527) applies,
   working at the `Z3RegexTheory.lang a` level (the same level
   `Z3RegexExprTheory.to_lang` denotes regex *expressions* into): each
   lemma below states, for the `lang a` combinator(s) `to_lang` maps a
   given `re_op` shape to, exactly the membership fact the
   corresponding `mk_str_in_regexp` branch relies on.

   `Z3RegexExprTheory.fst`'s own header explicitly scoped
   `OP_SEQ_IN_RE` out as "left for a higher-level theory of asserts" --
   this module is that higher-level theory, for the fragment of
   `mk_str_in_regexp` reachable without additionally modeling
   `str.len`/`str.<=` (lexicographic order) or `str.replace_all`. *)
module Z3RegexMembership

open Z3SeqTheory
open Z3RegexTheory
open Z3SeqRewrites
open Z3SeqDerive
module Classical = FStar.Classical

(* `str.in_re s r`'s own denotation is just language membership. Named
   for readability at call sites below. *)
let in_re (#a:eqtype) (w:seq a) (l:lang a) : prop = mem w l

(* ----------------------------------------------------------------- *)
(* Base cases -- seq_rewriter.cpp:3401-3408                            *)
(* ----------------------------------------------------------------- *)

(* (str.in_re e re.none) ==> false -- seq_rewriter.cpp:3401-3404. *)
let lemma_in_re_empty (#a:eqtype) (w:seq a)
  : Lemma (in_re w re_empty <==> False)
  = ()

(* (str.in_re e re.all) ==> true -- seq_rewriter.cpp:3405-3408. *)
let lemma_in_re_full (#a:eqtype) (w:seq a)
  : Lemma (in_re w re_full <==> True)
  = ()

(* ----------------------------------------------------------------- *)
(* lift_str_from_to_re -- seq_rewriter.cpp:3480-3483/3547-3556         *)
(* ----------------------------------------------------------------- *)

(* (str.in_re a (str.to_re s)) ==> (= a s) -- `lift_str_from_to_re`
   (seq_rewriter.cpp:3547-3556), invoked from `mk_str_in_regexp` at
   seq_rewriter.cpp:3480-3483. *)
let lemma_in_re_to_re (#a:eqtype) (w s:seq a)
  : Lemma (in_re w (re_to_re s) <==> (w == s))
  = ()

(* ----------------------------------------------------------------- *)
(* (str.in_re "" b) ==> nullable(b) -- seq_rewriter.cpp:3514-3519       *)
(* ----------------------------------------------------------------- *)

(* The empty string is in `l` iff `l` is nullable -- this is exactly
   `Z3SeqDerive.is_nullable`'s definition, restated here under the
   `in_re`/`mk_str_in_regexp` naming for direct traceability to the
   `str().is_empty(a) -> result = is_nullable(b)` branch. *)
let lemma_in_re_empty_string (#a:eqtype) (l:lang a)
  : Lemma (in_re empty l <==> is_nullable l)
  = ()

(* ----------------------------------------------------------------- *)
(* Ground string membership via the derivative chase                  *)
(* seq_rewriter.cpp:3443-3463 ("Just check membership")                *)
(* ----------------------------------------------------------------- *)

(* The soundness statement for `mk_str_in_regexp`'s ground-string loop
   `r := mk_derivative(ch, r); ... switch (get_info(r).nullable)`: a
   concrete word `w` is in `l` iff chasing `l`'s derivative along every
   character of `w` lands on a nullable language. This is
   `Z3SeqDerive.lemma_derivs_correct`, restated here under the
   `in_re` name for direct traceability. *)
let lemma_in_re_ground (#a:eqtype) (w:seq a) (l:lang a)
  : Lemma (in_re w l <==> is_nullable (derivs w l))
  = lemma_derivs_correct w l

(* ----------------------------------------------------------------- *)
(* opt / union-with-epsilon ITE rewrite -- seq_rewriter.cpp:3505-3512   *)
(* ----------------------------------------------------------------- *)

(* The empty word is exactly the length-0 word -- the fact that lets
   `mk_str_in_regexp` test nullability of the `b1?`/`eps|b1`/`b1|eps`
   branch via `str.len a = 0` rather than `a = ""` directly. *)
let lemma_len_zero_iff_empty (#a:eqtype) (w:seq a)
  : Lemma (len w = 0 <==> w == empty)
  = match w with
    | [] -> ()
    | _ :: _ -> ()

(* (str.in_re a b1?) <==> (len(a) = 0) or (str.in_re a b1)
   -- seq_rewriter.cpp:3505-3512's `result = ite(is_empty, true, in_b1)`
   (`b` one of `b1?`, `eps|b1`, `b1|eps`; all three denote `re_opt`). *)
let lemma_in_re_opt (#a:eqtype) (w:seq a) (l:lang a)
  : Lemma (in_re w (re_opt l) <==> (len w = 0 \/ in_re w l))
  = lemma_len_zero_iff_empty w

(* ----------------------------------------------------------------- *)
(* concat-with-full_seq prefix/suffix rewrites -- seq_rewriter.cpp:3486-3493 *)
(* ----------------------------------------------------------------- *)

(* (str.in_re a ((str.to_re e) ++ re.all)) <==> (str.prefixof e a)
   -- seq_rewriter.cpp:3486-3489 (`result = str().mk_prefix(e, a)`). *)
let lemma_in_re_prefix (#a:eqtype) (e w:seq a)
  : Lemma (in_re w (re_concat (re_to_re e) re_full) <==> is_prefix e w == true)
  = let fwd ()
      : Lemma (requires in_re w (re_concat (re_to_re e) re_full)) (ensures is_prefix e w == true)
      = elim_concat (re_to_re e) re_full w (is_prefix e w == true) (fun w1 w2 ->
          lemma_prefix_concat_intro e w2)
    in
    let bwd ()
      : Lemma (requires is_prefix e w == true) (ensures in_re w (re_concat (re_to_re e) re_full))
      = lemma_prefix_extract_reconstruct e w;
        intro_concat (re_to_re e) re_full w e (drop w (len e))
    in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

(* (str.in_re a (re.all ++ (str.to_re e))) <==> (str.suffixof e a)
   -- seq_rewriter.cpp:3490-3493 (`result = str().mk_suffix(e, a)`). *)
let lemma_in_re_suffix (#a:eqtype) (e w:seq a)
  : Lemma (in_re w (re_concat re_full (re_to_re e)) <==> is_suffix e w == true)
  = let fwd ()
      : Lemma (requires in_re w (re_concat re_full (re_to_re e))) (ensures is_suffix e w == true)
      = elim_concat re_full (re_to_re e) w (is_suffix e w == true) (fun w1 w2 ->
          lemma_suffix_concat_intro w1 e)
    in
    let bwd ()
      : Lemma (requires is_suffix e w == true) (ensures in_re w (re_concat re_full (re_to_re e)))
      = let rev_e = reverse e in
        let rev_w = reverse w in
        lemma_prefix_extract_reconstruct rev_e rev_w;
        (* rev_w == concat rev_e d, where d := drop rev_w (len rev_e) *)
        let d = drop rev_w (len rev_e) in
        lemma_reverse_concat rev_e d;
        (* reverse rev_w == concat (reverse d) (reverse rev_e) *)
        lemma_reverse_reverse w;
        lemma_reverse_reverse e;
        (* so w == concat (reverse d) e *)
        intro_concat re_full (re_to_re e) w (reverse d) e
    in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()
