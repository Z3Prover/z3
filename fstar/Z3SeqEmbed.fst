(*
   Z3SeqEmbed.fst

   The sequence-theory instance of the "synthesize the rewritten side"
   pattern described in `Z3ArrayEmbed.fst`'s module docstring: for
   `(a++b)++c = a++(b++c)` (`Z3SeqRewrites.lemma_concat_assoc`, matched
   by `Z3PatternMatchedProofChecker.fst`'s `match_concat_assoc`),
   `apply_lemma_concat_assoc t` recognizes a left-associated `((a++b)++c)`
   shape and returns the right-associated `(a++(b++c))` the lemma
   proves it equal to.
*)
module Z3SeqEmbed
open Z3AstTheory
open Z3ValueTheory
open Z3InterpretedProofChecker
open Z3PatternMatchedProofChecker
open FStar.List.Tot

let apply_lemma_concat_assoc (t:expr) : option expr =
  match t with
  | App f1 [App f2 [a; b]; c] ->
    if Some? f1.interp && Some?.v f1.interp = op_concat &&
       Some? f2.interp && Some?.v f2.interp = op_concat &&
       wf t && closed t && decls_ok t && no_quant t &&
       sort_eq (get_sort a) seq_s && sort_eq (get_sort b) seq_s && sort_eq (get_sort c) seq_s
    then Some (App f1 [a; App f2 [b; c]])
    else None
  | _ -> None

#push-options "--z3rlimit 50"
let lemma_apply_lemma_concat_assoc_sound (t:expr) (rho:env value)
  : Lemma (requires Some? (apply_lemma_concat_assoc t))
          (ensures eval the_interpretation t rho ==
                   eval the_interpretation (Some?.v (apply_lemma_concat_assoc t)) rho)
  = match t with
    | App f1 [App f2 [a; b]; c] ->
      lemma_eval_shape a rho;
      lemma_eval_shape b rho;
      lemma_eval_shape c rho;
      (match eval the_interpretation a rho, eval the_interpretation b rho, eval the_interpretation c rho with
       | VSeq av, VSeq bv, VSeq cv -> Z3SeqRewrites.lemma_concat_assoc av bv cv
       | _, _, _ -> ())
    | _ -> ()
#pop-options

let apply_lemmas (t:expr) : list expr =
  match apply_lemma_concat_assoc t with Some s -> [s] | None -> []

let is_rewrite (t s:expr) : bool = apply_lemma_concat_assoc t = Some s

let lemma_is_rewrite_sound (t s:expr) (rho:env value)
  : Lemma (requires is_rewrite t s)
          (ensures eval the_interpretation t rho == eval the_interpretation s rho)
  = lemma_apply_lemma_concat_assoc_sound t rho
