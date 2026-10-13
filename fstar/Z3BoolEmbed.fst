(*
   Z3BoolEmbed.fst

   The Boolean-theory instance of `Z3ArrayEmbed.fst`'s "synthesize the
   rewritten side" pattern: for `not(not(x)) = x` (`Z3BoolRewriter.not_not`,
   matched by `Z3PatternMatchedProofChecker.fst`'s `match_not_not`),
   `apply_lemma_not_not t` recognizes a double-negation shape and
   returns the un-negated `x`.
*)
module Z3BoolEmbed
open Z3AstTheory
open Z3ValueTheory
open Z3InterpretedProofChecker
open Z3PatternMatchedProofChecker
open FStar.List.Tot

let apply_lemma_not_not (t:expr) : option expr =
  match t with
  | App f1 [App f2 [x]] ->
    if Some? f1.interp && Some?.v f1.interp = op_not &&
       Some? f2.interp && Some?.v f2.interp = op_not &&
       wf t && closed t && decls_ok t && no_quant t &&
       sort_eq (get_sort x) bool_s
    then Some x
    else None
  | _ -> None

let lemma_apply_lemma_not_not_sound (t:expr) (rho:env value)
  : Lemma (requires Some? (apply_lemma_not_not t))
          (ensures eval the_interpretation t rho ==
                   eval the_interpretation (Some?.v (apply_lemma_not_not t)) rho)
  = match t with
    | App f1 [App f2 [x]] ->
      lemma_eval_shape x rho;
      (match eval the_interpretation x rho with
       | VBool xv -> Z3BoolRewriter.not_not xv
       | _ -> ())
    | _ -> ()

let apply_lemmas (t:expr) : list expr =
  match apply_lemma_not_not t with Some s -> [s] | None -> []

let is_rewrite (t s:expr) : bool = apply_lemma_not_not t = Some s

let lemma_is_rewrite_sound (t s:expr) (rho:env value)
  : Lemma (requires is_rewrite t s)
          (ensures eval the_interpretation t rho == eval the_interpretation s rho)
  = lemma_apply_lemma_not_not_sound t rho
