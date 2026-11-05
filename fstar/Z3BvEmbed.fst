(*
   Z3BvEmbed.fst

   The bit-vector-theory instance of `Z3ArrayEmbed.fst`'s "synthesize
   the rewritten side" pattern: for `bvand(y,y) = y`
   (`Z3BvRewriter.lemma_bvand_self`, matched by
   `Z3PatternMatchedProofChecker.fst`'s `match_bvand_self`),
   `apply_lemma_bvand_self t` recognizes a self-`bvand` shape and
   returns the deduplicated `y`.
*)
module Z3BvEmbed
open Z3AstTheory
open Z3ValueTheory
open Z3InterpretedProofChecker
open Z3PatternMatchedProofChecker
open FStar.List.Tot

let apply_lemma_bvand_self (t:expr) : option expr =
  match t with
  | App f [y1; y2] ->
    if Some? f.interp && Some?.v f.interp = op_bvand && y1 = y2 &&
       wf t && closed t && decls_ok t && no_quant t &&
       sort_eq (get_sort y1) bv_s
    then Some y1
    else None
  | _ -> None

let lemma_apply_lemma_bvand_self_sound (t:expr) (rho:env value)
  : Lemma (requires Some? (apply_lemma_bvand_self t))
          (ensures eval the_interpretation t rho ==
                   eval the_interpretation (Some?.v (apply_lemma_bvand_self t)) rho)
  = match t with
    | App f [y1; y2] ->
      lemma_eval_shape y1 rho;
      (match eval the_interpretation y1 rho with
       | VBV yv -> Z3BvRewriter.lemma_bvand_self #32 yv
       | _ -> ())
    | _ -> ()

let apply_lemmas (t:expr) : list expr =
  match apply_lemma_bvand_self t with Some s -> [s] | None -> []

let is_rewrite (t s:expr) : bool = apply_lemma_bvand_self t = Some s

let lemma_is_rewrite_sound (t s:expr) (rho:env value)
  : Lemma (requires is_rewrite t s)
          (ensures eval the_interpretation t rho == eval the_interpretation s rho)
  = lemma_apply_lemma_bvand_self_sound t rho
