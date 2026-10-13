(*
   Z3CoreEmbed.fst

   The two matchers in `Z3PatternMatchedProofChecker.fst` that are not
   tied to a single theory: reflexivity (`s = s`, sound for *any*
   `expr` under *any* interpretation -- no theory lemma, no sort side
   condition) and `eq_symm` (`(= a b) = (= b a)`, sound via the
   generic `op_eq` operator's symmetry,
   `Z3InterpretedProofChecker.lemma_value_eq_sym_symmetric` -- again no
   per-theory lemma). These get their own "embed" file rather than
   living in one of the per-theory ones, since both apply uniformly
   across every sort this checker models.
*)
module Z3CoreEmbed
open Z3AstTheory
open Z3ValueTheory
open Z3InterpretedProofChecker
open Z3PatternMatchedProofChecker
open FStar.List.Tot

(* Reflexivity is trivial as a *matcher* (`t = t` always "fires"), but
   deliberately pointless as an `apply_lemma_x` in the `expr -> option
   expr` sense: it would just be `fun t -> Some t`, a rewrite that
   never changes anything. It is included here anyway, `None`-gated on
   nothing but well-formedness, purely for uniformity with the other
   `apply_lemma_x` signatures and so `apply_lemmas`/`is_rewrite` below
   see the full matcher set this file's sibling,
   `Z3PatternMatchedProofChecker.fst`, supports. *)
let apply_lemma_reflexivity (t:expr) : option expr =
  if wf t && closed t && decls_ok t && no_quant t then Some t else None

let lemma_apply_lemma_reflexivity_sound (t:expr) (rho:env value)
  : Lemma (requires Some? (apply_lemma_reflexivity t))
          (ensures eval the_interpretation t rho ==
                   eval the_interpretation (Some?.v (apply_lemma_reflexivity t)) rho)
  = ()

(* `(= a b) = (= b a)`: `apply_lemma_eq_symm t` recognizes an `op_eq`
   application and returns its argument-swapped twin. *)
let apply_lemma_eq_symm (t:expr) : option expr =
  match t with
  | App f [a; b] ->
    if Some? f.interp && Some?.v f.interp = op_eq &&
       wf t && closed t && decls_ok t && no_quant t &&
       sort_eq (get_sort a) (get_sort b)
    then Some (App f [b; a])
    else None
  | _ -> None

let lemma_apply_lemma_eq_symm_sound (t:expr) (rho:env value)
  : Lemma (requires Some? (apply_lemma_eq_symm t))
          (ensures eval the_interpretation t rho ==
                   eval the_interpretation (Some?.v (apply_lemma_eq_symm t)) rho)
  = match t with
    | App f [a; b] ->
      lemma_eval_shape a rho;
      lemma_eval_shape b rho;
      lemma_value_eq_sym_symmetric (eval the_interpretation a rho) (eval the_interpretation b rho)
    | _ -> ()

let apply_lemmas (t:expr) : list expr =
  (match apply_lemma_reflexivity t with Some s -> [s] | None -> []) @
  (match apply_lemma_eq_symm t with Some s -> [s] | None -> [])

let is_rewrite (t s:expr) : bool =
  apply_lemma_reflexivity t = Some s || apply_lemma_eq_symm t = Some s

let lemma_is_rewrite_sound (t s:expr) (rho:env value)
  : Lemma (requires is_rewrite t s)
          (ensures eval the_interpretation t rho == eval the_interpretation s rho)
  = if apply_lemma_reflexivity t = Some s then
      lemma_apply_lemma_reflexivity_sound t rho
    else
      lemma_apply_lemma_eq_symm_sound t rho
