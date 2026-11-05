(*
   Z3AstTotEval.fst

   An executable (`Tot`) evaluator for the expression language of
   `Z3AstTheory`, for development code outside the checker that computes
   with the values of expressions.

   `Z3AstTheory.interpretation` and `Z3AstTheory.eval` are ghost (`GTot`),
   so that a model may decide classical propositions, such as the truth
   of `forall`/`exists` over an infinite domain or the identity of two
   array values. Ghost results cannot flow into executable code. The
   regular-expression track (`Z3RegexExprTheory`, `Z3RegexInfo`'s
   `compute_info`, the formalization of Z3's `get_info`) evaluates leaf
   sequences and branch conditions as part of its computation, so it uses
   the `Tot` record and evaluator below, `tot_interpretation` and `teval`.
   They are the old `Tot` record and `eval`, unchanged except for the
   names. `teval_bool` is the `Tot` copy of `Z3BasicExprTheory.eval_bool`.

   The two semantics agree only where no quantifier is evaluated: a
   quantifier field written for a `Tot` body cannot be given a ghost body
   (a ghost interpretation evaluates its quantifier bodies with `GTot`
   functions), so there is no general translation of a `Tot` record into
   a ghost one. `lift i q` uses the `Tot` application fields of `i` and an
   arbitrary ghost quantifier field `q`. `lemma_teval_lift` and
   `lemma_teval_bool_lift` prove that `teval`/`teval_bool` agree with
   `eval`/`eval_bool` of `lift i q`, for every `q`, on quantifier-free
   expressions only. Nothing here is claimed for expressions with binders.

   This module is not part of the checker (`fstar/tools/checker_modules.json`).
*)
module Z3AstTotEval

open Z3AstTheory
module B = Z3BasicExprTheory

noeq type tot_interpretation (value:Type) = {
  t_app      : f:func_decl{Some? f.interp} -> list value -> value;
  t_uninterp : f:func_decl{is_uninterp_decl f} -> list value -> value;
  t_quant    : quantifier_kind -> bound_sorts:list sort -> body_sem:(list value -> value) -> value;
}

let rec teval (#value:Type) (i:tot_interpretation value) (e:expr) (rho:env value) : Tot value (decreases e) =
  match e with
  | Var idx _ -> rho idx
  | App f args ->
    let vs = teval_args i args rho in
    if Some? f.interp then i.t_app f vs else i.t_uninterp f vs
  | Quantifier qk bound_sorts _ body ->
    i.t_quant qk bound_sorts (fun vs -> teval i body (shift vs rho))

and teval_args (#value:Type) (i:tot_interpretation value) (args:list expr) (rho:env value)
  : Tot (list value) (decreases args) =
  match args with
  | [] -> []
  | a :: args' -> teval i a rho :: teval_args i args' rho

(* The executable copy of `Z3BasicExprTheory.eval_bool`. *)
let rec teval_bool (#value:eqtype) (i:tot_interpretation value) (to_bool:value -> bool) (e:expr) (rho:env value)
  : Tot bool (decreases e)
  = match e with
    | Var _ _ -> to_bool (teval i e rho)
    | Quantifier _ _ _ _ -> to_bool (teval i e rho)
    | App f args ->
      if B.is_basic_op f B.Op_true then true
      else if B.is_basic_op f B.Op_false then false
      else if B.is_basic_op f B.Op_not then
        (match args with
         | [a] -> not (teval_bool i to_bool a rho)
         | _ -> to_bool (teval i e rho))
      else if B.is_basic_op f B.Op_and then teval_and i to_bool args rho
      else if B.is_basic_op f B.Op_or then teval_or i to_bool args rho
      else if B.is_basic_op f B.Op_implies then
        (match args with
         | [a; b] -> (not (teval_bool i to_bool a rho)) || teval_bool i to_bool b rho
         | _ -> to_bool (teval i e rho))
      else if B.is_basic_op f B.Op_xor then
        (match args with
         | [a; b] -> teval_bool i to_bool a rho <> teval_bool i to_bool b rho
         | _ -> to_bool (teval i e rho))
      else if B.is_basic_op f B.Op_eq then
        (match args with
         | [a; b] -> teval i a rho = teval i b rho
         | _ -> to_bool (teval i e rho))
      else if B.is_basic_op f B.Op_distinct then B.all_distinct (teval_args i args rho)
      else if B.is_basic_op f B.Op_ite then
        (match args with
         | [c; t; fe] -> if teval_bool i to_bool c rho then teval_bool i to_bool t rho else teval_bool i to_bool fe rho
         | _ -> to_bool (teval i e rho))
      else to_bool (teval i e rho)

and teval_and (#value:eqtype) (i:tot_interpretation value) (to_bool:value -> bool) (args:list expr) (rho:env value)
  : Tot bool (decreases args)
  = match args with
    | [] -> true
    | a :: rest -> teval_bool i to_bool a rho && teval_and i to_bool rest rho

and teval_or (#value:eqtype) (i:tot_interpretation value) (to_bool:value -> bool) (args:list expr) (rho:env value)
  : Tot bool (decreases args)
  = match args with
    | [] -> false
    | a :: rest -> teval_bool i to_bool a rho || teval_or i to_bool rest rho

(* --- Agreement with the ghost semantics, without binders --------------- *)

let rec quantifier_free (e:expr) : Tot bool (decreases e) =
  match e with
  | Var _ _ -> true
  | App _ args -> quantifier_free_args args
  | Quantifier _ _ _ _ -> false

and quantifier_free_args (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> quantifier_free a && quantifier_free_args rest

let lift (#value:Type) (i:tot_interpretation value)
         (q:quantifier_kind -> list sort -> (list value -> GTot value) -> GTot value)
  : interpretation value =
  { interp_app = i.t_app; uninterp_app = i.t_uninterp; interp_quant = q }

let rec lemma_teval_lift (#value:Type) (i:tot_interpretation value)
    (q:quantifier_kind -> list sort -> (list value -> GTot value) -> GTot value) (e:expr) (rho:env value)
  : Lemma (requires quantifier_free e) (ensures teval i e rho == eval (lift i q) e rho) (decreases e)
  = match e with
    | Var _ _ -> ()
    | App _ args -> lemma_teval_lift_args i q args rho

and lemma_teval_lift_args (#value:Type) (i:tot_interpretation value)
    (q:quantifier_kind -> list sort -> (list value -> GTot value) -> GTot value) (args:list expr) (rho:env value)
  : Lemma (requires quantifier_free_args args) (ensures teval_args i args rho == eval_args (lift i q) args rho)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest -> lemma_teval_lift i q a rho; lemma_teval_lift_args i q rest rho

let rec lemma_teval_bool_lift (#value:eqtype) (i:tot_interpretation value)
    (q:quantifier_kind -> list sort -> (list value -> GTot value) -> GTot value)
    (to_bool:value -> bool) (e:expr) (rho:env value)
  : Lemma (requires quantifier_free e)
          (ensures teval_bool i to_bool e rho == B.eval_bool (lift i q) to_bool e rho)
          (decreases e)
  = lemma_teval_lift i q e rho;
    match e with
    | Var _ _ -> ()
    | App f args ->
      lemma_teval_lift_args i q args rho;
      (match args with
       | [a] -> lemma_teval_bool_lift i q to_bool a rho
       | [a; b] ->
         lemma_teval_bool_lift i q to_bool a rho;
         lemma_teval_bool_lift i q to_bool b rho;
         lemma_teval_lift i q a rho;
         lemma_teval_lift i q b rho
       | [c; t; fe] ->
         lemma_teval_bool_lift i q to_bool c rho;
         lemma_teval_bool_lift i q to_bool t rho;
         lemma_teval_bool_lift i q to_bool fe rho
       | _ -> ());
      lemma_teval_and_lift i q to_bool args rho;
      lemma_teval_or_lift i q to_bool args rho

and lemma_teval_and_lift (#value:eqtype) (i:tot_interpretation value)
    (q:quantifier_kind -> list sort -> (list value -> GTot value) -> GTot value)
    (to_bool:value -> bool) (args:list expr) (rho:env value)
  : Lemma (requires quantifier_free_args args)
          (ensures teval_and i to_bool args rho == B.eval_and (lift i q) to_bool args rho)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest -> lemma_teval_bool_lift i q to_bool a rho; lemma_teval_and_lift i q to_bool rest rho

and lemma_teval_or_lift (#value:eqtype) (i:tot_interpretation value)
    (q:quantifier_kind -> list sort -> (list value -> GTot value) -> GTot value)
    (to_bool:value -> bool) (args:list expr) (rho:env value)
  : Lemma (requires quantifier_free_args args)
          (ensures teval_or i to_bool args rho == B.eval_or (lift i q) to_bool args rho)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest -> lemma_teval_bool_lift i q to_bool a rho; lemma_teval_or_lift i q to_bool rest rho
