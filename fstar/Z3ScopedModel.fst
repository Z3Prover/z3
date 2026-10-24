module Z3ScopedModel

open Z3AstTheory
open Z3ValueTheory
module D = Z3Definitions
module R = Z3ResolutionProofTheory
module L = FStar.List.Tot

let int_sort : sort = BaseSort "Int"

(* Other sorts retain their theory-specific contracts. *)
let scalar_typed (s:sort) (v:value) : bool =
  if s = bool_sort then VBool? v else if s = int_sort then VInt? v else true

let rec arguments_typed (ss:list sort) (vs:list value) : Tot bool (decreases ss) =
  match ss, vs with
  | [], [] -> true
  | s :: rest, v :: tail -> scalar_typed s v && arguments_typed rest tail
  | _, _ -> false

let environment_typed (scope:list sort) (rho:env value) : prop =
  forall (n:nat). n < L.length scope ==> scalar_typed (L.index scope n) (rho n)

let model (i:interpretation value) : prop =
  forall (scope:list sort) (e:expr) (rho:env value).
    D.scoped scope e /\ environment_typed scope rho ==>
      scalar_typed (get_sort e) (eval i e rho)

let literal_model (i:interpretation value) : prop =
  forall (rho:env value).
    eval i R.true_expr rho == VBool true /\ eval i R.false_expr rho == VBool false

let reflexive_equality (i:interpretation value) : prop =
  forall (s:sort) (v:value). i.interp_app (R.eq_decl s) [v; v] == VBool true

let lemma_legacy_reflexivity (i:interpretation value)
  : Lemma (requires R.eq_sound i) (ensures reflexive_equality i)
  = let aux (s:sort) (v:value)
      : Lemma (i.interp_app (R.eq_decl s) [v; v] == VBool true)
      = let a = Var 0 s in
        assert (eval i (R.mk_eq_expr a a) (fun _ -> v) == VBool true) in
    FStar.Classical.forall_intro_2 aux

let application_model (i:interpretation value) : prop =
  (forall (f:func_decl{Some? f.interp}) (vs:list value).
    arguments_typed f.domain vs ==> scalar_typed f.range (i.interp_app f vs)) /\
  (forall (f:func_decl{is_uninterp_decl f}) (vs:list value).
    arguments_typed f.domain vs ==> scalar_typed f.range (i.uninterp_app f vs)) /\
  (forall (k:quantifier_kind) (bs:list sort) (body:list value -> value).
    (k = Forall_k \/ k = Exists_k) ==> VBool? (i.interp_quant k bs body))

let rec lemma_evaluate (i:interpretation value) (scope:list sort) (e:expr) (rho:env value)
  : Lemma (requires application_model i)
          (ensures D.scoped scope e /\ environment_typed scope rho ==>
                     scalar_typed (get_sort e) (eval i e rho))
          (decreases e)
  = match e with
    | Var _ _ -> ()
    | App f args -> lemma_evaluate_args i scope args f.domain rho
    | Quantifier k _ _ _ -> (match k with Forall_k | Exists_k | Lambda_k -> ())

and lemma_evaluate_args (i:interpretation value) (scope:list sort)
                        (args:list expr) (ss:list sort) (rho:env value)
  : Lemma (requires application_model i)
          (ensures D.scoped_args scope args /\ sorts_match args ss /\ environment_typed scope rho ==>
                     arguments_typed ss (eval_args i args rho))
          (decreases args)
  = match args, ss with
    | a :: rest, s :: tail ->
      lemma_evaluate i scope a rho;
      lemma_evaluate_args i scope rest tail rho;
      (match get_sort a, s with BaseSort _, BaseSort _ -> () | _, _ -> ())
    | _, _ -> ()

let lemma_application_model (i:interpretation value)
  : Lemma (requires application_model i) (ensures model i)
  = FStar.Classical.forall_intro_3 (lemma_evaluate i)

let default_value (s:sort) : value = if s = bool_sort then VBool false else VInt 0

let default_environment (scope:list sort) : env value =
  fun n -> if n < L.length scope then default_value (L.index scope n) else VInt 0

let lemma_default_environment (scope:list sort)
  : Lemma (environment_typed scope (default_environment scope))
  = let aux (n:nat)
      : Lemma (n < L.length scope ==> scalar_typed (L.index scope n) (default_environment scope n))
      = () in
    FStar.Classical.forall_intro aux

(* A witness for the typing/literal/reflexivity contracts, not a BV model. *)
let witness : interpretation value = {
  interp_app = (fun f _ ->
    if f = (match R.true_expr with App g _ -> g | _ -> f) ||
       (f.interp = Some op_eq && f.range = bool_sort)
    then VBool true else default_value f.range);
  uninterp_app = (fun f _ -> default_value f.range);
  interp_quant = (fun _ _ _ -> VBool false);
}

let lemma_witness ()
  : Lemma (model witness /\ literal_model witness /\ reflexive_equality witness /\ quant_extensional witness)
  = let interpreted (f:func_decl{Some? f.interp}) (vs:list value)
      : Lemma (arguments_typed f.domain vs ==> scalar_typed f.range (witness.interp_app f vs))
      = () in
    let uninterpreted (f:func_decl{is_uninterp_decl f}) (vs:list value)
      : Lemma (arguments_typed f.domain vs ==> scalar_typed f.range (witness.uninterp_app f vs))
      = () in
    let quantifier (k:quantifier_kind) (bs:list sort) (body:list value -> value)
      : Lemma ((k = Forall_k \/ k = Exists_k) ==> VBool? (witness.interp_quant k bs body))
      = () in
    FStar.Classical.forall_intro_2 interpreted;
    FStar.Classical.forall_intro_2 uninterpreted;
    FStar.Classical.forall_intro_3 quantifier;
    lemma_application_model witness
