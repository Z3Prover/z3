module Z3ObservationalSemanticsTests

open Z3AstTheory
module C = Z3CanonicalOps
module OS = Z3ObservationalSemantics
module O = Z3ObservationalProof
module Syntax = Z3ObservationalSyntax
module D = Z3ExprScope
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics

let atom (name:string) (s:sort) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = [] } []

let p = atom "p" bool_sort
let q = atom "q" bool_sort
let array_s = ArraySort [BaseSort "Int"] (ArraySort [BaseSort "Int"] (BaseSort "Int"))
let a = atom "a" array_s
let b = atom "b" array_s

(* A non-legacy, inhabited interpretation for the generalized proof theorem. *)
let application (f:func_decl{Some? f.interp}) (vs:list int) : int =
  if C.canonical_eq f then
    match vs with [x; y] -> if x = y then 1 else 0 | _ -> 0
  else 0

let model : interpretation int = {
  interp_app = application;
  uninterp_app = (fun _ _ -> 1);
  interp_quant = (fun _ _ _ -> 0);
}

let rho : env int = fun _ -> 0

let lemma_boolean_result (e:expr)
  : Lemma (OS.boolean_value 1 0 (eval model e rho))
  = match e with
    | App f args ->
      if Some? f.interp then
        (match eval_args model args rho with [_; _] -> () | _ -> ())
    | _ -> ()

let lemma_model ()
  : Lemma (OS.boolean_model 1 0 (O.denotation model rho) /\ O.equality_model 1 model rho)
  = FStar.Classical.forall_intro lemma_boolean_result

let congruence : O.oproof =
  O.OCongr { decl_name = "f"; domain = [bool_sort]; range = array_s;
             interp = None; int_params = [] } [p] [q] [O.OIff p q]

let abstract_carrier_proof ()
  : Lemma (OS.observations_agree 1 (O.denotation model rho)
             (fst (Some?.v (O.ofact congruence))) (snd (Some?.v (O.ofact congruence))))
  = lemma_model ();
    assert_norm (Some? (O.ofact congruence));
    O.lemma_oproof_sound_at 1 0 model congruence rho

let malformed_observation_rejected ()
  : Lemma (O.ofact (O.OIff p a) == None /\ O.ofact (O.OPremise p a) == None)
  = assert_norm (O.ofact (O.OIff p a) == None /\ O.ofact (O.OPremise p a) == None)

type nested_array = int -> GTot (int -> GTot int)

let array_denotation (f g:nested_array) : OS.denotation nested_array (fun e -> get_sort e = array_s) =
  fun e -> if e = a then f else g

let ghost_array_observations (f g:nested_array)
  : Lemma (requires f == g)
          (ensures OS.observations_agree f (array_denotation f g) a b /\
                   OS.observations_agree f (array_denotation f g) b a)
  = OS.lemma_from_values f (array_denotation f g) a b;
    OS.lemma_symmetry f (array_denotation f g) a b

let incomplete_booleans : OS.denotation int (fun _ -> true) =
  fun e -> if e = p then 1 else 2

let boolean_completeness_is_required ()
  : Lemma (OS.observations_agree 0 incomplete_booleans p q /\
           incomplete_booleans p <> incomplete_booleans q /\
           not (OS.boolean_model 0 1 incomplete_booleans))
  = ()

let different_sorts_do_not_agree ()
  : Lemma (not (OS.observations_agree 1 (O.denotation model rho) p a))
  = ()

let sorted_observational_modus_ponens (#base:sort -> Type0) (s:S.checked_schema)
                                    (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                                    (other:V.interpretation base (S.signature s))
                                    (scope:list sort)
                                    (env:V.environment base (S.signature s) scope)
                                    (x:expr{D.scoped scope x}) (y:expr{D.scoped scope y})
  : Lemma (requires get_sort x == get_sort y /\
                    T.observations_agree_at s bc eq other scope env x y /\
                    T.evaluate_at s bc eq other scope env x == T.boolean s bc true)
          (ensures T.evaluate_at s bc eq other scope env y == T.boolean s bc true) =
  let relation = Syntax.mk_oeq_expr x y in
  assert (Syntax.decide_mp_oeq x relation == Some y);
  Syntax.lemma_decide_mp_oeq (T.boolean s bc true)
    (T.observation_denotation_at s bc eq other scope env) x relation

let observational_modus_ponens_rejects_mismatch ()
  : Lemma (Syntax.decide_mp_oeq q (Syntax.mk_oeq_expr p q) == None /\
           Syntax.decide_mp_oeq p (Syntax.mk_oeq_expr p a) == None) =
  assert_norm (Syntax.decide_mp_oeq q (Syntax.mk_oeq_expr p q) == None /\
               Syntax.decide_mp_oeq p (Syntax.mk_oeq_expr p a) == None)
