module Z3ScopedModelTests

open Z3AstTheory
open Z3ValueTheory
module SM = Z3ScopedModel
module O = Z3ObservationalEquality
module LE = Z3LinearArithmeticEmbed
module A = Z3ArrayLemma
module D = Z3Definitions

let lemma_legacy_boolean_contract_impossible (i:interpretation value)
  : Lemma (requires O.boolean_model i) (ensures False)
  = let a = Var 0 bool_sort in
    let rho : env value = fun _ -> VInt 0 in
    assert (eval i a rho == VInt 0);
    assert (VBool? (eval i a rho))

let lemma_legacy_integer_contract_impossible (i:interpretation value) (nu:value -> FStar.Real.real)
  : Lemma (requires LE.numeric_model i nu) (ensures False)
  = let a = Var 0 SM.int_sort in
    let rho : env value = fun _ -> VBool false in
    assert (eval i a rho == VBool false);
    assert (VInt? (eval i a rho))

let lemma_legacy_array_contract_impossible (i:interpretation value)
  : Lemma (requires A.array_model i) (ensures False)
  = let s = ArraySort [SM.int_sort] SM.int_sort in
    let a = Var 0 s in
    let k = Var 1 SM.int_sort in
    let f = { decl_name = "select"; domain = [s; SM.int_sort]; range = SM.int_sort;
              interp = Some op_select; int_params = [] } in
    let rho : env value = fun _ -> VBool false in
    assert (A.select_app f a k);
    assert (eval i a rho == VBool false);
    assert (VArr? (eval i a rho))

let lemma_scoped_environment_guards ()
  : Lemma (~(D.scoped [] (Var 0 bool_sort)) /\
           ~(SM.environment_typed [bool_sort] (fun _ -> VInt 0)) /\
           ~(SM.environment_typed [SM.int_sort] (fun _ -> VBool false)))
  = ()

let lemma_scoped_contract_has_witness ()
  : Lemma (SM.model SM.witness /\ SM.literal_model SM.witness /\
           SM.reflexive_equality SM.witness /\ quant_extensional SM.witness /\
           eval SM.witness (Var 0 bool_sort) (fun _ -> VInt 0) == VInt 0 /\
           eval SM.witness (Var 0 SM.int_sort) (fun _ -> VBool false) == VBool false)
  = SM.lemma_witness ()

let lemma_typed_variables ()
  : Lemma (SM.environment_typed [bool_sort; SM.int_sort]
             (SM.default_environment [bool_sort; SM.int_sort]) /\
           eval SM.witness (Var 0 bool_sort) (SM.default_environment [bool_sort; SM.int_sort]) == VBool false /\
           eval SM.witness (Var 1 SM.int_sort) (SM.default_environment [bool_sort; SM.int_sort]) == VInt 0)
  = SM.lemma_default_environment [bool_sort; SM.int_sort]
