module Z3SubstitutionTests

open Z3AstTheory
module S = Z3Substitution
module VS = Z3QuantifierVacuitySyntax
module VM = Z3QuantifierVacuitySemantics
module VD = Z3QuantifierVacuityScope
module VT = Z3QuantifierVacuitySorted
module NR = Z3NnfReplay
module Sig = Z3DatatypeSignature
module Sem = Z3SortedSemantics
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module D = Z3ExprScope
module DV = Z3DatatypeValue
module SB = Z3SortedBinding
module L = FStar.List.Tot

let int_s = SortApp IntSymbol []
let array_s = ArraySort [int_s] (ArraySort [int_s] int_s)
let lambda_s = ArraySort [int_s] array_s
let open_array = Var 0 array_s
let array_constant =
  App { decl_name = "a"; domain = []; range = array_s; interp = None; int_params = [] } []
let pair_decl =
  { decl_name = "pair"; domain = [array_s; int_s; array_s]; range = array_s;
    interp = None; int_params = [] }

let capture_body =
  Quantifier Lambda_k [int_s] lambda_s
    (App pair_decl [Var 1 array_s; Var 0 int_s; Var 2 array_s])
let capture_result =
  Quantifier Lambda_k [int_s] lambda_s
    (App pair_decl [Var 1 array_s; Var 0 int_s; Var 1 array_s])

let capture_avoiding_open_argument ()
  : Lemma (S.substitute [open_array] capture_body == Some capture_result)
  = assert_norm (S.substitute [open_array] capture_body == Some capture_result)

let predicate =
  { decl_name = "p"; domain = [int_s; bool_sort; array_s]; range = bool_sort;
    interp = None; int_params = [] }
let mixed_body =
  Quantifier Forall_k [bool_sort; int_s] bool_sort
    (App predicate [Var 0 int_s; Var 1 bool_sort; Var 2 array_s])
let mixed_result =
  Quantifier Forall_k [bool_sort; int_s] bool_sort
    (App predicate [Var 0 int_s; Var 1 bool_sort; array_constant])

let heterogeneous_binder_order ()
  : Lemma (S.substitute [array_constant] mixed_body == Some mixed_result)
  = assert_norm (S.substitute [array_constant] mixed_body == Some mixed_result)

let rejects_ill_sorted_and_missing_arguments ()
  : Lemma (S.substitute [Var 0 int_s] (Var 0 array_s) == None /\
           S.apply (fun _ _ -> Some (Var 0 int_s)) (Var 0 array_s) == None /\
           S.apply (fun _ _ -> None) mixed_body == None)
  = assert_norm (S.substitute [Var 0 int_s] (Var 0 array_s) == None /\
                 S.apply (fun _ _ -> Some (Var 0 int_s)) (Var 0 array_s) == None /\
                 S.apply (fun _ _ -> None) mixed_body == None)

let sparse_instantiation_under_binder ()
  : Lemma (S.instantiate 0 [9] [open_array]
             (Quantifier Lambda_k [int_s] lambda_s (Var 10 array_s)) ==
           Some (Quantifier Lambda_k [int_s] lambda_s (Var 1 array_s)) /\
           S.instantiate 0 [0] [array_constant] mixed_body == Some mixed_result)
  = assert_norm (S.instantiate 0 [9] [open_array]
                   (Quantifier Lambda_k [int_s] lambda_s (Var 10 array_s)) ==
                 Some (Quantifier Lambda_k [int_s] lambda_s (Var 1 array_s)) /\
                 S.instantiate 0 [0] [array_constant] mixed_body == Some mixed_result)

let sparse_variable_map_and_missing_entries ()
  : Lemma (S.instantiate 0 [9; 4; 1] [array_constant; open_array; Var 2 int_s]
             (App pair_decl [Var 4 array_s; Var 1 int_s; Var 9 array_s]) ==
           Some (App pair_decl [open_array; Var 2 int_s; array_constant]) /\
           S.instantiate 0 [4] [array_constant] (Var 9 array_s) == None /\
           S.instantiate 0 [4; 9] [array_constant] (Var 9 array_s) == None /\
           S.instantiate 0 [4; 4] [array_constant; open_array] (Var 4 array_s) ==
           Some array_constant)
  = assert_norm (S.instantiate 0 [9; 4; 1] [array_constant; open_array; Var 2 int_s]
                   (App pair_decl [Var 4 array_s; Var 1 int_s; Var 9 array_s]) ==
                 Some (App pair_decl [open_array; Var 2 int_s; array_constant]) /\
                 S.instantiate 0 [4] [array_constant] (Var 9 array_s) == None /\
                 S.instantiate 0 [4; 9] [array_constant] (Var 9 array_s) == None /\
                 S.instantiate 0 [4; 4] [array_constant; open_array] (Var 4 array_s) ==
                 Some array_constant)

type nested_array = int -> GTot (int -> GTot int)

let substitution_over_nested_arrays (i:interpretation nested_array) (rho:env nested_array)
  : Lemma (requires quant_extensional i)
          (ensures eval i capture_body (shift (eval_args i [open_array] rho) rho) ==
                   eval i capture_result rho)
  = capture_avoiding_open_argument ();
    S.lemma_substitute i rho [open_array] capture_body capture_result

let witness (v:nested_array) : interpretation nested_array = {
  interp_app = (fun _ args -> match args with [] -> v | head :: _ -> head);
  uninterp_app = (fun _ args -> match args with [] -> v | head :: _ -> head);
  interp_quant = (fun _ _ _ -> v);
}

let inhabited_function_carrier (v:nested_array)
  : Lemma (quant_extensional (witness v) /\
           eval (witness v) capture_body
             (shift (eval_args (witness v) [open_array] (fun _ -> v)) (fun _ -> v)) ==
           eval (witness v) capture_result (fun _ -> v))
  = assert (quant_extensional (witness v));
    substitution_over_nested_arrays (witness v) (fun _ -> v)

let lower_body =
  Quantifier Lambda_k [int_s] lambda_s
    (App pair_decl [Var 2 array_s; Var 0 int_s; Var 3 array_s])

let lower_result =
  Quantifier Lambda_k [int_s] lambda_s
    (App pair_decl [Var 1 array_s; Var 0 int_s; Var 2 array_s])

let lower_nested_function_carrier (i:interpretation nested_array) (rho:env nested_array) (v:nested_array)
  : Lemma (requires quant_extensional i)
          (ensures eval i lower_body (shift [v] rho) == eval i lower_result rho /\
                   VS.lower 0 (Quantifier Lambda_k [int_s] lambda_s (Var 1 array_s)) == None) =
  assert_norm (VS.lower 0 lower_body == Some lower_result);
  assert_norm (VS.lower 0 (Quantifier Lambda_k [int_s] lambda_s (Var 1 array_s)) == None);
  VM.lemma_erased_environment 0 [v] rho;
  VM.lemma_lower_sound 0 lower_body lower_result i (shift [v] rho) rho

let lower_assignment_equivalence (i:interpretation nested_array) (rho:env nested_array) (v:nested_array)
  : Lemma (requires quant_extensional i)
          (ensures VM.all_assignments_by (fun (a:nested_array) -> a 0 0 == 0) i rho 1 lower_body true <==>
                   VM.all_assignments_by (fun (a:nested_array) -> a 0 0 == 0) i rho 0 lower_result true) =
  assert_norm (VS.lower 0 lower_body == Some lower_result);
  VM.lemma_all_assignments_by v (fun (a:nested_array) -> a 0 0 == 0) 0 1 lower_body lower_result true i rho

let scoped_lower_body =
  Quantifier Forall_k [int_s] bool_sort
    (App predicate [Var 0 int_s; Var 2 bool_sort; Var 3 array_s])

let scoped_lower_result =
  Quantifier Forall_k [int_s] bool_sort
    (App predicate [Var 0 int_s; Var 1 bool_sort; Var 2 array_s])

let lowering_preserves_nested_scope ()
  : Lemma (D.scoped [bool_sort; array_s] scoped_lower_result /\
           get_sort scoped_lower_result == get_sort scoped_lower_body) =
  assert_norm (D.scoped [int_s; bool_sort; array_s] scoped_lower_body);
  assert_norm (VS.lower 0 scoped_lower_body == Some scoped_lower_result);
  VD.lemma_lower_erased_scope 0 [int_s; bool_sort; array_s]
    scoped_lower_body scoped_lower_result

let sorted_lowering_evaluation (#base:sort -> Type0) (sigma:DV.signature)
                               (i:DV.interpretation base sigma)
                               (eta:DV.environment base sigma [bool_sort; array_s])
                               (v:DV.value base sigma int_s)
  : Lemma (
      let rho = DV.extend sigma [bool_sort; array_s] [int_s] [v] eta in
      DV.evaluate sigma i [int_s; bool_sort; array_s] rho scoped_lower_body ==
      DV.evaluate sigma i [bool_sort; array_s] eta scoped_lower_result) =
  let rho = DV.extend sigma [bool_sort; array_s] [int_s] [v] eta in
  assert_norm (D.scoped [int_s; bool_sort; array_s] scoped_lower_body);
  assert_norm (VS.lower 0 scoped_lower_body == Some scoped_lower_result);
  VD.lemma_lower_erased_scopes 0 [int_s; bool_sort; array_s];
  let indices (n:nat{n < L.length [int_s; bool_sort; array_s]})
    : Lemma (
      match VD.lower_substitution 0 n (L.index [int_s; bool_sort; array_s] n) with
      | Some e ->
        D.scoped [bool_sort; array_s] e /\ get_sort e == L.index [int_s; bool_sort; array_s] n /\
        rho n == DV.evaluate sigma i [bool_sort; array_s] eta e
      | None -> True) =
    if n = 0 then () else if n = 1 then () else () in
  FStar.Classical.forall_intro indices;
  VD.lemma_lower_evaluate sigma i 0 [int_s; bool_sort; array_s] [bool_sort; array_s]
    rho eta scoped_lower_body scoped_lower_result

let remove_last_binder =
  Quantifier Forall_k [int_s] bool_sort
    (App predicate [Var 1 int_s; Var 2 bool_sort; Var 3 array_s])

let remove_last_result =
  App predicate [Var 0 int_s; Var 1 bool_sort; Var 2 array_s]

let remove_mixed_binder =
  Quantifier Forall_k [bool_sort; int_s] bool_sort
    (App predicate [Var 2 int_s; Var 1 bool_sort; Var 4 array_s])

let remove_mixed_result =
  Quantifier Forall_k [bool_sort] bool_sort
    (App predicate [Var 1 int_s; Var 0 bool_sort; Var 3 array_s])

let remove_later_exists =
  Quantifier Exists_k [bool_sort; int_s] bool_sort
    (App predicate [Var 0 int_s; Var 3 bool_sort; Var 4 array_s])

let remove_later_exists_result =
  Quantifier Exists_k [int_s] bool_sort
    (App predicate [Var 0 int_s; Var 2 bool_sort; Var 3 array_s])

let unused_removal_preserves_scope ()
  : Lemma (D.scoped [int_s; bool_sort; array_s] remove_last_result /\
           D.scoped [int_s; bool_sort; array_s] remove_mixed_result) =
  assert_norm (D.scoped [int_s; bool_sort; array_s] remove_last_binder /\
               D.scoped [int_s; bool_sort; array_s] remove_mixed_binder);
  assert_norm (VS.step remove_last_binder == Some remove_last_result /\
               VS.step remove_mixed_binder == Some remove_mixed_result);
  VD.lemma_step_scope [int_s; bool_sort; array_s] remove_last_binder remove_last_result;
  VD.lemma_step_scope [int_s; bool_sort; array_s] remove_mixed_binder remove_mixed_result

let sorted_unused_removal (#base:sort -> Type0) (s:Sig.checked_schema)
                          (bc:Sig.boolean_carrier base) (eq:Sem.scalar_model base)
                          (other:DV.interpretation base (Sig.signature s))
                          (rho:DV.environment base (Sig.signature s) [int_s; bool_sort; array_s])
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other)
          (ensures NR.same_at s bc eq other [int_s; bool_sort; array_s] rho
                     remove_last_binder remove_last_result /\
                   NR.same_at s bc eq other [int_s; bool_sort; array_s] rho
                     remove_mixed_binder remove_mixed_result /\
                   NR.same_at s bc eq other [int_s; bool_sort; array_s] rho
                     remove_later_exists remove_later_exists_result) =
  assert_norm (D.scoped [int_s; bool_sort; array_s] remove_last_binder /\
               D.scoped [int_s; bool_sort; array_s] remove_mixed_binder /\
               D.scoped [int_s; bool_sort; array_s] remove_later_exists);
  assert_norm (VS.step remove_last_binder == Some remove_last_result /\
               VS.step remove_mixed_binder == Some remove_mixed_result /\
               VS.step remove_later_exists == Some remove_later_exists_result);
  VT.lemma_step_at s bc eq other [int_s; bool_sort; array_s] rho
    remove_last_binder remove_last_result;
  NR.lemma_same_at s bc eq other [int_s; bool_sort; array_s] rho
    remove_last_binder remove_last_result;
  VT.lemma_step_at s bc eq other [int_s; bool_sort; array_s] rho
    remove_mixed_binder remove_mixed_result;
  NR.lemma_same_at s bc eq other [int_s; bool_sort; array_s] rho
    remove_mixed_binder remove_mixed_result;
  VT.lemma_step_at s bc eq other [int_s; bool_sort; array_s] rho
    remove_later_exists remove_later_exists_result;
  NR.lemma_same_at s bc eq other [int_s; bool_sort; array_s] rho
    remove_later_exists remove_later_exists_result

let bool_wrapper =
  { decl_name = "wrap"; domain = [bool_sort]; range = bool_sort;
    interp = None; int_params = [] }
let equivalent_nested =
  Quantifier Forall_k [int_s] bool_sort (App bool_wrapper [remove_last_binder])
let equivalent_nested_result =
  Quantifier Forall_k [int_s] bool_sort (App bool_wrapper [remove_last_result])

let sorted_nested_unused_equivalence (#base:sort -> Type0) (s:Sig.checked_schema)
                                     (bc:Sig.boolean_carrier base) (eq:Sem.scalar_model base)
                                     (other:DV.interpretation base (Sig.signature s))
                                     (rho:DV.environment base (Sig.signature s) [bool_sort; array_s])
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other)
          (ensures (assert_norm (D.scoped [bool_sort; array_s] equivalent_nested /\
                                  D.scoped [bool_sort; array_s] equivalent_nested_result);
            DV.evaluate (Sig.signature s) (Sem.interpretation s bc eq other)
              [bool_sort; array_s] rho equivalent_nested ==
            DV.evaluate (Sig.signature s) (Sem.interpretation s bc eq other)
              [bool_sort; array_s] rho equivalent_nested_result)) =
  assert_norm (D.scoped [bool_sort; array_s] equivalent_nested /\
               D.scoped [bool_sort; array_s] equivalent_nested_result);
  assert_norm (VS.equivalent 4 equivalent_nested equivalent_nested_result /\
               VS.equivalent 4 equivalent_nested_result equivalent_nested);
  VT.lemma_equivalent_at s bc eq other 4 [bool_sort; array_s] rho
    equivalent_nested equivalent_nested_result;
  VT.lemma_equivalent_at s bc eq other 4 [bool_sort; array_s] rho
    equivalent_nested_result equivalent_nested
