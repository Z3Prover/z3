module Z3SortedArrayTests

open Z3AstTheory
module A = Z3ArraySyntax
module K = Z3SortedArray
module F = Z3ArrayTheory
module R = Z3ClauseSyntax
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3ExprScope
module E = Z3ArrayEqualitySyntax
module X = Z3SortedArrayEquality

let nested_values_are_full_function_spaces (key:int)
  : Lemma (
      let inner = K.functional #bool #int false in
      let outer = K.functional #int #(F.semantic_arr bool int) 0 in
      let base = outer.constant (inner.constant 0) in
      let value = inner.write (inner.constant 7) true 9 in
      let array = outer.write base key value in
      inner.read (outer.read array key) true == 9 /\
      inner.read (outer.read array key) false == 7) = ()

let nested_overwrite_and_redundant (key:int)
  : Lemma (
      let inner = K.functional #bool #int false in
      let outer = K.functional #int #(F.semantic_arr bool int) 0 in
      let base = outer.constant (inner.constant 0) in
      outer.write (outer.write base key (inner.constant 1)) key (inner.constant 2) ==
      outer.write base key (inner.constant 2) /\
      outer.write base key (outer.read base key) == base) =
  let inner = K.functional #bool #int false in
  let outer = K.functional #int #(F.semantic_arr bool int) 0 in
  let base = outer.constant (inner.constant 0) in
  K.lemma_overwrite outer base key (inner.constant 1) (inner.constant 2);
  K.lemma_redundant outer base key

let native_scalar_gate_is_not_broadened ()
  : Lemma (
      let array = Var 0 (ArraySort [bool_sort] (SortApp IntSymbol [])) in
      not (A.select_app (K.select_decl bool_sort (SortApp IntSymbol [])) array R.true_expr)) =
  assert_norm (
    let array = Var 0 (ArraySort [bool_sort] (SortApp IntSymbol [])) in
    not (A.select_app (K.select_decl bool_sort (SortApp IntSymbol [])) array R.true_expr))

let malformed_store_metadata_is_rejected ()
  : Lemma (
      let integer = SortApp IntSymbol [] in
      let array = Var 0 (ArraySort [integer] integer) in
      let index = Var 1 integer in
      let value = Var 2 integer in
      A.store_contract
        (App { K.store_decl integer integer with int_params = [1] } [array; index; value]) == None) =
  assert_norm (
    let integer = SortApp IntSymbol [] in
    let array = Var 0 (ArraySort [integer] integer) in
    let index = Var 1 integer in
    let value = Var 2 integer in
    A.store_contract
      (App { K.store_decl integer integer with int_params = [1] } [array; index; value]) == None)

let nested_sort = ArraySort [SortApp IntSymbol []] (ArraySort [bool_sort] (SortApp IntSymbol []))
let ite_scope = [bool_sort; nested_sort; nested_sort]
let condition = Var 0 bool_sort
let first_array = Var 1 nested_sort
let second_array = Var 2 nested_sort
let original_ite = App (A.term_ite_decl nested_sort) [condition; first_array; second_array]
let flipped_ite = App (A.term_ite_decl nested_sort)
  [R.mk_not_expr condition; second_array; first_array]

let flipped_nested_array_ite_is_accepted ()
  : Lemma (A.equivalent 1 original_ite flipped_ite /\
           not (A.equivalent 0 original_ite flipped_ite)) =
  assert_norm (A.equivalent 1 original_ite flipped_ite /\
               not (A.equivalent 0 original_ite flipped_ite))

let flipped_nested_array_ite_is_sound (#base:sort -> Type0) (s:S.checked_schema)
                                    (bc:S.boolean_carrier base) (core:T.scalar_model base)
                                    (other:V.interpretation base (S.signature s))
                                    (rho:V.environment base (S.signature s) ite_scope)
  : Lemma (T.truth_at s bc core other ite_scope rho (R.mk_eq_expr original_ite flipped_ite)) =
  assert_norm (D.scoped ite_scope original_ite /\ D.scoped ite_scope flipped_ite /\
               A.ite_equivalent original_ite flipped_ite);
  K.lemma_ite_equivalent s bc core other ite_scope rho original_ite flipped_ite;
  T.lemma_equality_at s bc core other ite_scope rho original_ite flipped_ite

let integer_sort = SortApp IntSymbol []
let numeral (n:int) = App {
  decl_name = "array-default"; domain = []; range = integer_sort;
  interp = Some Z3OperatorTags.op_num_rational; int_params = [n; 1];
} []
let zero = numeral 0
let one = numeral 1
let zero_array = App X.const_decl [zero]
let one_array = App X.const_decl [one]
let stored_array = App (K.store_decl integer_sort integer_sort)
  [zero_array; Var 0 integer_sort; Var 1 integer_sort]
let unequal_default_formula = R.mk_eq_expr stored_array one_array

let symbolic_store_does_not_change_default_inequality ()
  : Lemma (E.unequal_defaults unequal_default_formula) =
  assert_norm (E.unequal_defaults unequal_default_formula)

let finite_index_defaults_are_not_an_infinite_domain_proof ()
  : Lemma (
      let f = { X.const_decl with range = ArraySort [bool_sort] integer_sort } in
      not (E.unequal_defaults (R.mk_eq_expr (App f [zero]) (App f [one])))) =
  assert_norm (
    let f = { X.const_decl with range = ArraySort [bool_sort] integer_sort } in
    not (E.unequal_defaults (R.mk_eq_expr (App f [zero]) (App f [one]))))

let rec stores (n:nat) (a:expr) : Tot expr (decreases n) =
  if n = 0 then a
  else App (K.store_decl integer_sort integer_sort)
    [stores (n - 1) a; Var 0 integer_sort; Var 1 integer_sort]

let default_search_budget_counts_the_constant_leaf ()
  : Lemma (E.default_term 64 (stores 63 zero_array) == Some zero /\
           E.default_term 64 (stores 64 zero_array) == None) =
  assert_norm (E.default_term 64 (stores 63 zero_array) == Some zero /\
               E.default_term 64 (stores 64 zero_array) == None)

let symbolic_store_default_inequality_is_sound (#base:sort -> Type0) (s:S.checked_schema)
                                             (bc:S.boolean_carrier base) (core:T.scalar_model base)
                                             (other:V.interpretation base (S.signature s))
                                             (m:K.family base (S.signature s){
                                               m.supports integer_sort integer_sort})
                                             (rho:V.environment base (S.signature s)
                                               [integer_sort; integer_sort])
  : Lemma (requires K.model s bc core other m /\ X.const_model s bc core other m)
          (ensures not (T.truth_at s bc core other [integer_sort; integer_sort] rho
                          unequal_default_formula)) =
  assert_norm (D.scoped [integer_sort; integer_sort] unequal_default_formula /\
               E.unequal_defaults unequal_default_formula);
  assert (K.supported m unequal_default_formula);
  X.lemma_unequal_defaults s bc core other m [integer_sort; integer_sort] rho unequal_default_formula
