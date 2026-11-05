module Z3DatatypeValueTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module L = FStar.List.Tot

let int_s = BaseSort "Int"
let bool_s = BaseSort "Bool"
let tree_s = BaseSort "Tree"
let forest_s = BaseSort "Forest"

let primitive (s:sort) : Type0 =
  match s with BaseSort "Int" -> int | BaseSort "Bool" -> bool | _ -> unit

let primitive_booleans : S.boolean_carrier primitive =
  S.Mkboolean_carrier #primitive (fun b -> b) (fun b -> b) ()

let leaf = {
  decl_name = "leaf"; domain = [int_s; bool_s]; range = tree_s;
  interp = Some 200; int_params = [0; 0; 2];
}
let branch = {
  decl_name = "branch"; domain = [forest_s]; range = tree_s;
  interp = Some 200; int_params = [0; 1; 1];
}
let nil = {
  decl_name = "nil"; domain = []; range = forest_s;
  interp = Some 200; int_params = [1; 2; 0];
}
let cons = {
  decl_name = "cons"; domain = [tree_s; forest_s]; range = forest_s;
  interp = Some 200; int_params = [1; 3; 2];
}
let sigma = [leaf; branch; nil; cons]

#push-options "--fuel 4 --ifuel 2"

let example_leaf : V.value primitive sigma tree_s =
  let xs:list (V.tree primitive) = [V.Scalar int_s 7; V.Scalar bool_s true] in
  assert_norm (V.fields_have_sorts #primitive sigma leaf.domain [V.Scalar int_s 7; V.Scalar bool_s true]);
  V.construct sigma leaf xs

let empty_forest : V.value primitive sigma forest_s = V.construct sigma nil []

let singleton_forest : V.value primitive sigma forest_s =
  V.construct sigma cons [example_leaf; empty_forest]

let heterogeneous_fields ()
  : Lemma (ensures V.has_sort #primitive sigma tree_s example_leaf /\
                   not (V.has_sort #primitive sigma tree_s
                     (V.Constructor leaf [V.Scalar bool_s true; V.Scalar int_s 7])) /\
                   not (V.has_sort #primitive sigma tree_s (V.Scalar tree_s ()))) =
  assert_norm (
    V.has_sort #primitive sigma tree_s example_leaf /\
    not (V.has_sort #primitive sigma tree_s
      (V.Constructor leaf [V.Scalar bool_s true; V.Scalar int_s 7])) /\
    not (V.has_sort #primitive sigma tree_s (V.Scalar tree_s ())))

let varying_fallback (v:V.value primitive sigma tree_s) : V.value primitive sigma int_s =
  assert_norm (not (V.contains_datatype sigma int_s));
  V.Scalar int_s (if V.size v = 2 then 11 else 29)

let wrong_constructor_selectors ()
  : Lemma (ensures
      V.select sigma leaf 0 varying_fallback (V.construct sigma branch [empty_forest]) ==
        V.Scalar int_s 11 /\
      V.select sigma leaf 0 varying_fallback (V.construct sigma branch [singleton_forest]) ==
        V.Scalar int_s 29 /\
      V.select sigma leaf 0 varying_fallback example_leaf == V.Scalar int_s 7) =
  assert_norm (
    V.select sigma leaf 0 varying_fallback (V.construct sigma branch [empty_forest]) ==
      V.Scalar int_s 11 /\
    V.select sigma leaf 0 varying_fallback (V.construct sigma branch [singleton_forest]) ==
      V.Scalar int_s 29 /\
    V.select sigma leaf 0 varying_fallback example_leaf == V.Scalar int_s 7)

let mutually_recursive_inhabitation ()
  : Lemma (ensures Some? (V.inhabit #primitive 4 sigma
      (fun s -> match s with BaseSort "Int" -> 0 | BaseSort "Bool" -> false | _ -> ()) forest_s)) =
  assert_norm (Some? (V.inhabit #primitive 4 sigma
    (fun s -> match s with BaseSort "Int" -> 0 | BaseSort "Bool" -> false | _ -> ()) forest_s))

let bound_values : V.arguments primitive sigma [bool_s; int_s] =
  assert_norm (V.fields_have_sorts #primitive sigma [bool_s; int_s]
    [V.Scalar bool_s true; V.Scalar int_s 7]);
  [V.Scalar bool_s true; V.Scalar int_s 7]

let sorted_environment_extension ()
  : Lemma (ensures (
      let rho:V.environment primitive sigma [tree_s] = fun _ -> example_leaf in
      let inner = V.extend sigma [tree_s] [bool_s; int_s] bound_values rho in
      inner 0 == V.Scalar bool_s true /\
      inner 1 == V.Scalar int_s 7 /\ inner 2 == example_leaf)) =
  assert_norm (
    let rho:V.environment primitive sigma [tree_s] = fun _ -> example_leaf in
    let inner = V.extend sigma [tree_s] [bool_s; int_s] bound_values rho in
    inner 0 == V.Scalar bool_s true /\
    inner 1 == V.Scalar int_s 7 /\ inner 2 == example_leaf)

let evaluation_values : V.arguments primitive sigma [int_s; bool_s] =
  assert_norm (V.fields_have_sorts #primitive sigma [int_s; bool_s]
    [V.Scalar int_s 7; V.Scalar bool_s true]);
  [V.Scalar int_s 7; V.Scalar bool_s true]

let evaluation_environment : V.environment primitive sigma [int_s; bool_s] =
  fun n ->
    V.lemma_fields_index sigma [int_s; bool_s] evaluation_values n;
    L.index evaluation_values n

let sorted_constructor_evaluation (i:V.interpretation primitive sigma)
  : Lemma (ensures
      V.evaluate sigma i [int_s; bool_s] evaluation_environment
        (App leaf [Var 0 int_s; Var 1 bool_s]) == example_leaf) =
  assert_norm (Z3Definitions.scoped [int_s; bool_s]
    (App leaf [Var 0 int_s; Var 1 bool_s]));
  assert_norm (L.mem leaf sigma)

#pop-options
