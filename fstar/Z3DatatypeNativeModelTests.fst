module Z3DatatypeNativeModelTests

(* The SEMANTIC assertions of `concrete_datatype_model` in
   tools/test_native_bridge.ml, moved to F*.

   Since the typed-root G1a prototype change (023988e32) the typed datatype
   semantics are ghost: Z3DatatypeSignature.accessor_value, .application
   and .interpretation, and Z3DatatypeValue.select/.evaluate are GTot, so
   Custard erases them and the native harness can no longer run them. Every
   executable check of that test (schema validation, constructor values,
   sorts, recognizer_value, reconstruction, witnesses, descendants,
   map_base, find_accessor/find_recognizer rejection, marshaling identity,
   schema mutations) stays in the native harness. The ghost assertions are
   proved here, UNCONDITIONALLY (no model hypothesis), with their exact
   expected concrete values, on the same fixture:

     (declare-datatypes ((Tree 0) (Forest 0))
       (((leaf (number Int) (marked Bool)) (branch (children Forest))
         (fork (left Tree) (right Tree)))
        ((nil) (cons (first Tree) (rest Forest)))))

   with the native metadata layout of Z3Native.datatype_parameters
   (constructor [sort id; decl id; arity], recognizer [sort id; constructor
   decl id], accessor [sort id; constructor decl id; field]). Native sort
   and declaration ids are runtime AST ids, so symbolic ids stand in for
   them here (Tree 1, Forest 2, leaf/branch/fork/nil/cons 10..14); every
   lookup compares them only with each other. The carrier is the harness's
   (every scalar payload `false`, as S.shape_witness builds it), and
   `other` is the harness's supplied interpretation. Mapping (harness line
   -> lemma) is listed at each lemma; mutants are positively proved
   negations of a wrong expected value. *)

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module D = Z3Definitions
module L = FStar.List.Tot

let int_s : sort = BaseSort "Int"
let bool_s : sort = BaseSort "Bool"
let tree_s : sort = BaseSort "Tree"
let forest_s : sort = BaseSort "Forest"

let leaf_c : func_decl = { decl_name = "leaf"; domain = [int_s; bool_s]; range = tree_s; interp = Some 200; int_params = [1; 10; 2] }
let branch_c : func_decl = { decl_name = "branch"; domain = [forest_s]; range = tree_s; interp = Some 200; int_params = [1; 11; 1] }
let fork_c : func_decl = { decl_name = "fork"; domain = [tree_s; tree_s]; range = tree_s; interp = Some 200; int_params = [1; 12; 2] }
let nil_c : func_decl = { decl_name = "nil"; domain = []; range = forest_s; interp = Some 200; int_params = [2; 13; 0] }
let cons_c : func_decl = { decl_name = "cons"; domain = [tree_s; forest_s]; range = forest_s; interp = Some 200; int_params = [2; 14; 2] }

let recognizer (name:string) (s:sort) (sid did:int) : func_decl =
  { decl_name = name; domain = [s]; range = bool_sort; interp = Some 201; int_params = [sid; did] }

let accessor (name:string) (s r:sort) (sid did n:int) : func_decl =
  { decl_name = name; domain = [s]; range = r; interp = Some 202; int_params = [sid; did; n] }

let children : func_decl = accessor "children" tree_s forest_s 1 11 0
let fork_tester : func_decl = recognizer "is-fork" tree_s 1 12
let branch_tester : func_decl = recognizer "is-branch" tree_s 1 11

let leaf : S.constructor_case = { S.constructor = leaf_c; recognizer = recognizer "is-leaf" tree_s 1 10;
  accessors = [accessor "number" tree_s int_s 1 10 0; accessor "marked" tree_s bool_s 1 10 1] }
let branch : S.constructor_case = { S.constructor = branch_c; recognizer = branch_tester; accessors = [children] }
let fork : S.constructor_case = { S.constructor = fork_c; recognizer = fork_tester;
  accessors = [accessor "left" tree_s tree_s 1 12 0; accessor "right" tree_s tree_s 1 12 1] }
let nil : S.constructor_case = { S.constructor = nil_c; recognizer = recognizer "is-nil" forest_s 2 13; accessors = [] }
let cons : S.constructor_case = { S.constructor = cons_c; recognizer = recognizer "is-cons" forest_s 2 14;
  accessors = [accessor "first" forest_s tree_s 2 14 0; accessor "rest" forest_s forest_s 2 14 1] }

let raw : S.schema = { S.sorts = [tree_s; forest_s]; S.cases = [leaf; branch; fork; nil; cons] }

(* harness: `require (S.valid schema)` (kept native) *)
let schema : S.checked_schema = assert_norm (S.valid raw); raw

let sigma : V.signature = S.signature schema

let bits : sort -> Type0 = fun _ -> bool

let leaf_case : S.registered_case schema = assert_norm (L.mem leaf schema.S.cases); leaf
let branch_case : S.registered_case schema = assert_norm (L.mem branch schema.S.cases); branch

(* The harness's values: the S.shape_witness scalars (payload false). *)
let number : V.value bits sigma int_s =
  assert_norm (V.has_sort #bits sigma int_s (V.Scalar int_s false)); V.Scalar int_s false
let marked : V.value bits sigma bool_s =
  assert_norm (V.has_sort #bits sigma bool_s (V.Scalar bool_s false)); V.Scalar bool_s false

let leaf_t : V.tree bits = V.Constructor leaf_c [number; marked]
let nil_t : V.tree bits = V.Constructor nil_c []
let cons_t : V.tree bits = V.Constructor cons_c [leaf_t; nil_t]
let fork_t : V.tree bits = V.Constructor fork_c [leaf_t; leaf_t]
let branch_t : V.tree bits = V.Constructor branch_c [cons_t]

let leaf_value : V.value bits sigma tree_s = assert_norm (V.has_sort sigma tree_s leaf_t); leaf_t
let nil_value : V.value bits sigma forest_s = assert_norm (V.has_sort sigma forest_s nil_t); nil_t
let cons_value : V.value bits sigma forest_s = assert_norm (V.has_sort sigma forest_s cons_t); cons_t
let fork_value : V.value bits sigma tree_s = assert_norm (V.has_sort sigma tree_s fork_t); fork_t
let branch_value : V.value bits sigma tree_s = assert_norm (V.has_sort sigma tree_s branch_t); branch_t

(* The harness obtains number/marked from S.shape_witness and builds the
   values with S.constructor_value; `V.map_base convert` (convert = false)
   leaves them unchanged, so the harness's *_bool values are these. *)
let fixture_values ()
  : Lemma (S.shape_witness sigma int_s == Some number /\ S.shape_witness sigma bool_s == Some marked /\
           V.map_base #bits #bits (fun _ _ -> false) leaf_t == leaf_t /\
           V.map_base #bits #bits (fun _ _ -> false) fork_t == fork_t /\
           V.map_base #bits #bits (fun _ _ -> false) branch_t == branch_t /\
           V.map_base #bits #bits (fun _ _ -> false) nil_t == nil_t /\
           V.map_base #bits #bits (fun _ _ -> false) cons_t == cons_t) =
  assert_norm (S.shape_witness sigma int_s == Some number /\ S.shape_witness sigma bool_s == Some marked);
  assert_norm (V.map_base #bits #bits (fun _ _ -> false) leaf_t == leaf_t /\
               V.map_base #bits #bits (fun _ _ -> false) fork_t == fork_t /\
               V.map_base #bits #bits (fun _ _ -> false) branch_t == branch_t /\
               V.map_base #bits #bits (fun _ _ -> false) nil_t == nil_t /\
               V.map_base #bits #bits (fun _ _ -> false) cons_t == cons_t)

(* ---------------------------------------------------------------------- *)
(* A1 (harness L1889-1894): S.accessor_value, matched field and           *)
(*     argument-dependent wrong-constructor fallback                       *)
(* ---------------------------------------------------------------------- *)

let fallback (v:V.value bits sigma tree_s) : GTot (V.value bits sigma forest_s) =
  if S.recognizer_value schema leaf_case v then nil_value else cons_value

let a1_leaf () : Lemma (S.accessor_value schema branch_case 0 fallback leaf_value == nil_value) =
  assert_norm (S.accessor_value schema branch_case 0 fallback leaf_value == nil_value)

let a1_fork () : Lemma (S.accessor_value schema branch_case 0 fallback fork_value == cons_value) =
  assert_norm (S.accessor_value schema branch_case 0 fallback fork_value == cons_value)

let a1_branch () : Lemma (S.accessor_value schema branch_case 0 fallback branch_value == cons_value) =
  assert_norm (S.accessor_value schema branch_case 0 fallback branch_value == cons_value)

(* Mutants: the matched field is not the fallback's answer, and the
   fallback depends on its argument. *)
let a1_mutants ()
  : Lemma (~(S.accessor_value schema branch_case 0 fallback leaf_value == cons_value) /\
           ~(S.accessor_value schema branch_case 0 fallback fork_value == nil_value) /\
           ~(S.accessor_value schema branch_case 0 fallback branch_value == nil_value)) =
  a1_leaf (); a1_fork (); a1_branch ();
  assert_norm (~(nil_t == cons_t))

(* ---------------------------------------------------------------------- *)
(* A2 (harness L1910-1945): S.interpretation over the supplied `other`     *)
(* ---------------------------------------------------------------------- *)

let opaque_f : func_decl = { children with decl_name = "opaque"; interp = None; int_params = [] }

let other_application (f:func_decl) (xs:V.arguments bits sigma f.domain) : GTot (V.value bits sigma f.range) =
  match xs with
  | [value] ->
    if f = children then (if V.recognize leaf_c value then nil_value else cons_value)
    else if f = opaque_f then nil_value
    else S.value_inhabitant schema (fun _ -> false) f.range
  | _ -> S.value_inhabitant schema (fun _ -> false) f.range

let reversed_arguments : V.arguments bits sigma [bool_s; int_s] =
  assert_norm (V.fields_have_sorts #bits sigma [bool_s; int_s] [V.Scalar bool_s true; V.Scalar int_s false]);
  [V.Scalar bool_s true; V.Scalar int_s false]

(* The harness's quantifier: on (forall, [Int; Bool], Bool) it calls the
   body at the REVERSED typed list [Bool true; Int false]. *)
let other_quantification (k:quantifier_kind) (bound:list sort) (body_sort:sort)
                         (body:V.arguments bits sigma (L.rev bound) -> GTot (V.value bits sigma body_sort))
  : GTot (V.value bits sigma (quant_sort k bound body_sort)) =
  if k = Forall_k && bound = [int_s; bool_s] && body_sort = bool_s then begin
    assert_norm (L.rev [int_s; bool_s] == [bool_s; int_s]);
    body reversed_arguments
  end
  else S.value_inhabitant schema (fun _ -> false) (quant_sort k bound body_sort)

let other : V.interpretation bits sigma = {
  V.application = other_application;
  V.quantification = other_quantification;
}

let booleans : S.boolean_carrier bits = S.Mkboolean_carrier #bits (fun b -> b) (fun b -> b) ()

let interpreted : V.interpretation bits sigma = S.interpretation schema booleans other

(* harness: apply fork.constructor [leaf_bool; leaf_bool] = fork_bool *)
let a2_constructor () : Lemma (interpreted.V.application fork_c [leaf_value; leaf_value] == fork_value) =
  assert_norm (interpreted.V.application fork_c [leaf_value; leaf_value] == fork_value)

(* harness: apply fork.recognizer [fork_bool] = true, apply branch.recognizer [fork_bool] = false *)
let a2_recognizers ()
  : Lemma (interpreted.V.application fork_tester [fork_value] == V.Scalar bool_sort true /\
           interpreted.V.application branch_tester [fork_value] == V.Scalar bool_sort false) =
  assert_norm (interpreted.V.application fork_tester [fork_value] == V.Scalar bool_sort true);
  assert_norm (interpreted.V.application branch_tester [fork_value] == V.Scalar bool_sort false)

(* harness: apply children [branch_bool] = cons_bool (matched field) *)
let a2_matched () : Lemma (interpreted.V.application children [branch_value] == cons_value) =
  assert_norm (interpreted.V.application children [branch_value] == cons_value)

(* harness: apply children [leaf_bool] = nil_bool, [fork_bool] = cons_bool
   (argument-dependent fallback to `other`) *)
let a2_fallback ()
  : Lemma (interpreted.V.application children [leaf_value] == nil_value /\
           interpreted.V.application children [fork_value] == cons_value) =
  assert_norm (interpreted.V.application children [leaf_value] == nil_value);
  assert_norm (interpreted.V.application children [fork_value] == cons_value)

(* harness: apply opaque [fork_bool] = nil_bool (not a datatype operation) *)
let a2_opaque () : Lemma (interpreted.V.application opaque_f [fork_value] == nil_value) =
  assert_norm (interpreted.V.application opaque_f [fork_value] == nil_value)

(* Mutants: wrong recognizer answers, wrong field, wrong fallback argument. *)
let a2_mutants ()
  : Lemma (~(interpreted.V.application fork_tester [fork_value] == V.Scalar bool_sort false) /\
           ~(interpreted.V.application branch_tester [fork_value] == V.Scalar bool_sort true) /\
           ~(interpreted.V.application children [branch_value] == nil_value) /\
           ~(interpreted.V.application children [leaf_value] == cons_value) /\
           ~(interpreted.V.application children [fork_value] == nil_value)) =
  a2_recognizers (); a2_matched (); a2_fallback ();
  assert_norm (~(nil_t == cons_t))

(* The harness's `other` FAILS (failwith "canonical datatype operation
   escaped to the supplied interpretation") on every operation except
   `children` and `opaque`. Here the dispatch path is pinned instead: the
   constructor and the two recognizers are handled by the schema (never by
   `other`), `children` is the schema's matched accessor (so `other` is
   reached only through the fallback for a wrong constructor), and `opaque`
   is no datatype operation (so it reaches `other` directly). *)
let a2_dispatch_paths ()
  : Lemma (L.mem fork_c sigma /\
           not (L.mem fork_tester sigma) /\ not (L.mem branch_tester sigma) /\
           S.find_recognizer fork_tester schema.S.cases == Some fork /\
           S.find_recognizer branch_tester schema.S.cases == Some branch /\
           not (L.mem children sigma) /\ None? (S.find_recognizer children schema.S.cases) /\
           S.find_accessor children schema.S.cases == Some ({ S.matched_case = branch; S.field = 0 }) /\
           not (L.mem opaque_f sigma) /\ None? (S.find_recognizer opaque_f schema.S.cases) /\
           None? (S.find_accessor opaque_f schema.S.cases)) =
  assert_norm (L.mem fork_c sigma /\ not (L.mem fork_tester sigma) /\ not (L.mem branch_tester sigma));
  assert_norm (S.find_recognizer fork_tester schema.S.cases == Some fork);
  assert_norm (S.find_recognizer branch_tester schema.S.cases == Some branch);
  assert_norm (not (L.mem children sigma) /\ None? (S.find_recognizer children schema.S.cases));
  assert_norm (S.find_accessor children schema.S.cases == Some ({ S.matched_case = branch; S.field = 0 }));
  assert_norm (not (L.mem opaque_f sigma) /\ None? (S.find_recognizer opaque_f schema.S.cases) /\
               None? (S.find_accessor opaque_f schema.S.cases))

(* ---------------------------------------------------------------------- *)
(* A3 (harness L1946-1949): V.evaluate goes through the selector dispatch  *)
(* ---------------------------------------------------------------------- *)

let selected : expr = App children [Var 0 tree_s]

let rho : V.environment bits sigma [tree_s] = fun _ -> fork_value

let a3_scoped () : Lemma (D.scoped [tree_s] selected) = assert_norm (D.scoped [tree_s] selected)

let a3_evaluate () : Lemma (D.scoped [tree_s] selected /\ V.evaluate sigma interpreted [tree_s] rho selected == cons_value) =
  a3_scoped ();
  assert_norm (V.evaluate sigma interpreted [tree_s] rho selected == cons_value)

let a3_mutant () : Lemma (D.scoped [tree_s] selected /\ ~(V.evaluate sigma interpreted [tree_s] rho selected == nil_value)) =
  a3_evaluate ();
  assert_norm (~(nil_t == cons_t))

(* ---------------------------------------------------------------------- *)
(* A4 (harness L1912-1930, 1950-1955): the quantifier keeps the supplied  *)
(*     interpretation and binds the REVERSED typed list (de Bruijn)        *)
(* ---------------------------------------------------------------------- *)

let quantified : expr = Quantifier Forall_k [int_s; bool_s] bool_s (Var 0 bool_s)

let empty : V.environment bits sigma [] = fun _ -> FStar.Pervasives.false_elim ()

let a4_scoped () : Lemma (D.scoped [] quantified /\ D.scoped (L.rev [int_s; bool_s] @ []) (Var 0 bool_s)) =
  assert_norm (D.scoped [] quantified);
  assert_norm (D.scoped (L.rev [int_s; bool_s] @ []) (Var 0 bool_s))

(* Inside `other`: the evaluator's body at [Bool true; Int false] is Bool
   true, because Var 0 is the LAST binder (Bool). *)
let a4_body ()
  : Lemma (D.scoped [] quantified /\
           V.evaluate_body sigma interpreted [] empty [int_s; bool_s] (Var 0 bool_s) reversed_arguments ==
           V.Scalar bool_s true) =
  a4_scoped ();
  assert_norm (L.rev [int_s; bool_s] == [bool_s; int_s]);
  let env = V.extend sigma [] (L.rev [int_s; bool_s]) reversed_arguments empty in
  assert_norm (V.extend sigma [] [bool_s; int_s] reversed_arguments empty 0 == V.Scalar bool_s true);
  assert (V.evaluate sigma interpreted (L.rev [int_s; bool_s] @ []) env (Var 0 bool_s) == V.Scalar bool_s true)

let a4_evaluate ()
  : Lemma (D.scoped [] quantified /\ V.evaluate sigma interpreted [] empty quantified == V.Scalar bool_s true) =
  a4_body ();
  assert (V.evaluate sigma interpreted [] empty quantified ==
          other_quantification Forall_k [int_s; bool_s] bool_s
            (V.typed_body sigma [int_s; bool_s] bool_s
              (V.evaluate_body sigma interpreted [] empty [int_s; bool_s] (Var 0 bool_s))))

(* Mutants: the value is not false, and not the first binder's (Int false)
   value, which a non-reversed binding would have read. *)
let a4_mutants ()
  : Lemma (D.scoped [] quantified /\
           ~(V.evaluate sigma interpreted [] empty quantified == V.Scalar bool_s false) /\
           ~(V.evaluate sigma interpreted [] empty quantified == V.Scalar int_s false)) =
  a4_evaluate ()
