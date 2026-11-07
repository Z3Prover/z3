module Z3SortedProofTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module DT = Z3SortedDatatype
module K = Z3SortedProof
module U = Z3UnifiedProof
module P = Z3ProofDocument
module R = Z3ResolutionProofTheory
module BR = Z3BooleanRewrite
module Tac = FStar.Tactics.V2
module LA = Z3LinearArithmeticAst
module AR = Z3SortedArithmetic

let box = BaseSort "Box"
let integer = (SortApp IntSymbol [])

let primitive (s:sort) : Type0 =
  match s with (SortApp IntSymbol []) -> int | (SortApp BoolSymbol []) -> bool | _ -> unit

let primitive_default (s:sort) : primitive s =
  match s with (SortApp IntSymbol []) -> 0 | (SortApp BoolSymbol []) -> false | _ -> ()

let primitive_equal (s:sort) (x y:primitive s) : bool =
  match s with (SortApp IntSymbol []) -> x = y | (SortApp BoolSymbol []) -> x = y | _ -> true

let equality : T.scalar_model primitive =
  { T.reflection = T.Mkscalar_equality #primitive primitive_equal ();
    integers = Z3SortedInteger.Mkcarrier #primitive (fun n -> n) (fun n -> n) () }

let booleans : S.boolean_carrier primitive =
  S.Mkboolean_carrier #primitive (fun b -> b) (fun b -> b) ()

let empty = {
  decl_name = "empty"; domain = []; range = box; interp = Some 200; int_params = [0; 0; 0];
}
let pair = {
  decl_name = "pair"; domain = [integer; bool_sort]; range = box;
  interp = Some 200; int_params = [0; 1; 2];
}
let is_empty = {
  decl_name = "is-empty"; domain = [box]; range = bool_sort; interp = Some 201; int_params = [0; 0];
}
let is_pair = {
  decl_name = "is-pair"; domain = [box]; range = bool_sort; interp = Some 201; int_params = [0; 1];
}
let number = {
  decl_name = "number"; domain = [box]; range = integer; interp = Some 202; int_params = [0; 1; 0];
}
let flag = {
  decl_name = "flag"; domain = [box]; range = bool_sort; interp = Some 202; int_params = [0; 1; 1];
}

#push-options "--fuel 6 --ifuel 2"

let schema : S.checked_schema =
  let s = {
    S.sorts = [box];
    cases = [
      { S.constructor = empty; recognizer = is_empty; accessors = [] };
      { S.constructor = pair; recognizer = is_pair; accessors = [number; flag] }];
  } in
  assert_norm (S.valid s);
  s

let model : V.interpretation primitive (S.signature schema) =
  T.interpretation #primitive schema booleans equality
    (S.default_interpretation #primitive schema primitive_default)

let shifted_integers : T.scalar_model primitive = {
  equality with integers = Z3SortedInteger.Mkcarrier #primitive
    (fun n -> n + 17) (fun n -> n - 17) () }

let integer_literal (n:int) = App {
  decl_name = "integer"; domain = []; range = integer;
  interp = Some Z3ValueTheory.op_num_rational; int_params = [n; 1] } []

let integer_addition = App {
  decl_name = "+"; domain = [integer; integer]; range = integer;
  interp = Some Z3ValueTheory.op_arith_add; int_params = [] }
  [integer_literal 2; integer_literal 3]

let integer_semantics_is_not_the_carrier_representation ()
  : Lemma (T.evaluate schema booleans shifted_integers
      (S.default_interpretation #primitive schema primitive_default) integer_addition ==
      V.Scalar integer 22) =
  assert (T.evaluate schema booleans shifted_integers
    (S.default_interpretation #primitive schema primitive_default) integer_addition ==
    V.Scalar integer 22) by
    (Tac.norm [nbe; delta; iota; zeta; primops]; Tac.trivial ())

let integer_sort_cannot_be_a_datatype ()
  : Lemma (not (S.valid {
      S.sorts = [integer];
      cases = [{ S.constructor = { empty with range = integer };
                 recognizer = { is_empty with domain = [integer] };
                 accessors = [] }] })) =
  assert_norm (not (S.valid {
    S.sorts = [integer];
    cases = [{ S.constructor = { empty with range = integer };
               recognizer = { is_empty with domain = [integer] };
               accessors = [] }] }))

let chain = BaseSort "Chain"
let chain_empty : func_decl = {
  decl_name = "chain-empty"; domain = []; range = chain;
  interp = Some 200; int_params = [1; 0; 0];
}
let chain_link : func_decl = {
  decl_name = "chain-link"; domain = [chain; chain]; range = chain;
  interp = Some 200; int_params = [1; 1; 2];
}
let chain_is_empty : func_decl = {
  decl_name = "chain-is-empty"; domain = [chain]; range = bool_sort;
  interp = Some 201; int_params = [1; 0];
}
let chain_is_link : func_decl = {
  decl_name = "chain-is-link"; domain = [chain]; range = bool_sort;
  interp = Some 201; int_params = [1; 1];
}
let chain_head : func_decl = {
  decl_name = "chain-head"; domain = [chain]; range = chain;
  interp = Some 202; int_params = [1; 1; 0];
}
let chain_tail : func_decl = {
  decl_name = "chain-tail"; domain = [chain]; range = chain;
  interp = Some 202; int_params = [1; 1; 1];
}

let chain_schema : S.checked_schema =
  let s = {
    S.sorts = [chain];
    cases = [
      { S.constructor = chain_empty; recognizer = chain_is_empty; accessors = [] };
      { S.constructor = chain_link; recognizer = chain_is_link; accessors = [chain_head; chain_tail] }];
  } in
  assert_norm (S.valid s);
  s

let chain_x = App {
  decl_name = "chain-x"; domain = []; range = chain; interp = None; int_params = [];
} []
let chain_y = App {
  decl_name = "chain-y"; domain = []; range = chain; interp = None; int_params = [];
} []
let chain_nil = App chain_empty []
let chain_cycle = App chain_link [chain_nil; chain_x]

let checked_direct_constructor_cycles ()
  : Lemma (K.cyclic_conflict chain_schema [R.mk_eq_expr chain_cycle chain_x] /\
           K.cyclic_conflict chain_schema [R.true_expr; R.mk_eq_expr chain_x chain_cycle] /\
           K.cyclic_conflict chain_schema [R.mk_eq_expr chain_x (App chain_link [chain_x; chain_nil])] /\
           K.direct_consequence chain_schema [R.mk_eq_expr chain_cycle chain_x] R.false_expr) =
  assert_norm (K.cyclic_conflict chain_schema [R.mk_eq_expr chain_cycle chain_x]);
  assert_norm (K.cyclic_conflict chain_schema [R.true_expr; R.mk_eq_expr chain_x chain_cycle]);
  assert_norm (K.cyclic_conflict chain_schema [R.mk_eq_expr chain_x (App chain_link [chain_x; chain_nil])]);
  assert_norm (K.direct_consequence chain_schema [R.mk_eq_expr chain_cycle chain_x] R.false_expr)

let rejected_constructor_cycle_lookalikes ()
  : Lemma (
    not (K.cyclic_conflict chain_schema []) /\
    not (K.cyclic_conflict chain_schema [R.mk_eq_expr chain_x (App chain_link [chain_nil; chain_y])]) /\
    not (K.cyclic_conflict chain_schema [R.mk_eq_expr chain_x
      (App { chain_link with decl_name = "opaque-link" } [chain_nil; chain_x])]) /\
    not (K.cyclic_conflict chain_schema [App { (R.eq_decl chain) with interp = None }
      [chain_x; chain_cycle]]) /\
    not (K.cyclic_conflict chain_schema [R.mk_eq_expr (Var 0 chain) (App chain_link [chain_nil; Var 0 chain])])) =
  assert_norm (not (K.cyclic_conflict chain_schema []));
  assert_norm (not (K.cyclic_conflict chain_schema [R.mk_eq_expr chain_x (App chain_link [chain_nil; chain_y])]));
  assert_norm (not (K.cyclic_conflict chain_schema [R.mk_eq_expr chain_x
    (App { chain_link with decl_name = "opaque-link" } [chain_nil; chain_x])]));
  assert_norm (not (K.cyclic_conflict chain_schema [App { (R.eq_decl chain) with interp = None }
    [chain_x; chain_cycle]]));
  assert_norm (not (K.cyclic_conflict chain_schema [R.mk_eq_expr (Var 0 chain)
    (App chain_link [chain_nil; Var 0 chain])]))

let opaque_array = ArraySort [box] integer

let all_result_sorts_are_inhabited ()
  : Lemma (ensures V.has_sort #primitive (S.signature schema) opaque_array
    ((S.default_interpretation #primitive schema primitive_default).application
      { decl_name = "array"; domain = []; range = opaque_array; interp = None; int_params = [] } [])) =
  assert_norm (not (V.datatype_sort (S.signature schema) opaque_array))

let x : expr = App {
  decl_name = "x"; domain = []; range = box; interp = None; int_params = [];
} []
let y : expr = App {
  decl_name = "y"; domain = []; range = box; interp = None; int_params = [];
} []

let disjunction (es:list expr) = App (BR.connective_decl BR.Disjunction es) es
let exhaustive = disjunction [App is_empty [x]; App is_pair [x]]
let reconstruction =
  disjunction [R.mk_not_expr (App is_pair [x]);
    R.mk_eq_expr x (App pair [App number [x]; App flag [x]])]

let checked_datatype_laws ()
  : Lemma (ensures DT.consequence schema [] exhaustive /\
                   DT.consequence schema [] reconstruction /\
                   not (DT.consequence schema []
                     (R.mk_eq_expr x (App pair [App number [x]; App flag [x]]))) /\
                   not (DT.consequence schema [App is_pair [x]]
                     (R.mk_eq_expr x (App pair [App number [y]; App flag [x]])))) =
  assert_norm (DT.consequence schema [] exhaustive);
  assert_norm (DT.consequence schema [] reconstruction);
  assert_norm (not (DT.consequence schema []
    (R.mk_eq_expr x (App pair [App number [x]; App flag [x]]))));
  assert_norm (not (DT.consequence schema [App is_pair [x]]
    (R.mk_eq_expr x (App pair [App number [y]; App flag [x]]))))

let no_empty = R.mk_not_expr (App is_empty [x])
let no_pair = R.mk_not_expr (App is_pair [x])

let choice = {
  decl_name = "if"; domain = [bool_sort; box; box]; range = box;
  interp = Some Z3ValueTheory.op_ite; int_params = [];
}

let rec wide_clause (n:nat) : Tot (list expr) (decreases n) =
  if n = 0 then []
  else App {
    decl_name = "bit"; domain = []; range = bool_sort; interp = None; int_params = [n];
  } [] :: wide_clause (n - 1)

let shared = disjunction (wide_clause 14)

let conditional_term_normalizes ()
  : Lemma (DT.normalize schema 64 (App choice [R.false_expr; x; y]) == Some y) =
  assert_norm (DT.normalize schema 64 (App choice [R.false_expr; x; y]) == Some y)

let shared_boolean_fact_propagates ()
  : Lemma (DT.boolean_consequence
    [shared; R.mk_eq_expr shared (App is_empty [x])] (App is_empty [x])) =
  assert_norm (DT.boolean_consequence
    [shared; R.mk_eq_expr shared (App is_empty [x])] (App is_empty [x]))

let unrelated_boolean_fact_is_rejected ()
  : Lemma (not (DT.boolean_consequence [shared] (App is_empty [x]))) =
  assert (not (DT.boolean_consequence [shared] (App is_empty [x]))) by
    (Tac.norm [nbe; delta; iota; zeta; primops];
     Tac.trivial ())

[@@expect_failure]
let nbe_normalization_rejects_unrelated_boolean_fact ()
  : Lemma (DT.boolean_consequence [shared] (App is_empty [x])) =
  assert (DT.boolean_consequence [shared] (App is_empty [x])) by
    (Tac.norm [nbe; delta; iota; zeta; primops];
     Tac.trivial ())

let conditional_and_shared_boolean_facts ()
  : Lemma (ensures DT.normalize schema 64 (App choice [R.false_expr; x; y]) == Some y /\
                   DT.boolean_consequence
                     [shared; R.mk_eq_expr shared (App is_empty [x])] (App is_empty [x]) /\
                   not (DT.boolean_consequence [shared] (App is_empty [x])))
  =
  conditional_term_normalizes ();
  shared_boolean_fact_propagates ();
  unrelated_boolean_fact_is_rejected ()

let direct_resolution_checks_actual_units ()
  : Lemma (ensures
      DT.simple_consequence
        [disjunction [App is_empty [x]; App is_pair [y]]; no_empty] (App is_pair [y]) /\
      not (DT.simple_consequence
        [disjunction [App is_empty [x]; App is_pair [y]]; no_pair] (App is_pair [y]))) =
  assert_norm (DT.simple_consequence
    [disjunction [App is_empty [x]; App is_pair [y]]; no_empty] (App is_pair [y]));
  assert_norm (not (DT.simple_consequence
    [disjunction [App is_empty [x]; App is_pair [y]]; no_pair] (App is_pair [y])))

let canonical_hypothesis_discharge ()
  : Lemma (ensures
      K.remaining_hypotheses [App is_empty [x]] no_empty == [] /\
      K.remaining_hypotheses [App is_empty [x]] no_pair == [App is_empty [x]] /\
      K.remaining_hypotheses [R.mk_not_expr exhaustive] exhaustive == [] /\
      K.remaining_hypotheses [App is_empty [x]]
        (App { R.not_decl with interp = None } [App is_empty [x]]) == [App is_empty [x]]) =
  assert_norm (K.remaining_hypotheses [App is_empty [x]] no_empty == []);
  assert_norm (K.remaining_hypotheses [App is_empty [x]] no_pair == [App is_empty [x]]);
  assert_norm (K.remaining_hypotheses [R.mk_not_expr exhaustive] exhaustive == []);
  assert_norm (K.remaining_hypotheses [App is_empty [x]]
    (App { R.not_decl with interp = None } [App is_empty [x]]) == [App is_empty [x]])

let equality_symmetry_is_derived ()
  : Lemma (ensures
      DT.consequence schema [] (R.mk_eq_expr (R.mk_eq_expr x y) (R.mk_eq_expr y x)) /\
      not (DT.consequence schema [] (R.mk_eq_expr (R.mk_eq_expr x y) (R.mk_eq_expr x x)))) =
  assert_norm (DT.consequence schema [] (R.mk_eq_expr (R.mk_eq_expr x y) (R.mk_eq_expr y x)));
  assert_norm (not (DT.consequence schema [] (R.mk_eq_expr (R.mk_eq_expr x y) (R.mk_eq_expr x x))))

let exhaustive_document : P.document = {
  declarations = []; expressions = [];
  assertions = [no_empty; no_pair];
  entries = [
    { P.rule = U.Asserted; formula = no_empty; premise_ids = [] };
    { P.rule = U.Asserted; formula = no_pair; premise_ids = [] };
    { P.rule = U.Unverified "th-lemma"; formula = exhaustive; premise_ids = [] };
    { P.rule = U.UnitResolution; formula = R.false_expr; premise_ids = [0; 1; 2] }];
  root = 3;
}

let original_inputs_and_exhaustiveness ()
  : Lemma (ensures K.check_document schema exhaustive_document == Some 0 /\
                   K.check_document schema { exhaustive_document with assertions = [no_empty] } == None /\
                   K.check_document schema { exhaustive_document with entries = [
                     { P.rule = U.Unverified "th-lemma"; formula = R.false_expr; premise_ids = [] }];
                     root = 0 } == Some 1) =
  assert_norm (K.check_document schema exhaustive_document == Some 0);
  assert_norm (K.check_document schema { exhaustive_document with assertions = [no_empty] } == None);
  assert_norm (K.check_document schema { exhaustive_document with entries = [
    { P.rule = U.Unverified "th-lemma"; formula = R.false_expr; premise_ids = [] }];
    root = 0 } == Some 1)

let certified_document_has_no_model (#base:sort -> Type0) (bc:S.boolean_carrier base)
                                   (eq:T.scalar_model base)
                                   (other:V.interpretation base (S.signature schema))
  : Lemma (ensures not (T.truths schema bc eq other exhaustive_document.assertions)) =
  original_inputs_and_exhaustiveness ();
  assert_norm (not (K.needs_real_semantics schema exhaustive_document.entries));
  K.lemma_check_document schema bc eq other exhaustive_document

let equality_exclusion_document : P.document = {
  declarations = []; expressions = [];
  assertions = [no_pair; R.mk_eq_expr x y; R.mk_not_expr (App is_empty [y])];
  entries = [
    { P.rule = U.Asserted; formula = no_pair; premise_ids = [] };
    { P.rule = U.Asserted; formula = R.mk_eq_expr x y; premise_ids = [] };
    { P.rule = U.Asserted; formula = R.mk_not_expr (App is_empty [y]); premise_ids = [] };
    { P.rule = U.Unverified "th-lemma"; formula = App is_empty [y]; premise_ids = [0; 1] };
    { P.rule = U.UnitResolution; formula = R.false_expr; premise_ids = [3; 2] }];
  root = 4;
}

let equality_recognizer_propagation ()
  : Lemma (ensures K.check_document schema equality_exclusion_document == Some 0 /\
      K.check_document schema { equality_exclusion_document with entries = [
        { P.rule = U.Asserted; formula = no_pair; premise_ids = [] };
        { P.rule = U.Asserted; formula = R.mk_not_expr (App is_empty [y]); premise_ids = [] };
        { P.rule = U.Unverified "th-lemma"; formula = App is_empty [y]; premise_ids = [0] };
        { P.rule = U.UnitResolution; formula = R.false_expr; premise_ids = [2; 1] }];
        root = 3 } == Some 1) =
  assert_norm (K.check_document schema equality_exclusion_document == Some 0);
  assert_norm (K.check_document schema { equality_exclusion_document with entries = [
    { P.rule = U.Asserted; formula = no_pair; premise_ids = [] };
    { P.rule = U.Asserted; formula = R.mk_not_expr (App is_empty [y]); premise_ids = [] };
    { P.rule = U.Unverified "th-lemma"; formula = App is_empty [y]; premise_ids = [0] };
    { P.rule = U.UnitResolution; formula = R.false_expr; premise_ids = [2; 1] }];
    root = 3 } == Some 1)

let constructor_conflict_document : P.document = {
  declarations = []; expressions = [];
  assertions = [no_pair; R.mk_eq_expr (App pair [App number [x]; App flag [x]]) x];
  entries = [
    { P.rule = U.Asserted; formula = no_pair; premise_ids = [] };
    { P.rule = U.Asserted;
      formula = R.mk_eq_expr (App pair [App number [x]; App flag [x]]) x; premise_ids = [] };
    { P.rule = U.Unverified "th-lemma"; formula = R.false_expr; premise_ids = [0; 1] }];
  root = 2;
}

let constructor_equality_conflict ()
  : Lemma (ensures K.check_document schema constructor_conflict_document == Some 0) =
  assert_norm (K.check_document schema constructor_conflict_document == Some 0)

let core_schema : S.checked_schema =
  let s = { S.sorts = []; cases = [] } in
  assert_norm (S.valid s);
  s

let core_model : V.interpretation primitive (S.signature core_schema) =
  T.interpretation #primitive core_schema booleans equality
    (S.default_interpretation #primitive core_schema primitive_default)

let proposition : expr = App {
  decl_name = "p"; domain = []; range = bool_sort; interp = None; int_params = [];
} []

let core_document : P.document = {
  declarations = []; expressions = [];
  assertions = [proposition; R.mk_not_expr proposition];
  entries = [
    { P.rule = U.Asserted; formula = proposition; premise_ids = [] };
    { P.rule = U.Asserted; formula = R.mk_not_expr proposition; premise_ids = [] };
    { P.rule = U.UnitResolution; formula = R.false_expr; premise_ids = [0; 1] }];
  root = 2;
}

let core_refutation_without_legacy_contracts (#base:sort -> Type0) (bc:S.boolean_carrier base)
                                             (eq:T.scalar_model base)
                                             (other:V.interpretation base (S.signature core_schema))
  : Lemma (ensures K.check_document core_schema core_document == Some 0 /\
                   not (T.truths core_schema bc eq other core_document.assertions)) =
  assert_norm (K.check_document core_schema core_document == Some 0);
  assert_norm (not (K.needs_real_semantics core_schema core_document.entries));
  K.lemma_check_document core_schema bc eq other core_document

(* Independently constructed bodies: declaration-order blocks flatten as
   outer @ inner, whereas the de Bruijn scope is rev inner @ rev outer. *)
let pull_body = App {
  decl_name = "pull-relation"; domain = [box; bool_sort; integer]; range = bool_sort;
  interp = None; int_params = [];
} [Var 2 box; Var 1 bool_sort; Var 0 integer]

let pull_nested =
  Quantifier Forall_k [box] bool_sort
    (Quantifier Forall_k [bool_sort; integer] bool_sort pull_body)

let pull_flat = Quantifier Forall_k [box; bool_sort; integer] bool_sort pull_body

let pull_boolean_body = R.mk_eq_expr
  (App { decl_name = "pull-boolean"; domain = [bool_sort; bool_sort]; range = bool_sort;
         interp = None; int_params = [] } [Var 1 bool_sort; Var 0 bool_sort])
  (Var 1 bool_sort)

let pull_boolean_nested =
  Quantifier Forall_k [bool_sort] bool_sort
    (Quantifier Forall_k [bool_sort] bool_sort pull_boolean_body)

let pull_boolean_flat =
  Quantifier Forall_k [bool_sort; bool_sort] bool_sort pull_boolean_body

let pull_node (a b:expr) : U.proof_node = {
  U.kind = U.PullQuantifier; conclusion = U.Equal a b; premises = [];
}

let checked_sorted_quantifier_flattening ()
  : Lemma (ensures
      K.check_node schema [] (pull_node pull_nested pull_flat) ==
        Some ({ U.conclusion = U.Equal pull_nested pull_flat; hypotheses = [] }, 0) /\
      K.check_node schema [] (pull_node pull_boolean_nested pull_boolean_flat) ==
        Some ({ U.conclusion = U.Equal pull_boolean_nested pull_boolean_flat; hypotheses = [] }, 0) /\
      Z3SortedQuantifier.check_flatten (R.mk_eq_expr pull_flat pull_nested)) =
  assert_norm (K.check_node schema [] (pull_node pull_nested pull_flat) ==
    Some ({ U.conclusion = U.Equal pull_nested pull_flat; hypotheses = [] }, 0));
  assert_norm (K.check_node schema [] (pull_node pull_boolean_nested pull_boolean_flat) ==
    Some ({ U.conclusion = U.Equal pull_boolean_nested pull_boolean_flat; hypotheses = [] }, 0));
  assert_norm (Z3SortedQuantifier.check_flatten (R.mk_eq_expr pull_flat pull_nested))

let rejected_sorted_quantifier_flattening ()
  : Lemma (ensures
      not (Z3SortedQuantifier.check_flatten (R.mk_eq_expr pull_nested
        (Quantifier Forall_k [bool_sort; integer; box] bool_sort pull_body))) /\
      not (Z3SortedQuantifier.check_flatten (R.mk_eq_expr pull_boolean_nested
        (Quantifier Forall_k [bool_sort; bool_sort] bool_sort
          (R.mk_eq_expr (Var 0 bool_sort) (Var 1 bool_sort))))) /\
      not (Z3SortedQuantifier.check_flatten (R.mk_eq_expr pull_nested
        (Quantifier Exists_k [box; bool_sort; integer] bool_sort pull_body))) /\
      not (Z3SortedQuantifier.check_flatten (R.mk_eq_expr
        (Quantifier Forall_k [bool_sort] bool_sort
          (Quantifier Forall_k [bool_sort] bool_sort (Var 2 bool_sort)))
        (Quantifier Forall_k [bool_sort; bool_sort] bool_sort (Var 2 bool_sort))))) =
  assert_norm (not (Z3SortedQuantifier.check_flatten (R.mk_eq_expr pull_nested
    (Quantifier Forall_k [bool_sort; integer; box] bool_sort pull_body))));
  assert_norm (not (Z3SortedQuantifier.check_flatten (R.mk_eq_expr pull_boolean_nested
    (Quantifier Forall_k [bool_sort; bool_sort] bool_sort
      (R.mk_eq_expr (Var 0 bool_sort) (Var 1 bool_sort))))));
  assert_norm (not (Z3SortedQuantifier.check_flatten (R.mk_eq_expr pull_nested
    (Quantifier Exists_k [box; bool_sort; integer] bool_sort pull_body))));
  assert_norm (not (Z3SortedQuantifier.check_flatten (R.mk_eq_expr
    (Quantifier Forall_k [bool_sort] bool_sort
      (Quantifier Forall_k [bool_sort] bool_sort (Var 2 bool_sort)))
    (Quantifier Forall_k [bool_sort; bool_sort] bool_sort (Var 2 bool_sort)))))

let sorted_flattening_semantics (#base:sort -> Type0) (bc:S.boolean_carrier base)
                               (eq:T.scalar_model base)
                               (other:V.interpretation base (S.signature schema))
  : Lemma (requires Z3SortedQuantifier.forall_model schema bc other)
          (ensures T.truth schema bc eq other (R.mk_eq_expr pull_nested pull_flat)) =
  assert_norm (Z3SortedQuantifier.check_flatten (R.mk_eq_expr pull_nested pull_flat));
  Z3SortedQuantifier.lemma_check_flatten schema bc eq other (R.mk_eq_expr pull_nested pull_flat)

(* ---------------------------------------------------------------------- *)
(* Int equality/order laws (triangle clauses and implied equalities)        *)
(* ---------------------------------------------------------------------- *)

(* Int terms: the producer's binary + and * (op_plus, op_mul), opaque
   Int-valued applications and a nonconstant product of them. *)
let universe = BaseSort "Universe"
let ulevel : func_decl = {
  decl_name = "ulevel"; domain = [universe]; range = integer; interp = None; int_params = [];
}
let level (name:string) : expr =
  App ulevel [App { decl_name = name; domain = []; range = universe; interp = None; int_params = [] } []]
let la = level "a"
let lb = level "b"

let x_decl : func_decl = { decl_name = "x"; domain = []; range = integer; interp = None; int_params = [] }
let xi = App x_decl []
let yi = App { x_decl with decl_name = "y" } []
let zi = App { x_decl with decl_name = "z" } []
(* Spelled like x, a different declaration. *)
let x_twin = App { x_decl with int_params = [1] } []

let int_operator (name:string) (tag:decl_kind) (range:sort) : func_decl =
  { decl_name = name; domain = [integer; integer]; range = range; interp = Some tag; int_params = [] }
let iadd = int_operator "+" Z3ValueTheory.op_plus integer
let imul = int_operator "*" Z3ValueTheory.op_mul integer
let ile = int_operator "<=" Z3ValueTheory.op_arith_le bool_sort
let ige = int_operator ">=" Z3ValueTheory.op_arith_ge bool_sort
let ilt = int_operator "<" Z3ValueTheory.op_arith_lt bool_sort

let izero = integer_literal 0
let ione = integer_literal 1
let minus (a b:expr) : expr = App iadd [a; App imul [integer_literal (-1); b]]
let leq (a b:expr) : expr = App ile [a; b]
let geq (a b:expr) : expr = App ige [a; b]
let not_eq (a b:expr) : expr = R.mk_not_expr (R.mk_eq_expr a b)

let product = App imul [la; lb]
let span = minus la lb
let gap = minus product la

(* The actual clause shapes: Pulse.Lib.Raise q5 (1 = S with S <= 1 and
   S >= 1, S a sum), difference forms of a nonconstant product against an
   opaque application in either equality orientation and literal order, and
   the antisymmetry clause in two literal orders. *)
let raise_le = disjunction [not_eq ione span; leq span ione]
let raise_ge = disjunction [not_eq ione span; geq span ione]
let gap_ge = disjunction [not_eq product la; geq gap izero]
let gap_le_reversed = disjunction [leq gap izero; not_eq la product]
let antisymmetry = disjunction [R.mk_eq_expr product la; R.mk_not_expr (leq gap izero); R.mk_not_expr (geq gap izero)]
let antisymmetry_permuted =
  disjunction [R.mk_not_expr (geq gap izero); R.mk_eq_expr product la; R.mk_not_expr (leq gap izero)]

let checked_int_order_laws ()
  : Lemma (K.order_clause raise_le /\ K.order_clause raise_ge /\ K.order_clause gap_ge /\
           K.order_clause gap_le_reversed /\ K.order_clause antisymmetry /\
           K.order_clause antisymmetry_permuted /\
           K.order_equation [geq gap izero; leq gap izero] (R.mk_eq_expr product la) /\
           K.order_equation [leq gap izero; R.true_expr; geq gap izero] (R.mk_eq_expr la product) /\
           K.order_equation [geq gap izero; leq gap izero] (R.mk_eq_expr izero gap) /\
           K.consequence core_schema [] raise_le /\
           K.consequence core_schema [geq gap izero; leq gap izero] (R.mk_eq_expr product la)) =
  assert_norm (K.order_clause raise_le /\ K.order_clause raise_ge /\ K.order_clause gap_ge /\
               K.order_clause gap_le_reversed /\ K.order_clause antisymmetry /\
               K.order_clause antisymmetry_permuted);
  assert_norm (K.order_equation [geq gap izero; leq gap izero] (R.mk_eq_expr product la) /\
               K.order_equation [leq gap izero; R.true_expr; geq gap izero] (R.mk_eq_expr la product) /\
               K.order_equation [geq gap izero; leq gap izero] (R.mk_eq_expr izero gap));
  assert_norm (K.consequence core_schema [] raise_le);
  assert_norm (K.consequence core_schema [geq gap izero; leq gap izero] (R.mk_eq_expr product la))

(* The generic theorem at one instance: in EVERY Sorted model (any carrier,
   scalar model and interpretation) the Raise clause holds, and the two
   opposite bounds give the equation. *)
let int_order_laws_hold (#base:sort -> Type0) (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                        (other:V.interpretation base (S.signature core_schema))
  : Lemma (T.truth core_schema bc eq other raise_le /\
           (T.truths core_schema bc eq other [geq gap izero; leq gap izero] ==>
            T.truth core_schema bc eq other (R.mk_eq_expr product la))) =
  checked_int_order_laws ();
  K.lemma_consequence core_schema bc eq other [] raise_le;
  if T.truths core_schema bc eq other [geq gap izero; leq gap izero] then
    K.lemma_consequence core_schema bc eq other [geq gap izero; leq gap izero] (R.mk_eq_expr product la)

(* False variants, each refused by the executable checks. *)
let strict_mutant = disjunction [not_eq xi yi; App ilt [xi; yi]]
let plus_one_mutant = disjunction [not_eq xi yi; leq (App iadd [xi; App imul [ione; yi]]) izero]
let wrong_operand_mutant = disjunction [not_eq xi yi; geq (minus xi zi) izero]
let twin_mutant = disjunction [not_eq xi yi; leq (minus x_twin yi) izero]
let counterfeit_le_mutant = disjunction [not_eq xi yi; App ({ ile with interp = None }) [xi; yi]]
let counterfeit_add_mutant =
  disjunction [not_eq xi yi; leq (App ({ iadd with interp = Some Z3ValueTheory.op_mul }) [xi; App imul [integer_literal (-1); yi]]) izero]
let same_bounds_mutant = disjunction [R.mk_eq_expr xi yi; R.mk_not_expr (geq (minus xi yi) izero);
                                      R.mk_not_expr (leq (minus yi xi) izero)]

let refused_int_order_mutants ()
  : Lemma (not (K.order_clause strict_mutant) /\ not (K.order_clause plus_one_mutant) /\
           not (K.order_clause wrong_operand_mutant) /\ not (K.order_clause twin_mutant) /\
           not (K.order_clause counterfeit_le_mutant) /\ not (K.order_clause counterfeit_add_mutant) /\
           not (K.order_clause same_bounds_mutant) /\
           not (K.order_equation [geq (minus xi yi) izero] (R.mk_eq_expr xi yi)) /\
           not (K.order_equation [geq (minus xi yi) izero; leq (minus yi xi) izero] (R.mk_eq_expr xi yi)) /\
           not (K.direct_consequence core_schema [] strict_mutant) /\
           not (K.direct_consequence core_schema [geq (minus xi yi) izero] (R.mk_eq_expr xi yi))) =
  assert_norm (not (K.order_clause strict_mutant) /\ not (K.order_clause plus_one_mutant) /\
               not (K.order_clause wrong_operand_mutant) /\ not (K.order_clause twin_mutant) /\
               not (K.order_clause counterfeit_le_mutant) /\ not (K.order_clause counterfeit_add_mutant) /\
               not (K.order_clause same_bounds_mutant));
  assert_norm (not (K.order_equation [geq (minus xi yi) izero] (R.mk_eq_expr xi yi)) /\
               not (K.order_equation [geq (minus xi yi) izero; leq (minus yi xi) izero] (R.mk_eq_expr xi yi)));
  assert_norm (not (K.direct_consequence core_schema [] strict_mutant));
  assert_norm (not (K.direct_consequence core_schema [geq (minus xi yi) izero] (R.mk_eq_expr xi yi)))

(* Opposite-value counter-models in concrete Sorted models (Int scalars,
   every free Int-valued symbol 0 unless chosen otherwise): each false
   variant is false there, so certifying it would contradict
   K.lemma_check_document. *)
let valued (pick:func_decl -> option int) : V.interpretation primitive (S.signature core_schema) = {
  V.application = (fun f _ ->
    match pick f with
    | Some n -> if f.range = integer then V.Scalar integer n
                else S.value_inhabitant core_schema primitive_default f.range
    | None -> S.value_inhabitant core_schema primitive_default f.range);
  V.quantification = (S.default_interpretation #primitive core_schema primitive_default).V.quantification;
}

let ones (f:func_decl) : option int = if f.range = integer then Some 1 else None
let nothing (f:func_decl) : option int = None
let twin_one (f:func_decl) : option int = if f = { x_decl with int_params = [1] } then Some 1 else None
let z_one (f:func_decl) : option int = if f.decl_name = "z" then Some 1 else None
let x_one (f:func_decl) : option int = if f = x_decl then Some 1 else None
let counterfeit_one (f:func_decl) : option int =
  if f = { iadd with interp = Some Z3ValueTheory.op_mul } then Some 1 else None

let int_order_counter_models ()
  : Lemma (T.truth core_schema booleans equality (valued nothing) strict_mutant == false /\
           T.truth core_schema booleans equality (valued ones) plus_one_mutant == false /\
           T.truth core_schema booleans equality (valued z_one) wrong_operand_mutant == false /\
           T.truth core_schema booleans equality (valued twin_one) twin_mutant == false /\
           T.truth core_schema booleans equality (valued nothing) counterfeit_le_mutant == false /\
           T.truth core_schema booleans equality (valued x_one) same_bounds_mutant == false /\
           T.truth core_schema booleans equality (valued counterfeit_one) counterfeit_add_mutant == false /\
           T.truth core_schema booleans equality (valued x_one) (geq (minus xi yi) izero) == true /\
           T.truth core_schema booleans equality (valued x_one) (R.mk_eq_expr xi yi) == false) =
  assert (T.truth core_schema booleans equality (valued nothing) strict_mutant == false /\
          T.truth core_schema booleans equality (valued ones) plus_one_mutant == false /\
          T.truth core_schema booleans equality (valued z_one) wrong_operand_mutant == false /\
          T.truth core_schema booleans equality (valued twin_one) twin_mutant == false /\
          T.truth core_schema booleans equality (valued nothing) counterfeit_le_mutant == false /\
          T.truth core_schema booleans equality (valued x_one) same_bounds_mutant == false /\
          T.truth core_schema booleans equality (valued counterfeit_one) counterfeit_add_mutant == false /\
          T.truth core_schema booleans equality (valued x_one) (geq (minus xi yi) izero) == true /\
          T.truth core_schema booleans equality (valued x_one) (R.mk_eq_expr xi yi) == false) by
    (Tac.norm [nbe; delta; iota; zeta; primops]; Tac.trivial ())

(* ---------------------------------------------------------------------- *)
(* Term if-then-else branch clauses                                         *)
(* ---------------------------------------------------------------------- *)

(* Raise q5's term choice over the uninterpreted sort Universe (its
   condition an Int bound on ulevel(b) + (-1) * ulevel(a)), and Int choices
   of the numerals 1 and 0 under an opaque Boolean p. *)
let universe_decl (name:string) : func_decl =
  { decl_name = name; domain = []; range = universe; interp = None; int_params = [] }
let ua = App (universe_decl "a") []
let ub = App (universe_decl "b") []
let raise_guard = geq (minus lb la) izero
let raise_le_guard = leq (minus lb la) izero
let universe_choice (c:expr) (t u:expr) : expr = App (T.ite_decl universe) [c; t; u]
let int_choice (c:expr) (t u:expr) : expr = App (T.ite_decl integer) [c; t; u]

let p_decl : func_decl = { decl_name = "p"; domain = []; range = bool_sort; interp = None; int_params = [] }
let pb = App p_decl []
let qb = App { p_decl with decl_name = "q" } []

let ite_then = disjunction [R.mk_not_expr raise_guard; R.mk_eq_expr ub (universe_choice raise_guard ub ua)]
let ite_else = disjunction [raise_guard; R.mk_eq_expr ua (universe_choice raise_guard ub ua)]
let ite_then_le = disjunction [R.mk_not_expr raise_le_guard; R.mk_eq_expr ua (universe_choice raise_le_guard ua ub)]
let ite_int_then_reversed = disjunction [R.mk_not_expr pb; R.mk_eq_expr (int_choice pb ione izero) ione]
let ite_int_else_swapped = disjunction [R.mk_eq_expr (int_choice pb ione izero) izero; pb]
(* A negated condition: its then-branch literal is the condition's atom. *)
let ite_negated_guard = disjunction [pb; R.mk_eq_expr ione (int_choice (R.mk_not_expr pb) ione izero)]

let checked_choice_clauses ()
  : Lemma (K.choice_clause ite_then /\ K.choice_clause ite_else /\ K.choice_clause ite_then_le /\
           K.choice_clause ite_int_then_reversed /\ K.choice_clause ite_int_else_swapped /\
           K.choice_clause ite_negated_guard /\ K.consequence core_schema [] ite_then /\
           K.consequence core_schema [] ite_int_else_swapped) =
  assert_norm (K.choice_clause ite_then /\ K.choice_clause ite_else /\ K.choice_clause ite_then_le /\
               K.choice_clause ite_int_then_reversed /\ K.choice_clause ite_int_else_swapped /\
               K.choice_clause ite_negated_guard);
  assert_norm (K.consequence core_schema [] ite_then);
  assert_norm (K.consequence core_schema [] ite_int_else_swapped)

(* The generic theorem at one instance: both branch clauses hold in EVERY
   Sorted model. *)
let choice_clauses_hold (#base:sort -> Type0) (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                        (other:V.interpretation base (S.signature core_schema))
  : Lemma (T.truth core_schema bc eq other ite_then /\ T.truth core_schema bc eq other ite_else) =
  checked_choice_clauses ();
  assert_norm (K.consequence core_schema [] ite_else);
  K.lemma_consequence core_schema bc eq other [] ite_then;
  K.lemma_consequence core_schema bc eq other [] ite_else

(* False variants: the guard flipped, the other branch, another condition,
   and a counterfeit `if` or `=` (same name, no interpretation tag). *)
let flipped_guard_mutant = disjunction [pb; R.mk_eq_expr ione (int_choice pb ione izero)]
let wrong_branch_mutant = disjunction [R.mk_not_expr pb; R.mk_eq_expr izero (int_choice pb ione izero)]
let other_condition_mutant = disjunction [R.mk_not_expr pb; R.mk_eq_expr ione (int_choice qb ione izero)]
let counterfeit_ite_mutant =
  disjunction [R.mk_not_expr pb; R.mk_eq_expr ione (App ({ T.ite_decl integer with interp = None }) [pb; ione; izero])]
let counterfeit_eq_mutant =
  disjunction [R.mk_not_expr pb; App ({ R.eq_decl integer with interp = None }) [ione; int_choice pb ione izero]]

let refused_choice_mutants ()
  : Lemma (not (K.choice_clause flipped_guard_mutant) /\ not (K.choice_clause wrong_branch_mutant) /\
           not (K.choice_clause other_condition_mutant) /\ not (K.choice_clause counterfeit_ite_mutant) /\
           not (K.choice_clause counterfeit_eq_mutant) /\
           not (K.direct_consequence core_schema [] flipped_guard_mutant) /\
           not (K.direct_consequence core_schema [] wrong_branch_mutant)) =
  assert_norm (not (K.choice_clause flipped_guard_mutant) /\ not (K.choice_clause wrong_branch_mutant) /\
               not (K.choice_clause other_condition_mutant) /\ not (K.choice_clause counterfeit_ite_mutant) /\
               not (K.choice_clause counterfeit_eq_mutant));
  assert_norm (not (K.direct_consequence core_schema [] flipped_guard_mutant));
  assert_norm (not (K.direct_consequence core_schema [] wrong_branch_mutant))

(* Opposite-value counter-models: p (and q) chosen, every other free symbol
   at its default; each false variant is false there. *)
let booled (holds:func_decl -> bool) : V.interpretation primitive (S.signature core_schema) = {
  V.application = (fun f xs ->
    if f.range = bool_sort && holds f then V.Scalar bool_sort true
    else (valued nothing).V.application f xs);
  V.quantification = (valued nothing).V.quantification;
}

let p_true (f:func_decl) : bool = f = p_decl
let none_true (f:func_decl) : bool = false

let choice_counter_models ()
  : Lemma (T.truth core_schema booleans equality (booled none_true) flipped_guard_mutant == false /\
           T.truth core_schema booleans equality (booled p_true) wrong_branch_mutant == false /\
           T.truth core_schema booleans equality (booled p_true) other_condition_mutant == false /\
           T.truth core_schema booleans equality (booled p_true) counterfeit_ite_mutant == false /\
           T.truth core_schema booleans equality (booled p_true) counterfeit_eq_mutant == false) =
  assert (T.truth core_schema booleans equality (booled none_true) flipped_guard_mutant == false /\
          T.truth core_schema booleans equality (booled p_true) wrong_branch_mutant == false /\
          T.truth core_schema booleans equality (booled p_true) other_condition_mutant == false /\
          T.truth core_schema booleans equality (booled p_true) counterfeit_ite_mutant == false /\
          T.truth core_schema booleans equality (booled p_true) counterfeit_eq_mutant == false) by
    (Tac.norm [nbe; delta; iota; zeta; primops]; Tac.trivial ())

(* ---------------------------------------------------------------------- *)
(* Int equality/order laws over the commuted difference (-1) * y + x       *)
(* ---------------------------------------------------------------------- *)

(* The arithmetic solver's own equality atoms put the negated operand first:
   FStar.Math.Lemmas-2 q12 node 68 concludes (mod x0 x1) = x0 from
   (-1) * x0 + (mod x0 x1) >= 0 and <= 0, and FStar.Algebra.CommMonoid q3
   node 97 gives the equation in the other orientation. Here (mod x0 x1) is
   the nonconstant product, x0 the opaque application. *)
let commuted (a b:expr) : expr = App iadd [App imul [integer_literal (-1); b]; a]
let cgap = commuted product la

let commuted_eq_upper = disjunction [not_eq product la; leq cgap izero]
let commuted_eq_lower_reversed = disjunction [geq cgap izero; not_eq la product]
let commuted_antisymmetry =
  disjunction [R.mk_eq_expr product la; R.mk_not_expr (leq cgap izero); R.mk_not_expr (geq cgap izero)]

let checked_commuted_order_laws ()
  : Lemma (K.order_clause commuted_eq_upper /\ K.order_clause commuted_eq_lower_reversed /\
           K.order_clause commuted_antisymmetry /\
           K.order_equation [geq cgap izero; leq cgap izero] (R.mk_eq_expr product la) /\
           K.order_equation [geq cgap izero; leq cgap izero] (R.mk_eq_expr la product) /\
           K.order_equation [geq gap izero; leq cgap izero] (R.mk_eq_expr product la) /\
           K.consequence core_schema [] commuted_eq_upper /\
           K.consequence core_schema [geq cgap izero; leq cgap izero] (R.mk_eq_expr product la)) =
  assert_norm (K.order_clause commuted_eq_upper /\ K.order_clause commuted_eq_lower_reversed /\
               K.order_clause commuted_antisymmetry);
  assert_norm (K.order_equation [geq cgap izero; leq cgap izero] (R.mk_eq_expr product la) /\
               K.order_equation [geq cgap izero; leq cgap izero] (R.mk_eq_expr la product) /\
               K.order_equation [geq gap izero; leq cgap izero] (R.mk_eq_expr product la));
  assert_norm (K.consequence core_schema [] commuted_eq_upper);
  assert_norm (K.consequence core_schema [geq cgap izero; leq cgap izero] (R.mk_eq_expr product la))

(* The generic theorem at these instances, in EVERY Sorted model. *)
let commuted_order_laws_hold (#base:sort -> Type0) (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                             (other:V.interpretation base (S.signature core_schema))
  : Lemma (T.truth core_schema bc eq other commuted_eq_upper /\
           (T.truths core_schema bc eq other [geq cgap izero; leq cgap izero] ==>
            T.truth core_schema bc eq other (R.mk_eq_expr product la))) =
  checked_commuted_order_laws ();
  K.lemma_consequence core_schema bc eq other [] commuted_eq_upper;
  if T.truths core_schema bc eq other [geq cgap izero; leq cgap izero] then
    K.lemma_consequence core_schema bc eq other [geq cgap izero; leq cgap izero] (R.mk_eq_expr product la)

(* False variants of the commuted form: the coefficient +1, x and y swapped
   in one bound so both bounds point the same way, a counterfeit `*` (no
   interpretation tag) or `+` (the op_mul tag; either is an uninterpreted
   Int function), the coefficient -2, and the difference compared with 1. *)
let commuted_plus_one_mutant = disjunction [not_eq xi yi; leq (App iadd [App imul [ione; yi]; xi]) izero]
let commuted_swapped_mutant =
  disjunction [R.mk_eq_expr xi yi; R.mk_not_expr (leq (commuted xi yi) izero);
               R.mk_not_expr (geq (commuted yi xi) izero)]
let commuted_counterfeit_mul_mutant =
  disjunction [not_eq xi yi; leq (App iadd [App ({ imul with interp = None }) [integer_literal (-1); yi]; xi]) izero]
let commuted_counterfeit_add_mutant =
  disjunction [not_eq xi yi;
               leq (App ({ iadd with interp = Some Z3ValueTheory.op_mul }) [App imul [integer_literal (-1); yi]; xi]) izero]
let commuted_minus_two_mutant =
  disjunction [not_eq xi yi; geq (App iadd [App imul [integer_literal (-2); yi]; xi]) izero]
let commuted_constant_mutant = disjunction [not_eq xi yi; geq (commuted xi yi) ione]

let refused_commuted_mutants ()
  : Lemma (not (K.order_clause commuted_plus_one_mutant) /\ not (K.order_clause commuted_swapped_mutant) /\
           not (K.order_clause commuted_counterfeit_mul_mutant) /\
           not (K.order_clause commuted_counterfeit_add_mutant) /\
           not (K.order_clause commuted_minus_two_mutant) /\ not (K.order_clause commuted_constant_mutant) /\
           not (K.order_equation [geq (commuted xi yi) izero; leq (commuted yi xi) izero] (R.mk_eq_expr xi yi)) /\
           not (K.order_equation [geq (App iadd [App imul [ione; yi]; xi]) izero;
                                  leq (App iadd [App imul [ione; yi]; xi]) izero] (R.mk_eq_expr xi yi)) /\
           not (K.direct_consequence core_schema [] commuted_plus_one_mutant) /\
           not (K.direct_consequence core_schema [geq (commuted xi yi) izero; leq (commuted yi xi) izero]
                  (R.mk_eq_expr xi yi))) =
  assert_norm (not (K.order_clause commuted_plus_one_mutant) /\ not (K.order_clause commuted_swapped_mutant) /\
               not (K.order_clause commuted_counterfeit_mul_mutant) /\
               not (K.order_clause commuted_counterfeit_add_mutant) /\
               not (K.order_clause commuted_minus_two_mutant) /\ not (K.order_clause commuted_constant_mutant));
  assert_norm (not (K.order_equation [geq (commuted xi yi) izero; leq (commuted yi xi) izero] (R.mk_eq_expr xi yi)) /\
               not (K.order_equation [geq (App iadd [App imul [ione; yi]; xi]) izero;
                                      leq (App iadd [App imul [ione; yi]; xi]) izero] (R.mk_eq_expr xi yi)));
  assert_norm (not (K.direct_consequence core_schema [] commuted_plus_one_mutant));
  assert_norm (not (K.direct_consequence core_schema [geq (commuted xi yi) izero; leq (commuted yi xi) izero]
                      (R.mk_eq_expr xi yi)))

(* Opposite-value counter-models: each false variant is false in a concrete
   Sorted model (x = y = 1 or x = y = 0; x = 0 and y = 1 for the swapped
   bounds, whose premises then hold at x = 1, y = 0 while x = y fails). *)
let y_one (f:func_decl) : option int = if f.decl_name = "y" then Some 1 else None

let commuted_counter_models ()
  : Lemma (T.truth core_schema booleans equality (valued ones) commuted_plus_one_mutant == false /\
           T.truth core_schema booleans equality (valued y_one) commuted_swapped_mutant == false /\
           T.truth core_schema booleans equality (valued ones) commuted_counterfeit_mul_mutant == false /\
           T.truth core_schema booleans equality (valued ones) commuted_counterfeit_add_mutant == false /\
           T.truth core_schema booleans equality (valued ones) commuted_minus_two_mutant == false /\
           T.truth core_schema booleans equality (valued nothing) commuted_constant_mutant == false /\
           T.truths core_schema booleans equality (valued x_one)
             [geq (commuted xi yi) izero; leq (commuted yi xi) izero] == true /\
           T.truth core_schema booleans equality (valued x_one) (R.mk_eq_expr xi yi) == false) =
  assert (T.truth core_schema booleans equality (valued ones) commuted_plus_one_mutant == false /\
          T.truth core_schema booleans equality (valued y_one) commuted_swapped_mutant == false /\
          T.truth core_schema booleans equality (valued ones) commuted_counterfeit_mul_mutant == false /\
          T.truth core_schema booleans equality (valued ones) commuted_counterfeit_add_mutant == false /\
          T.truth core_schema booleans equality (valued ones) commuted_minus_two_mutant == false /\
          T.truth core_schema booleans equality (valued nothing) commuted_constant_mutant == false /\
          T.truths core_schema booleans equality (valued x_one)
            [geq (commuted xi yi) izero; leq (commuted yi xi) izero] == true /\
          T.truth core_schema booleans equality (valued x_one) (R.mk_eq_expr xi yi) == false) by
    (Tac.norm [nbe; delta; iota; zeta; primops]; Tac.trivial ())

(* ---------------------------------------------------------------------- *)
(* Boolean or-gate definition clauses                                       *)
(* ---------------------------------------------------------------------- *)

let bool_atom (name:string) : expr =
  App { decl_name = name; domain = []; range = bool_sort; interp = None; int_params = [] } []
let atom_a = bool_atom "a"
let atom_b = bool_atom "b"
let atom_c = bool_atom "c"

(* FStar.Tactics.BreakVC-1 q1 node 51: (or g h), g = (or (not a) (not h)) and h
   itself an `or`, nested six deep over 16 more atoms; the other literal
   order; the literal the negation of a disjunct; and or-elim clauses (Pure.
   BreakVC-1 q1 node 80, FStar.Order q9 node 145), one over the nested g and h. *)
let bvc_h =
  disjunction [
    R.mk_not_expr (disjunction [bool_atom "b1"; bool_atom "b2"; bool_atom "b3"; bool_atom "b4";
                                bool_atom "b5"; bool_atom "b6"; bool_atom "b7"; bool_atom "b8";
                                bool_atom "b9"; bool_atom "b10"; bool_atom "b11"; bool_atom "b12"]);
    R.mk_not_expr (disjunction [bool_atom "c1";
                                R.mk_not_expr (disjunction [R.mk_not_expr (bool_atom "d1"); bool_atom "d2"]);
                                bool_atom "c3"])]
let bvc_g = disjunction [R.mk_not_expr atom_a; R.mk_not_expr bvc_h]
let or_intro_nested = disjunction [bvc_g; bvc_h]
let or_intro_swapped = disjunction [atom_c; disjunction [atom_a; R.mk_not_expr atom_c; atom_b]]
let or_intro_negated = disjunction [disjunction [atom_a; atom_b; atom_c]; R.mk_not_expr atom_b]
let or_elim_two = disjunction [R.mk_not_expr (disjunction [atom_a; atom_b]); atom_a; atom_b]
let or_elim_nested =
  disjunction [R.mk_not_expr (disjunction [bvc_g; bvc_h; atom_c]); bvc_g; bvc_h; atom_c]

let checked_gate_clauses ()
  : Lemma (K.gate_clause or_intro_nested /\ K.gate_clause or_intro_swapped /\
           K.gate_clause or_intro_negated /\ K.gate_clause or_elim_two /\ K.gate_clause or_elim_nested /\
           K.consequence core_schema [] or_intro_nested /\ K.consequence core_schema [] or_elim_two) =
  assert (K.gate_clause or_intro_nested /\ K.gate_clause or_intro_swapped /\
               K.gate_clause or_intro_negated /\ K.gate_clause or_elim_two /\ K.gate_clause or_elim_nested) by
    (Tac.norm [nbe; delta; iota; zeta; primops]; Tac.trivial ());
  assert (K.consequence core_schema [] or_intro_nested) by
    (Tac.norm [nbe; delta; iota; zeta; primops]; Tac.trivial ());
  assert (K.consequence core_schema [] or_elim_two) by
    (Tac.norm [nbe; delta; iota; zeta; primops]; Tac.trivial ())

(* The bounded propositional route alone refuses the nested or-intro: the
   shared h is cut at two depths into two different skeletons over more than
   12 atoms (reflection boundaries share subformulas between formulas only). *)
let nested_gate_beyond_boolean_consequence ()
  : Lemma (not (DT.boolean_consequence [] or_intro_nested)) =
  assert_norm (not (DT.boolean_consequence [] or_intro_nested))

(* The generic theorem at these instances, in EVERY Sorted model. *)
let gate_clauses_hold (#base:sort -> Type0) (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                      (other:V.interpretation base (S.signature core_schema))
  : Lemma (T.truth core_schema bc eq other or_intro_nested /\ T.truth core_schema bc eq other or_elim_two) =
  checked_gate_clauses ();
  K.lemma_consequence core_schema bc eq other [] or_intro_nested;
  K.lemma_consequence core_schema bc eq other [] or_elim_two

(* False variants: an or-elim with a disjunct dropped, an or-intro literal of
   the wrong polarity (the disjunct itself), a literal complementing no
   disjunct, and a counterfeit `or` or `not` (same name, no interpretation
   tag: an uninterpreted Boolean function). *)
let elim_dropped_mutant =
  disjunction [R.mk_not_expr (disjunction [atom_a; atom_b; atom_c]); atom_a; atom_b]
let intro_polarity_mutant = disjunction [disjunction [atom_a; atom_b]; atom_a]
let intro_member_mutant = disjunction [disjunction [atom_a; atom_b]; R.mk_not_expr atom_c]
let counterfeit_or_mutant =
  disjunction [App ({ BR.connective_decl BR.Disjunction [atom_a; atom_b] with interp = None }) [atom_a; atom_b];
               R.mk_not_expr atom_a]
let counterfeit_not_mutant =
  disjunction [disjunction [atom_a; atom_b]; App ({ R.not_decl with interp = None }) [atom_a]]

let refused_gate_mutants ()
  : Lemma (not (K.gate_clause elim_dropped_mutant) /\ not (K.gate_clause intro_polarity_mutant) /\
           not (K.gate_clause intro_member_mutant) /\ not (K.gate_clause counterfeit_or_mutant) /\
           not (K.gate_clause counterfeit_not_mutant) /\
           not (K.direct_consequence core_schema [] elim_dropped_mutant) /\
           not (K.direct_consequence core_schema [] intro_polarity_mutant) /\
           not (K.direct_consequence core_schema [] intro_member_mutant) /\
           not (K.direct_consequence core_schema [] counterfeit_or_mutant) /\
           not (K.direct_consequence core_schema [] counterfeit_not_mutant)) =
  assert_norm (not (K.gate_clause elim_dropped_mutant) /\ not (K.gate_clause intro_polarity_mutant) /\
               not (K.gate_clause intro_member_mutant) /\ not (K.gate_clause counterfeit_or_mutant) /\
               not (K.gate_clause counterfeit_not_mutant));
  assert_norm (not (K.direct_consequence core_schema [] elim_dropped_mutant));
  assert_norm (not (K.direct_consequence core_schema [] intro_polarity_mutant));
  assert_norm (not (K.direct_consequence core_schema [] intro_member_mutant));
  assert_norm (not (K.direct_consequence core_schema [] counterfeit_or_mutant));
  assert_norm (not (K.direct_consequence core_schema [] counterfeit_not_mutant))

(* Opposite-value counter-models: c true and a, b false (the dropped disjunct
   and the non-member literal); everything false (the wrong polarity, the
   counterfeit `not`); a true (the counterfeit `or`, false by default). *)
let c_true (f:func_decl) : bool = f.decl_name = "c"
let a_true (f:func_decl) : bool = f.decl_name = "a"

let gate_counter_models ()
  : Lemma (T.truth core_schema booleans equality (booled c_true) elim_dropped_mutant == false /\
           T.truth core_schema booleans equality (booled none_true) intro_polarity_mutant == false /\
           T.truth core_schema booleans equality (booled c_true) intro_member_mutant == false /\
           T.truth core_schema booleans equality (booled a_true) counterfeit_or_mutant == false /\
           T.truth core_schema booleans equality (booled none_true) counterfeit_not_mutant == false) =
  assert (T.truth core_schema booleans equality (booled c_true) elim_dropped_mutant == false /\
          T.truth core_schema booleans equality (booled none_true) intro_polarity_mutant == false /\
          T.truth core_schema booleans equality (booled c_true) intro_member_mutant == false /\
          T.truth core_schema booleans equality (booled a_true) counterfeit_or_mutant == false /\
          T.truth core_schema booleans equality (booled none_true) counterfeit_not_mutant == false) by
    (Tac.norm [nbe; delta; iota; zeta; primops]; Tac.trivial ())

(* ---------------------------------------------------------------------- *)
(* Coefficient-free linear Int consequences (recomputed, checked weights)  *)
(* ---------------------------------------------------------------------- *)

(* Actual producer shapes (premise and conclusion formulas as emitted; the
   corpus's BoxInt_proj_0 applications are opaque Int terms here):
   FStar.Tactics.Canon.Lemmas q2 node 495, x = x + y from the bounds through
   ulevel(a); FStar.Int64 q8 node 289, 63 = c64 + (-1) * c1 from constant
   bounds; FStar.Math.Euclid-2 q3 node 306, -1 = x from not (x <= -2) and
   not (x >= 0), refuted only with the strict-Int rounding; an equality chain
   x = z through y (four premises); and false from not (x <= 0) and
   not (x >= 1). *)
let lin_c64 = App { x_decl with decl_name = "c64" } []
let lin_c1 = App { x_decl with decl_name = "c1" } []

let lin_canon = [leq la izero; geq (minus la yi) izero; geq la izero; leq (minus la yi) izero]
let lin_canon_target = R.mk_eq_expr xi (App iadd [xi; yi])
let lin_constants = [leq lin_c64 (integer_literal 64); leq lin_c1 ione; geq lin_c64 (integer_literal 64); geq lin_c1 ione]
let lin_constants_target = R.mk_eq_expr (integer_literal 63) (minus lin_c64 lin_c1)
let lin_tight = [R.mk_not_expr (leq xi (integer_literal (-2))); R.mk_not_expr (geq xi izero)]
let lin_tight_target = R.mk_eq_expr (integer_literal (-1)) xi
let lin_chain = [leq (minus xi yi) izero; geq (minus xi yi) izero; leq (minus yi zi) izero; geq (minus yi zi) izero]
let lin_chain_target = R.mk_eq_expr xi zi
let lin_conflict = [R.mk_not_expr (leq xi izero); R.mk_not_expr (geq xi ione)]

let checked_linear_consequences ()
  : Lemma (K.linear_consequence lin_canon lin_canon_target /\
           K.linear_consequence lin_constants lin_constants_target /\
           K.linear_consequence lin_tight lin_tight_target /\
           K.linear_consequence lin_chain lin_chain_target /\
           K.linear_consequence lin_conflict R.false_expr /\
           not (K.direct_consequence core_schema lin_canon lin_canon_target) /\
           not (K.direct_consequence core_schema lin_constants lin_constants_target) /\
           not (K.direct_consequence core_schema lin_tight lin_tight_target) /\
           not (K.direct_consequence core_schema lin_chain lin_chain_target)) =
  assert_norm (K.linear_consequence lin_canon lin_canon_target);
  assert_norm (K.linear_consequence lin_constants lin_constants_target);
  assert_norm (K.linear_consequence lin_tight lin_tight_target);
  assert_norm (K.linear_consequence lin_chain lin_chain_target);
  assert_norm (K.linear_consequence lin_conflict R.false_expr);
  assert_norm (not (K.direct_consequence core_schema lin_canon lin_canon_target));
  assert_norm (not (K.direct_consequence core_schema lin_constants lin_constants_target));
  assert_norm (not (K.direct_consequence core_schema lin_tight lin_tight_target));
  assert_norm (not (K.direct_consequence core_schema lin_chain lin_chain_target))

(* The generic theorem at these instances, in EVERY Sorted model. *)
let linear_consequences_hold (#base:sort -> Type0) (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                             (other:V.interpretation base (S.signature core_schema))
  : Lemma ((T.truths core_schema bc eq other lin_canon ==> T.truth core_schema bc eq other lin_canon_target) /\
           (T.truths core_schema bc eq other lin_constants ==>
            T.truth core_schema bc eq other lin_constants_target) /\
           (T.truths core_schema bc eq other lin_tight ==> T.truth core_schema bc eq other lin_tight_target) /\
           (T.truths core_schema bc eq other lin_chain ==> T.truth core_schema bc eq other lin_chain_target)) =
  checked_linear_consequences ();
  assert_norm (Z3Definitions.scoped [] lin_canon_target /\ Z3Definitions.scoped [] lin_constants_target /\
               Z3Definitions.scoped [] lin_tight_target /\ Z3Definitions.scoped [] lin_chain_target);
  if T.truths core_schema bc eq other lin_canon then
    K.lemma_linear_consequence core_schema bc eq other lin_canon lin_canon_target;
  if T.truths core_schema bc eq other lin_constants then
    K.lemma_linear_consequence core_schema bc eq other lin_constants lin_constants_target;
  if T.truths core_schema bc eq other lin_tight then
    K.lemma_linear_consequence core_schema bc eq other lin_tight lin_tight_target;
  if T.truths core_schema bc eq other lin_chain then
    K.lemma_linear_consequence core_schema bc eq other lin_chain lin_chain_target

(* The conflict is unsatisfiable in EVERY Sorted model. *)
let linear_conflict_unsatisfiable (#base:sort -> Type0) (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                                  (other:V.interpretation base (S.signature core_schema))
  : Lemma (not (T.truths core_schema bc eq other lin_conflict)) =
  checked_linear_consequences ();
  if T.truths core_schema bc eq other lin_conflict then (
    assert_norm (Z3Definitions.scoped [] R.false_expr);
    K.lemma_linear_consequence core_schema bc eq other lin_conflict R.false_expr;
    assert (T.truth core_schema bc eq other R.false_expr);
    assert_norm (T.cut 1 R.false_expr == Z3BoundedBoolEquiv.Bool false);
    T.lemma_cut core_schema bc eq other 1 R.false_expr;
    assert_norm (Z3BoundedBoolEquiv.geval (T.truth core_schema bc eq other) (Z3BoundedBoolEquiv.Bool false) == false))

(* False variants: a sign flipped (x + 1 * y), a wrong coefficient
   (x + (-2) * y), a dropped bound, a wrong target constant (62), one link
   of the chain at Real (to_real comparisons: Real/mixed), non-strict bounds
   in place of the strict ones (x >= -2; x >= 0 with x < 1), a same-spelled
   twin declaration and a counterfeit `<=` without its interpretation tag. *)
let lin_plus_one (a b:expr) : expr = App iadd [a; App imul [ione; b]]
let lin_minus_two (a b:expr) : expr = App iadd [a; App imul [integer_literal (-2); b]]
let real = (SortApp RealSymbol [])
let to_real (e:expr) : expr =
  App { decl_name = "to_real"; domain = [integer]; range = real; interp = Some Z3ValueTheory.op_to_real;
        int_params = [] } [e]
let real_compare (name:string) (tag:decl_kind) (a b:expr) : expr =
  App { decl_name = name; domain = [real; real]; range = bool_sort; interp = Some tag; int_params = [] } [a; b]

let lin_wrong_sign =
  [leq (lin_plus_one xi yi) izero; geq (lin_plus_one xi yi) izero; leq (minus yi zi) izero; geq (minus yi zi) izero]
let lin_wrong_coefficient =
  [leq (lin_minus_two xi yi) izero; geq (lin_minus_two xi yi) izero; leq (minus yi zi) izero; geq (minus yi zi) izero]
let lin_dropped = [leq (minus xi yi) izero; geq (minus xi yi) izero; leq (minus yi zi) izero]
let lin_wrong_target = R.mk_eq_expr (integer_literal 62) (minus lin_c64 lin_c1)
let lin_mixed =
  [leq (minus xi yi) izero; geq (minus xi yi) izero;
   real_compare "<=" Z3ValueTheory.op_arith_le (to_real yi) (to_real zi);
   real_compare ">=" Z3ValueTheory.op_arith_ge (to_real yi) (to_real zi)]
let lin_weak_tight = [geq xi (integer_literal (-2)); R.mk_not_expr (geq xi izero)]
let lin_weak_conflict = [geq xi izero; R.mk_not_expr (geq xi ione)]
let lin_twin = [leq (minus x_twin yi) izero; geq (minus x_twin yi) izero; leq (minus yi zi) izero; geq (minus yi zi) izero]
let lin_counterfeit =
  [App ({ ile with interp = None }) [minus xi yi; izero]; geq (minus xi yi) izero;
   leq (minus yi zi) izero; geq (minus yi zi) izero]
(* Genuinely false claims over satisfiable bounds 0 < x < 2 (x = 1 in every
   model of them): x = 0, and false. No recomputed certificate exists. *)
let lin_between = [R.mk_not_expr (leq xi izero); R.mk_not_expr (geq xi (integer_literal 2))]
let lin_between_target = R.mk_eq_expr xi izero

(* Each refused. For the Real link the sort-blind search does propose weights
   (to_real read through); the typed check refuses them (Int literals only),
   and linear_consequence refuses the inputs before any search. *)
let refused_linear_mutants ()
  : Lemma (not (K.linear_consequence lin_wrong_sign lin_chain_target) /\
           not (K.linear_consequence lin_wrong_coefficient lin_chain_target) /\
           not (K.linear_consequence lin_dropped lin_chain_target) /\
           not (K.linear_consequence lin_constants lin_wrong_target) /\
           not (K.linear_consequence lin_mixed lin_chain_target) /\
           not (K.linear_consequence lin_weak_tight lin_tight_target) /\
           not (K.linear_consequence lin_weak_conflict R.false_expr) /\
           not (K.linear_consequence lin_twin lin_chain_target) /\
           not (K.linear_consequence lin_counterfeit lin_chain_target) /\
           not (K.linear_consequence lin_between lin_between_target) /\
           not (K.linear_consequence lin_between R.false_expr) /\
           (match LA.synthesize (K.int_le xi zi) lin_mixed with
            | Some cs -> not (AR.check_contradiction (LA.assumptions (K.int_le xi zi) lin_mixed) cs)
            | None -> False)) =
  assert_norm (not (K.linear_consequence lin_wrong_sign lin_chain_target));
  assert_norm (not (K.linear_consequence lin_wrong_coefficient lin_chain_target));
  assert_norm (not (K.linear_consequence lin_dropped lin_chain_target));
  assert_norm (not (K.linear_consequence lin_constants lin_wrong_target));
  assert_norm (not (K.linear_consequence lin_mixed lin_chain_target));
  assert_norm (not (K.linear_consequence lin_weak_tight lin_tight_target));
  assert_norm (not (K.linear_consequence lin_weak_conflict R.false_expr));
  assert_norm (not (K.linear_consequence lin_twin lin_chain_target));
  assert_norm (not (K.linear_consequence lin_counterfeit lin_chain_target));
  assert_norm (not (K.linear_consequence lin_between lin_between_target));
  assert_norm (not (K.linear_consequence lin_between R.false_expr));
  assert_norm (match LA.synthesize (K.int_le xi zi) lin_mixed with
               | Some cs -> not (AR.check_contradiction (LA.assumptions (K.int_le xi zi) lin_mixed) cs)
               | None -> False)

(* Opposite-value counter-models: in each concrete Sorted model every premise
   of the false variant holds and its conclusion is false. The Real
   comparisons are not Int arithmetic in the Sorted semantics, so they are
   chosen true there. *)
let picked (pick:func_decl -> option int) (holds:func_decl -> bool)
  : V.interpretation primitive (S.signature core_schema) = {
  V.application = (fun f xs ->
    if f.range = bool_sort && holds f then V.Scalar bool_sort true
    else (valued pick).V.application f xs);
  V.quantification = (valued nothing).V.quantification;
}

let xyz (x y z:int) (f:func_decl) : option int =
  if f = x_decl then Some x
  else if f = { x_decl with decl_name = "y" } then Some y
  else if f = { x_decl with decl_name = "z" } then Some z
  else None
let c64_c1 (f:func_decl) : option int =
  if f.decl_name = "c64" then Some 64 else if f.decl_name = "c1" then Some 1 else None
let real_comparisons (f:func_decl) : bool = f.domain = [real; real]
let counterfeit_le (f:func_decl) : bool = f = { ile with interp = None }

let linear_counter_models ()
  : Lemma (T.truths core_schema booleans equality (valued (xyz (-1) 1 1)) lin_wrong_sign == true /\
           T.truth core_schema booleans equality (valued (xyz (-1) 1 1)) lin_chain_target == false /\
           T.truths core_schema booleans equality (valued (xyz 2 1 1)) lin_wrong_coefficient == true /\
           T.truth core_schema booleans equality (valued (xyz 2 1 1)) lin_chain_target == false /\
           T.truths core_schema booleans equality (valued (xyz 0 0 1)) lin_dropped == true /\
           T.truth core_schema booleans equality (valued (xyz 0 0 1)) lin_chain_target == false /\
           T.truths core_schema booleans equality (valued c64_c1) lin_constants == true /\
           T.truth core_schema booleans equality (valued c64_c1) lin_wrong_target == false /\
           T.truths core_schema booleans equality (picked (xyz 0 0 1) real_comparisons) lin_mixed == true /\
           T.truth core_schema booleans equality (picked (xyz 0 0 1) real_comparisons) lin_chain_target == false /\
           T.truths core_schema booleans equality (valued (xyz (-2) 0 0)) lin_weak_tight == true /\
           T.truth core_schema booleans equality (valued (xyz (-2) 0 0)) lin_tight_target == false /\
           T.truths core_schema booleans equality (valued nothing) lin_weak_conflict == true /\
           T.truths core_schema booleans equality (valued (xyz 1 0 0)) lin_twin == true /\
           T.truth core_schema booleans equality (valued (xyz 1 0 0)) lin_chain_target == false /\
           T.truths core_schema booleans equality (picked (xyz 1 0 0) counterfeit_le) lin_counterfeit == true /\
           T.truth core_schema booleans equality (picked (xyz 1 0 0) counterfeit_le) lin_chain_target == false /\
           T.truths core_schema booleans equality (valued (xyz 1 0 0)) lin_between == true /\
           T.truth core_schema booleans equality (valued (xyz 1 0 0)) lin_between_target == false) =
  assert (T.truths core_schema booleans equality (valued (xyz (-1) 1 1)) lin_wrong_sign == true /\
          T.truth core_schema booleans equality (valued (xyz (-1) 1 1)) lin_chain_target == false /\
          T.truths core_schema booleans equality (valued (xyz 2 1 1)) lin_wrong_coefficient == true /\
          T.truth core_schema booleans equality (valued (xyz 2 1 1)) lin_chain_target == false /\
          T.truths core_schema booleans equality (valued (xyz 0 0 1)) lin_dropped == true /\
          T.truth core_schema booleans equality (valued (xyz 0 0 1)) lin_chain_target == false /\
          T.truths core_schema booleans equality (valued c64_c1) lin_constants == true /\
          T.truth core_schema booleans equality (valued c64_c1) lin_wrong_target == false /\
          T.truths core_schema booleans equality (picked (xyz 0 0 1) real_comparisons) lin_mixed == true /\
          T.truth core_schema booleans equality (picked (xyz 0 0 1) real_comparisons) lin_chain_target == false /\
          T.truths core_schema booleans equality (valued (xyz (-2) 0 0)) lin_weak_tight == true /\
          T.truth core_schema booleans equality (valued (xyz (-2) 0 0)) lin_tight_target == false /\
          T.truths core_schema booleans equality (valued nothing) lin_weak_conflict == true /\
          T.truths core_schema booleans equality (valued (xyz 1 0 0)) lin_twin == true /\
          T.truth core_schema booleans equality (valued (xyz 1 0 0)) lin_chain_target == false /\
          T.truths core_schema booleans equality (picked (xyz 1 0 0) counterfeit_le) lin_counterfeit == true /\
          T.truth core_schema booleans equality (picked (xyz 1 0 0) counterfeit_le) lin_chain_target == false /\
          T.truths core_schema booleans equality (valued (xyz 1 0 0)) lin_between == true /\
          T.truth core_schema booleans equality (valued (xyz 1 0 0)) lin_between_target == false) by
    (Tac.norm [nbe; delta; iota; zeta; primops]; Tac.trivial ())

#pop-options
