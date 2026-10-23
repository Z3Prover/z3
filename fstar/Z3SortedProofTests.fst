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

let box = BaseSort "Box"
let integer = BaseSort "Int"

let primitive (s:sort) : Type0 =
  match s with BaseSort "Int" -> int | BaseSort "Bool" -> bool | _ -> unit

let primitive_default (s:sort) : primitive s =
  match s with BaseSort "Int" -> 0 | BaseSort "Bool" -> false | _ -> ()

let primitive_equal (s:sort) (x y:primitive s) : bool =
  match s with BaseSort "Int" -> x = y | BaseSort "Bool" -> x = y | _ -> true

let equality : T.scalar_equality primitive =
  T.Mkscalar_equality #primitive primitive_equal ()

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
                                   (eq:T.scalar_equality base)
                                   (other:V.interpretation base (S.signature schema))
  : Lemma (ensures not (T.truths schema bc eq other exhaustive_document.assertions)) =
  original_inputs_and_exhaustiveness ();
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
                                             (eq:T.scalar_equality base)
                                             (other:V.interpretation base (S.signature core_schema))
  : Lemma (ensures K.check_document core_schema core_document == Some 0 /\
                   not (T.truths core_schema bc eq other core_document.assertions)) =
  assert_norm (K.check_document core_schema core_document == Some 0);
  K.lemma_check_document core_schema bc eq other core_document

#pop-options
