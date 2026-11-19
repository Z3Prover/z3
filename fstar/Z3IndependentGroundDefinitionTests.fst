module Z3IndependentGroundDefinitionTests

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module R = Z3ClauseSyntax
module A = Z3SortedArray
module Ground = Z3IndependentGroundDefinition
module GroundRoot = Z3IndependentGroundDefinitionRoot
module Recognition = Z3DefinitionRecognition

let schema : S.checked_schema = { S.sorts = []; S.cases = [] }
let int_s = TR.int_s
let array_s = ArraySort [int_s] int_s
let constant (name:string) (s:sort) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = [] } []
let a = constant "a" array_s
let i = constant "i" int_s
let v = constant "v" int_s
let body = App (A.store_decl int_s int_s) [a; i; v]
let symbol = { decl_name = "fresh-array"; domain = []; range = array_s; interp = None; int_params = [] }
let name = App symbol []
let formula = R.mk_eq_expr body name
let input = R.mk_eq_expr a a
let definition : D.definition = { D.symbol = symbol; variables = []; body = body }

let controls ()
  : Lemma (
    Ground.valid schema [input] formula definition /\
    Ground.recognize schema [input] formula == Some definition /\
    Ground.recognize schema [input] (R.mk_eq_expr name body) == Some definition /\
    Ground.recognize schema [R.mk_eq_expr name name] formula == None /\
    not (Ground.valid schema [input] (R.mk_eq_expr name name)
      { definition with D.body = name }) /\
    not (Ground.valid schema [input] formula
      { definition with D.symbol = { symbol with interp = Some 1 } }) /\
    not (Ground.valid schema [input] formula
      { definition with D.body = Var 0 array_s }) /\
    Ground.recognize schema [input] (R.mk_not_expr formula) == None) =
  assert_norm (Ground.valid schema [input] formula definition);
  assert_norm (Ground.recognize schema [input] formula == Some definition);
  assert_norm (Ground.recognize schema [input] (R.mk_eq_expr name body) == Some definition);
  assert_norm (Ground.recognize schema [R.mk_eq_expr name name] formula == None);
  assert_norm (not (Ground.valid schema [input] (R.mk_eq_expr name name)
    { definition with D.body = name }));
  assert_norm (not (Ground.valid schema [input] formula
    { definition with D.symbol = { symbol with interp = Some 1 } }));
  assert_norm (not (Ground.valid schema [input] formula
    { definition with D.body = Var 0 array_s }));
  assert_norm (Ground.recognize schema [input] (R.mk_not_expr formula) == None)

let sound_control (u:TR.uninterpreted) (other:TR.interp u schema)
  (d:Ground.definition schema [input] formula)
  : Lemma (requires TR.root_model u schema other)
    (ensures (
      let extended = Ground.override schema (TR.booleans u) (SR.root_scalars u)
        other [input] formula d in
      TR.root_model u schema extended /\
      Z3SortedSemantics.truth schema (TR.booleans u) (SR.root_scalars u) extended formula /\
      Z3SortedSemantics.truths schema (TR.booleans u) (SR.root_scalars u) extended [input] ==
      Z3SortedSemantics.truths schema (TR.booleans u) (SR.root_scalars u) other [input])) =
  GroundRoot.lemma_override_root u schema (TR.booleans u) (SR.root_scalars u)
    [input] formula d other;
  Ground.lemma_definition schema (TR.booleans u) (SR.root_scalars u) other [input] formula d;
  Ground.lemma_inputs schema (TR.booleans u) (SR.root_scalars u) other [input] formula d

let definition_pair (condition name yes no:expr) : expr =
  let not_condition = R.mk_not_expr condition in
  let positive_equality = R.mk_eq_expr name yes in
  let negative_equality = R.mk_eq_expr name no in
  let positive = App (R.or_decl [not_condition; positive_equality]) [not_condition; positive_equality] in
  let negative = App (R.or_decl [condition; negative_equality]) [condition; negative_equality] in
  App (R.and_decl [positive; negative]) [positive; negative]

let probe = constant "ground-definition-probe" bool_sort
let not_probe = R.mk_not_expr probe
let first_name = constant "ground-definition-first" bool_sort
let second_name = constant "ground-definition-second" bool_sort
let first_definition =
  definition_pair R.true_expr second_name first_name R.false_expr
let second_definition =
  definition_pair probe first_name probe not_probe

let paired_definitions_are_recognized ()
  : Lemma (Some? (Recognition.definition_of first_definition) /\
           Some? (Recognition.definition_of second_definition)) =
  assert_norm (Some? (Recognition.definition_of first_definition) /\
               Some? (Recognition.definition_of second_definition))

let ground_definition_controls ()
  : Lemma (D.scoped [] first_definition /\ D.scoped [] second_definition /\
           (match Recognition.definition_of first_definition with
            | Some d -> d.D.symbol.domain = [] /\ d.D.variables = []
            | None -> false) /\
           (match Recognition.definition_of second_definition with
            | Some d -> d.D.symbol.domain = [] /\ d.D.variables = []
            | None -> false)) =
  assert_norm (D.scoped [] first_definition /\ D.scoped [] second_definition /\
               (match Recognition.definition_of first_definition with
                | Some d -> d.D.symbol.domain = [] /\ d.D.variables = []
                | None -> false) /\
               (match Recognition.definition_of second_definition with
                | Some d -> d.D.symbol.domain = [] /\ d.D.variables = []
                | None -> false))
