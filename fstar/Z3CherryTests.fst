module Z3CherryTests

module A = Z3AstTheory
module P = Z3ProofDocument
module R = Z3ResolutionProofTheory
module U = Z3UnifiedProof
module C = Z3Cherry
module CR = Z3ConditionalRewrite

let fixture (rule:U.rule) : C.marshaled =
  let declarations = match R.false_expr with A.App f _ -> [f] | _ -> [] in
  { C.document = {
      P.declarations = declarations;
      P.expressions = [R.false_expr];
      P.assertions = [R.false_expr];
      P.entries = [{ P.rule = rule; P.formula = R.false_expr; P.premise_ids = [] }];
      P.root = 0 };
    C.schema = { Z3DatatypeSignature.sorts = []; Z3DatatypeSignature.cases = [] } }

let rec repeat_entries (count:nat) (e:P.entry) (entries:list P.entry)
  : Tot (list P.entry) (decreases count) =
  if count = 0 then entries
  else repeat_entries (count - 1) e (e :: entries)

let large_axiom_scan () : bool =
  let branch (guard:A.expr) : A.expr =
    A.App {
      A.decl_name = "or"; A.domain = [A.bool_sort; A.bool_sort];
      A.range = A.bool_sort; A.interp = Some Z3ValueTheory.op_or; A.int_params = [];
    } [guard; R.mk_eq_expr (A.Var 2 A.bool_sort) R.false_expr] in
  let first = branch (A.Var 0 A.bool_sort) in
  let last = branch (A.Var 1 A.bool_sort) in
  let entry (rule:U.rule) (formula:A.expr) : P.entry =
    { P.rule = rule; P.formula = formula; P.premise_ids = [] } in
  P.axiom_branches
    (entry U.DefAxiom first ::
     repeat_entries 200000 (entry U.Asserted R.false_expr) [entry U.DefAxiom last]) =
    [first; last]

let shared_decl : A.func_decl = {
  A.decl_name = "shared"; A.domain = [A.bool_sort; A.bool_sort];
  A.range = A.bool_sort; A.interp = None; A.int_params = [];
}

let rec shared_expression (depth:nat) (leaf:A.expr)
  : Tot A.expr (decreases depth) =
  if depth = 0 then leaf
  else let child = shared_expression (depth - 1) leaf in
    A.App shared_decl [child; child]

let bounded_conditional_rewrite () : bool =
  let guard = A.Var 0 A.bool_sort in
  let leaf = A.Var 1 A.bool_sort in
  let pair = A.App shared_decl [leaf; leaf] in
  let shared = shared_expression 24 leaf in
  let ite (c t e:A.expr) : A.expr =
    A.App (Z3ArrayRewrite.term_ite_decl A.bool_sort) [c; t; e] in
  A.expression_budget 3 pair = Some 0 &&
  A.expression_budget 2 pair = None &&
  not (CR.equivalent (ite guard shared R.true_expr) shared) &&
  not (Z3TheoryNormalize.equivalent shared R.true_expr) &&
  CR.equivalent (ite guard R.true_expr R.false_expr) guard

let run () : bool =
  let good = fixture U.Asserted in
  let bad_root = { good with C.document = { good.document with P.root = 1 } } in
  let missing_input = { good with C.document = { good.document with P.assertions = [] } } in
  let bad_rule = fixture U.Reflexivity in
  let pending = fixture (U.Unverified "unsupported") in
  C.check false good = Some 0 &&
  C.check true good = Some 0 &&
  C.check false bad_root = None &&
  C.check false missing_input = None &&
  C.check false bad_rule = None &&
  C.check false pending = Some 1 &&
  C.check true pending = Some 1 &&
  large_axiom_scan () &&
  bounded_conditional_rewrite ()
