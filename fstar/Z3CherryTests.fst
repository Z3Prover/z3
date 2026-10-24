module Z3CherryTests

module A = Z3AstTheory
module P = Z3ProofDocument
module R = Z3ResolutionProofTheory
module U = Z3UnifiedProof
module C = Z3Cherry

let fixture (rule:U.rule) : C.marshaled =
  let declarations = match R.false_expr with A.App f _ -> [f] | _ -> [] in
  { C.document = {
      P.declarations = declarations;
      P.expressions = [R.false_expr];
      P.assertions = [R.false_expr];
      P.entries = [{ P.rule = rule; P.formula = R.false_expr; P.premise_ids = [] }];
      P.root = 0 };
    C.schema = { Z3DatatypeSignature.sorts = []; Z3DatatypeSignature.cases = [] } }

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
  C.check true pending = Some 1
