module A = Z3AstTheory
module U = Z3UnifiedProofSyntax
module P = Z3DocumentSyntax
module R = Z3ClauseSyntax
module S = Z3DatatypeSignature
module SP = Z3SortedProof
module Cached = Z3IndependentCachedReplay
module Checker = Z3IndependentChecker
module Root = Z3SortedRootDocument

let require value message = if not value then failwith message
let schema = { S.sorts = []; cases = [] }
let assertions = [R.false_expr]

let reference entry premises =
  match SP.prepare_entry_from schema premises entry with
  | None -> None
  | Some node ->
    match SP.check_node_cached schema assertions node with
    | None -> None
    | Some (fact, local) -> Some (node, fact, local)

let check memo index entry premises =
  let actual, memo = Cached.check_entry schema assertions memo index entry premises in
  require (actual = reference entry premises)
    "memo reused a different entry or resolved premises";
  actual, memo

let entry rule formula premise_ids = { P.rule; formula; premise_ids }
let doc entries root =
  { P.declarations = []; expressions = []; assertions; entries; root }

let () =
  let asserted = entry U.Asserted R.false_expr [] in
  let first, memo = check (Cached.empty schema assertions) Z.zero asserted (Some []) in
  require (Option.is_some first) "asserted fixture was rejected";
  let memo = Cached.seal schema assertions memo in
  let _, memo = check memo Z.zero asserted (Some []) in
  let changed, memo = check memo Z.zero { asserted with P.rule = U.Hypothesis } (Some []) in
  require (changed <> first) "changed rule did not change hypotheses";
  let _, fact, _ = Option.get changed in
  let rejected, memo = check memo Z.zero asserted (Some [fact]) in
  require (Option.is_none rejected) "changed premises reused an earlier result";
  let rejected, memo = check memo Z.zero { asserted with P.formula = R.true_expr } (Some []) in
  require (Option.is_none rejected) "changed raw formula reused an earlier preparation";
  let restored, _ = check (Cached.seal schema assertions memo) Z.zero asserted (Some []) in
  require (restored = first) "cached rejection masked a valid replacement";
  let _, good_fact, _ = Option.get first in
  let carry = entry (U.Unverified "carry") R.false_expr [Z.zero] in
  let inherited, memo =
    check (Cached.empty schema assertions) Z.zero carry (Some [good_fact]) in
  let changed, _ =
    check (Cached.seal schema assertions memo) Z.zero carry (Some [fact]) in
  require (inherited <> changed) "same entry reused different premise hypotheses";
  let variants = [
    doc [entry U.Asserted R.false_expr []] Z.zero;
    doc [entry (U.Unverified "pending") R.false_expr []] Z.zero;
    doc [entry U.Hypothesis R.false_expr []] Z.zero;
    doc [entry U.Asserted R.true_expr []] Z.zero;
    doc [entry U.Asserted R.false_expr [Z.zero]] Z.zero;
    doc [] Z.zero;
    doc [entry U.Asserted R.false_expr []] Z.one;
  ] in
  let memo = ref (Cached.empty schema assertions) in
  List.iter (fun document ->
    let verdict = Checker.check_definition schema document in
    let diagnostic =
      if verdict = Root.RootCertified then P.DocumentChecked (Z.zero, [])
      else Checker.diagnose schema document in
    require (Checker.check_definition_diagnosed schema document = (verdict, diagnostic))
      "shared definition checking changed verdicts or diagnostics";
    let actual, next = Cached.diagnose_document schema document !memo in
    require (actual = SP.diagnose_document schema document)
      "reused replay changed complete diagnostics";
    memo := Cached.seal schema assertions next) (variants @ List.rev variants);
  let atom name =
    A.App ({ A.decl_name = name; domain = []; range = A.bool_sort;
             interp = None; int_params = [] }, []) in
  let left = atom "congruence-left" and right = atom "congruence-right" in
  let f = { A.decl_name = "congruence-function"; domain = [A.bool_sort];
            range = A.bool_sort; interp = None; int_params = [] } in
  let premise = { U.conclusion = U.Equal (left, right);
                  hypotheses = [R.mk_eq_expr left right] } in
  let congruent = entry U.Congruence
      (R.mk_eq_expr (A.App (f, [left])) (A.App (f, [right]))) [Z.zero] in
  let result, _ =
    check (Cached.empty schema assertions) Z.one congruent (Some [premise]) in
  require (match result with
    | Some (_, fact, pending) ->
      Z.equal pending Z.zero && fact.U.hypotheses = premise.U.hypotheses
    | None -> false) "application congruence lost its premise hypotheses";
  let changed = { f with A.decl_name = "congruence-other" } in
  let mismatched = { congruent with P.formula =
      R.mk_eq_expr (A.App (f, [left])) (A.App (changed, [right])) } in
  let _, _ =
    check (Cached.empty schema assertions) Z.one mismatched (Some [premise]) in
  let ill_scoped = { congruent with P.formula =
      R.mk_eq_expr (A.App (f, [A.Var (Z.zero, A.bool_sort)]))
                   (A.App (f, [right])) } in
  let rejected, _ =
    check (Cached.empty schema assertions) Z.one ill_scoped (Some [premise]) in
  require (Option.is_none rejected) "application shortcut accepted an unscoped term";
  print_endline "locally threaded replay cache tests passed"
