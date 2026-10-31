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

let large_documents () : bool =
  let good = fixture U.Asserted in
  let entry = { P.rule = U.Asserted; P.formula = R.false_expr; P.premise_ids = [] } in
  let document = { good with C.document = {
    good.document with
      P.entries = repeat_entries 20000 entry [];
      P.root = 19999 } } in
  let bad = { entry with P.rule = U.Reflexivity } in
  let rejected = { document with C.document = {
    document.document with P.entries = repeat_entries 19999 entry [bad] } } in
  C.check false document = Some 0 &&
  C.check true document = Some 0 &&
  C.check false rejected = None

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

(* The binder scope guard builds scopes, walks expressions and compares sorts
   with loops (`U.scope_under`, `U.scoped_frames_within`, `U.sort_tasks_within`).
   Each certificate below holds a deep or wide term in a used internal entry
   under the closed root `(= true true)`, so the document's own scope check of
   the node formula does not walk it; unused `refl` entries give the guard its
   work. Before the loops, the guard overflowed the native stack on all four
   (a quantifier over 200,000 binders, 200,000 nested negations, a sort nested
   50,000 deep in an array domain); the guard-free checker accepted them. Inputs
   are built by tail-recursive accumulators. *)
let rec int_sorts (n:nat) (acc:list A.sort) : Tot (list A.sort) (decreases n) =
  if n = 0 then acc else int_sorts (n - 1) (A.BaseSort "Int" :: acc)

let rec nested_not (depth:nat) (acc:A.expr) : Tot A.expr (decreases depth) =
  if depth = 0 then acc else nested_not (depth - 1) (R.mk_not_expr acc)

let rec domain_nested (depth:nat) (acc:A.sort) : Tot A.sort (decreases depth) =
  if depth = 0 then acc else domain_nested (depth - 1) (A.ArraySort [acc] (A.BaseSort "Int"))

let binder_entry (name:string) (formula:A.expr) (premises:list int) : U.binder_entry =
  { U.binder_name = name; U.binder_formula = formula; U.binder_premises = premises; U.binder_sorts = None }

let rec padding (count:nat) (entries:list U.binder_entry)
  : Tot (list U.binder_entry) (decreases count) =
  if count = 0 then entries
  else padding (count - 1) (binder_entry "refl" (R.mk_eq_expr R.true_expr R.true_expr) [] :: entries)

(* refl (= q q); iff-true ((= q q) = true); mp true; iff-true (true = true), the root. *)
let hidden_term_pending (q:A.expr) (pad:nat) : int =
  let eqq = R.mk_eq_expr q q in
  let entries =
    binder_entry "refl" eqq [] ::
    binder_entry "iff-true" (R.mk_iff_expr eqq R.true_expr) [0] ::
    binder_entry "mp" R.true_expr [0; 1] ::
    binder_entry "iff-true" (R.mk_iff_expr R.true_expr R.true_expr) [2] :: padding pad [] in
  let e = { P.rule = U.QuantifierIntroduction ({ U.binder_entries = entries; U.binder_root = 3 });
            P.formula = R.mk_eq_expr R.true_expr R.true_expr; P.premise_ids = [] } in
  match P.check_entry false true [] [] Z3ProofIndex.Empty e with
  | Some (_, pending) -> pending
  | None -> -1

let binder_guard_stack () : bool =
  let deep_sort = domain_nested 50000 (A.BaseSort "Int") in
  let x = A.Var 0 deep_sort in
  let deep_sort_q = A.Quantifier A.Forall_k [deep_sort] A.bool_sort (R.mk_eq_expr x x) in
  hidden_term_pending (A.Quantifier A.Forall_k (int_sorts 200000 []) A.bool_sort R.true_expr) 42 = 0 &&
  hidden_term_pending (nested_not 200000 R.true_expr) 308 = 0 &&
  hidden_term_pending deep_sort_q 200 = 0 &&
  (* the same certificate with less work: the guard's budget leaves it pending *)
  hidden_term_pending deep_sort_q 79 = 1

(* The verdict of a diagnosed document is the verdict of its check (Z3Cherry.lemma_diagnose_is_check),
   for accepted, pending and rejected documents. *)
let diagnosis_is_check (force_sorted:bool) (m:C.marshaled) : bool =
  P.diagnostic_result (C.diagnose force_sorted m) = C.check force_sorted m

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
  diagnosis_is_check false good && diagnosis_is_check true good &&
  diagnosis_is_check false bad_root && diagnosis_is_check true bad_root &&
  diagnosis_is_check false missing_input && diagnosis_is_check true missing_input &&
  diagnosis_is_check false bad_rule && diagnosis_is_check true bad_rule &&
  diagnosis_is_check false pending && diagnosis_is_check true pending &&
  large_axiom_scan () &&
  large_documents () &&
  bounded_conditional_rewrite () &&
  binder_guard_stack ()
