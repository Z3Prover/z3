module Z3CherryTests

module A = Z3AstTheory
module P = Z3ProofDocument
module R = Z3ResolutionProofTheory
module U = Z3UnifiedProof
module C = Z3Cherry
module CR = Z3ConditionalRewrite
module CS = Z3CheckedSorts

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

(* Checked sorts with the native bounded name counter (`CS.checked_name_units`): the exact
   units of Int, Bool and Array Int Bool (Z3CheckedSortsTests.exact_budgets) and one short by
   phase; an 8 MiB name is refused at preparation 0 and 1, and one short of its units
   (1 + 8388608 characters + 33 + 66 + 33 + 33). *)
let sort_units (raw:list CS.raw_sort) (p s:nat) : int =
  match CS.validate_sort_graph CS.checked_name_units raw ({ CS.preparation = p; CS.storage = s }) with
  | CS.Prepared _ _ left -> p - left.CS.preparation
  | CS.InvalidSortGraph _ -> -1
  | CS.Exhausted CS.Preparation -> -2
  | CS.Exhausted CS.Storage -> -3

let checked_name_units () : bool =
  let basic = [CS.RawBase 1 "Int"; CS.RawBase 2 "Bool"; CS.RawArray 3 1 [1] 2] in
  let giant = [CS.RawBase 1 (FStar.String.make 8388608 'g')] in
  let giant_units = 8388608 + 166 in
  sort_units basic 573 308 = 573 &&
  sort_units basic 572 308 = -2 &&
  sort_units basic 573 307 = -3 &&
  sort_units giant 0 102 = -2 &&
  sort_units giant 1 102 = -2 &&
  sort_units giant (giant_units - 1) 102 = -2 &&
  sort_units giant giant_units 102 = giant_units

let units_within (s:string) (n limit:nat) : bool =
  Z3NameUnits.scan_units s limit = (if n <= limit then n else -1)

(* Called by tests.cpp on byte strings F* cannot write: the native counter against the
   runtime decoder's count (`U.name_length`) under limits 0, 1, the count - 1, the count,
   the count + 1 and 2^100. *)
let name_units_agree (s:string) : bool =
  let n = U.name_length s in
  units_within s n 0 && units_within s n 1 && (n = 0 || units_within s n (n - 1)) &&
  units_within s n n && units_within s n (n + 1) &&
  units_within s n 1267650600228229401496703205376

(* The NNF certificate replay (Z3NnfReplay) at native scale: its walks are
   loops. A chain of 200,000 transitivity steps, a 100,000-ary disjunction,
   200,000 nested negations (replayed with enough unused padding entries for
   the work budget, pending without them), a shared term whose tree has 2^60
   nodes (pending: the budget is charged per tree node, so the walk stops
   early), and a forward premise id (malformed). *)
let nnf_p : A.expr =
  A.App { A.decl_name = "p"; A.domain = []; A.range = A.bool_sort; A.interp = None; A.int_params = [] } []

let nnf_oeq (a b:A.expr) : A.expr = Z3ObservationalEquality.mk_oeq_expr a b

let rec nnf_chain (count k:nat) (acc:list U.binder_entry) : Tot (list U.binder_entry) (decreases count) =
  if count = 0 then acc
  else nnf_chain (count - 1) (k + 1) (binder_entry "trans" (nnf_oeq nnf_p nnf_p) [k; 0] :: acc)

let rec nnf_copies (#a:Type) (count:nat) (x:a) (acc:list a) : Tot (list a) (decreases count) =
  if count = 0 then acc else nnf_copies (count - 1) x (x :: acc)

let nnf_verdict (entries:list U.binder_entry) (root:int) (lhs rhs:A.expr) : Z3NnfReplay.verdict =
  Z3NnfReplay.replay [] ({ U.binder_entries = entries; U.binder_root = root }) (U.Observational lhs rhs)

let nnf_wide (n pad:nat) : Z3NnfReplay.verdict =
  let np = R.mk_not_expr nnf_p in
  let ps = nnf_copies n nnf_p [] in
  let nps = nnf_copies n np [] in
  let bools = nnf_copies n A.bool_sort [] in
  let disjunction = A.App { A.decl_name = "or"; A.domain = bools; A.range = A.bool_sort;
                            A.interp = Some Z3ValueTheory.op_or; A.int_params = [] } ps in
  let conjunction = A.App { A.decl_name = "and"; A.domain = bools; A.range = A.bool_sort;
                            A.interp = Some Z3ValueTheory.op_and; A.int_params = [] } nps in
  nnf_verdict (binder_entry "refl" (nnf_oeq np np) [] ::
               binder_entry "nnf-neg" (nnf_oeq (R.mk_not_expr disjunction) conjunction) (nnf_copies n 0 []) ::
               padding pad [])
    1 (R.mk_not_expr disjunction) conjunction

let nnf_deep (depth pad:nat) : Z3NnfReplay.verdict =
  let deep = nested_not depth nnf_p in
  let twice = R.mk_not_expr (R.mk_not_expr deep) in
  nnf_verdict (binder_entry "refl" (nnf_oeq deep deep) [] ::
               binder_entry "nnf-neg" (nnf_oeq twice deep) [0] :: padding pad [])
    1 twice deep

let nnf_replay_scale () : bool =
  let twice = R.mk_not_expr (R.mk_not_expr nnf_p) in
  let chain = FStar.List.Tot.rev
    (binder_entry "nnf-neg" (nnf_oeq twice nnf_p) [200000] ::
     nnf_chain 200000 0 [binder_entry "refl" (nnf_oeq nnf_p nnf_p) []]) in
  let big = shared_expression 60 nnf_p in
  let big_twice = R.mk_not_expr (R.mk_not_expr big) in
  nnf_verdict chain 200001 twice nnf_p = Z3NnfReplay.Replayed &&
  nnf_wide 100000 200 = Z3NnfReplay.Replayed &&
  nnf_wide 100000 0 = Z3NnfReplay.Unreplayed &&
  nnf_deep 200000 800 = Z3NnfReplay.Replayed &&
  nnf_deep 200000 0 = Z3NnfReplay.Unreplayed &&
  nnf_verdict [binder_entry "refl" (nnf_oeq big big) []; binder_entry "nnf-neg" (nnf_oeq big_twice big) [0]]
    1 big_twice big = Z3NnfReplay.Unreplayed &&
  nnf_verdict [binder_entry "refl" (nnf_oeq nnf_p nnf_p) [1]; binder_entry "nnf-neg" (nnf_oeq twice nnf_p) [0]]
    1 twice nnf_p = Z3NnfReplay.Malformed

(* The regrouping check of quant-intro rewrite leaves (Z3NnfReplay.regrouped)
   at native scale, in the Cherry checker (the OCaml counterpart is
   test_native_bridge.ml `sorted_quant_intro_regrouping`). The
   Pulse.Checker.Base-1 shape (or g1 g2 g3 deep) = (or (or g1 g2) (or g3
   deep)) with `deep` nesting alternating and/or 71 levels is refused by the
   depth-64 and depth-2 propositional checks, regrouped and replayed; a
   wrong operand stays pending; a 2,000-operand disjunction against its
   left-nested binary form is regrouped, 2,100 operands exceed the
   4,096-pop operand walk; an operand with 2^17 tree nodes replays with
   enough work and is pending without it; an operand whose tree has 2^60
   nodes is pending; a 200,000-deep or chain is refused by the pop bound.
   Distinct deep operands f^d(a) and f^d(b), which pointer equality cannot
   short-circuit, on the ordered and the order-free path: at d = 4,000 the
   generated (recursive) C equality compares them at the normal stack
   (refused when the leaves differ, accepted for an unshared equal copy);
   at d = 200,000 the depth admission (4,096 levels) refuses them before
   any comparison. Atoms are distinguished by declaration parameters;
   inputs are built by tail-recursive accumulators. *)
let qi_term : A.sort = A.BaseSort "Term"

let qi_all (body:A.expr) : A.expr = A.Quantifier A.Forall_k [qi_term] A.bool_sort body

let rec qi_bools (xs:list A.expr) (acc:list A.sort) : Tot (list A.sort) (decreases xs) =
  match xs with [] -> acc | _ :: rest -> qi_bools rest (A.bool_sort :: acc)

let qi_connective (name:string) (op:A.decl_kind) (args:list A.expr) : A.expr =
  A.App { A.decl_name = name; A.domain = qi_bools args []; A.range = A.bool_sort; A.interp = Some op;
          A.int_params = [] } args

let qi_or (args:list A.expr) : A.expr = qi_connective "or" Z3ValueTheory.op_or args
let qi_and (args:list A.expr) : A.expr = qi_connective "and" Z3ValueTheory.op_and args

let qi_atom (name:string) (k:int) : A.expr =
  A.App { A.decl_name = name; A.domain = []; A.range = A.bool_sort; A.interp = None; A.int_params = [k] } []

let qi_leaf (l r:A.expr) (pad:nat) : Z3NnfReplay.verdict =
  Z3NnfReplay.replay [] ({ U.binder_entries =
      binder_entry "rewrite" (R.mk_eq_expr l r) [] ::
      { U.binder_name = "quant-intro"; U.binder_formula = R.mk_eq_expr (qi_all l) (qi_all r);
        U.binder_premises = [0]; U.binder_sorts = Some [qi_term] } ::
      padding pad [];
    U.binder_root = 1 }) (U.Equal (qi_all l) (qi_all r))

let rec qi_chain (n:nat) : Tot A.expr (decreases n) =
  let level = [qi_atom "y" n; qi_atom "z" n] in
  if n = 0 then qi_or level
  else if n % 2 = 0 then qi_or (FStar.List.Tot.append level [qi_chain (n - 1)])
  else qi_and (FStar.List.Tot.append level [qi_chain (n - 1)])

let rec qi_atoms (n:nat) (acc:list A.expr) : Tot (list A.expr) (decreases n) =
  if n = 0 then acc else qi_atoms (n - 1) (qi_atom "p" n :: acc)

let rec qi_left_nested (acc:A.expr) (xs:list A.expr) : Tot A.expr (decreases xs) =
  match xs with [] -> acc | x :: rest -> qi_left_nested (qi_or [acc; x]) rest

let qi_wide_regrouped (n:nat) : bool =
  match qi_atoms n [] with
  | [] -> false
  | x :: rest -> Z3NnfReplay.regrouped (qi_or (x :: rest)) (qi_left_nested x rest)

let rec qi_or_chain (depth:nat) (acc:A.expr) : Tot A.expr (decreases depth) =
  if depth = 0 then acc else qi_or_chain (depth - 1) (qi_or [acc; qi_atom "g" 2])

let qi_f : A.func_decl =
  { A.decl_name = "f"; A.domain = [A.bool_sort]; A.range = A.bool_sort; A.interp = None; A.int_params = [] }

let rec qi_applied (depth:nat) (acc:A.expr) : Tot A.expr (decreases depth) =
  if depth = 0 then acc else qi_applied (depth - 1) (A.App qi_f [acc])

(* The ordered (o = true) or order-free shape over the operand x on the left
   and y on the right. *)
let qi_shape (o:bool) (x y:A.expr) : A.expr & A.expr =
  let g2 = qi_atom "g" 2 in
  let g3 = qi_atom "g" 3 in
  if o then (qi_or [x; g2; g3], qi_or [qi_or [y; g2]; g3])
  else (qi_or [x; g2; g3], qi_or [g3; qi_or [g2; y]])

let qi_distinct_deep (o:bool) : bool =
  let a = qi_atom "a" 0 in
  let b = qi_atom "b" 0 in
  let (l1, r1) = qi_shape o (qi_applied 4000 a) (qi_applied 4000 b) in
  let (l2, r2) = qi_shape o (qi_applied 4000 a) (qi_applied 4000 a) in
  let (l3, r3) = qi_shape o (qi_applied 200000 a) (qi_applied 200000 b) in
  let (l4, r4) = qi_shape o (qi_applied 200000 a) (qi_applied 200000 a) in
  not (Z3NnfReplay.regrouped l1 r1) && qi_leaf l1 r1 0 = Z3NnfReplay.Unreplayed &&
  Z3NnfReplay.regrouped l2 r2 && qi_leaf l2 r2 0 = Z3NnfReplay.Replayed &&
  not (Z3NnfReplay.regrouped l3 r3) &&
  not (Z3NnfReplay.regrouped l4 r4)

let qi_regroup_scale () : bool =
  let g1 = qi_atom "g" 1 in
  let g2 = qi_atom "g" 2 in
  let g3 = qi_atom "g" 3 in
  let g4 = qi_atom "g" 4 in
  let deep = qi_chain 70 in
  let a6_l = qi_or [g1; g2; g3; deep] in
  let a6_r = qi_or [qi_or [g1; g2]; qi_or [g3; deep]] in
  let wide = shared_expression 16 g1 in
  let wide_l = qi_or [wide; g2; g3] in
  let wide_r = qi_or [qi_or [wide; g2]; g3] in
  let big = shared_expression 60 g1 in
  not (Z3NnfReplay.propositional_at 64 a6_l a6_r) &&
  not (Z3NnfReplay.propositional_at 2 a6_l a6_r) &&
  Z3NnfReplay.regrouped a6_l a6_r &&
  qi_leaf a6_l a6_r 0 = Z3NnfReplay.Replayed &&
  qi_leaf (qi_or [g1; g2; g3]) (qi_or [qi_or [g1; g2]; g4]) 0 = Z3NnfReplay.Unreplayed &&
  qi_wide_regrouped 2000 &&
  not (qi_wide_regrouped 2100) &&
  qi_leaf wide_l wide_r 2000 = Z3NnfReplay.Replayed &&
  qi_leaf wide_l wide_r 0 = Z3NnfReplay.Unreplayed &&
  qi_leaf (qi_or [big; g2]) (qi_or [qi_or [big]; g2]) 40 = Z3NnfReplay.Unreplayed &&
  not (Z3NnfReplay.regrouped (qi_or_chain 200000 g1) (qi_or [g1; g2])) &&
  qi_distinct_deep true &&
  qi_distinct_deep false

(* The premise-id boundary of the NNF replay is structural: forward, self,
   negative and missing (past the last entry) ids make a certificate
   Malformed and its document is rejected; a valid earlier id and one id
   shared by two children replay; an unsupported rule with valid ids stays
   pending (Unreplayed), and a valid certificate document is certified. *)
let nnf_premise_boundary () : bool =
  let np = R.mk_not_expr nnf_p in
  let twice = R.mk_not_expr np in
  let double (ids:list int) : Z3NnfReplay.verdict =
    nnf_verdict [binder_entry "refl" (nnf_oeq nnf_p nnf_p) []; binder_entry "nnf-neg" (nnf_oeq twice nnf_p) ids]
      1 twice nnf_p in
  let two : list A.sort = [A.bool_sort; A.bool_sort] in
  let or2 = A.App { A.decl_name = "or"; A.domain = two; A.range = A.bool_sort;
                    A.interp = Some Z3ValueTheory.op_or; A.int_params = [] } [nnf_p; nnf_p] in
  let and2 = A.App { A.decl_name = "and"; A.domain = two; A.range = A.bool_sort;
                     A.interp = Some Z3ValueTheory.op_and; A.int_params = [] } [np; np] in
  let document (ids:list int) : C.marshaled =
    let good = fixture U.Asserted in
    let certificate = { U.binder_entries = [binder_entry "refl" (nnf_oeq nnf_p nnf_p) [];
                                            binder_entry "nnf-neg" (nnf_oeq twice nnf_p) ids];
                        U.binder_root = 1 } in
    { good with C.document = { good.document with
        P.entries = [{ P.rule = U.QuantifierIntroduction certificate; P.formula = nnf_oeq twice nnf_p; P.premise_ids = [] };
                     { P.rule = U.Asserted; P.formula = R.false_expr; P.premise_ids = [] }];
        P.root = 1 } } in
  double [0] = Z3NnfReplay.Replayed &&
  nnf_verdict [binder_entry "refl" (nnf_oeq np np) []; binder_entry "nnf-neg" (nnf_oeq (R.mk_not_expr or2) and2) [0; 0]]
    1 (R.mk_not_expr or2) and2 = Z3NnfReplay.Replayed &&
  nnf_verdict [binder_entry "apply-def" (nnf_oeq nnf_p nnf_p) []; binder_entry "nnf-neg" (nnf_oeq twice nnf_p) [0]]
    1 twice nnf_p = Z3NnfReplay.Unreplayed &&
  double [1] = Z3NnfReplay.Malformed &&
  double [-1] = Z3NnfReplay.Malformed &&
  double [2] = Z3NnfReplay.Malformed &&
  double [7] = Z3NnfReplay.Malformed &&
  C.check true (document [0]) = Some 0 &&
  C.check true (document [1]) = None &&
  C.check true (document [-1]) = None &&
  C.check true (document [7]) = None &&
  P.diagnostic_result (C.diagnose true (document [0])) = Some 0 &&
  P.diagnostic_result (C.diagnose true (document [7])) = None

(* The verdict of a diagnosed document is the verdict of its check (Z3Cherry.lemma_diagnose_is_check),
   for accepted, pending and rejected documents. *)
let diagnosis_is_check (force_sorted:bool) (m:C.marshaled) : bool =
  P.diagnostic_result (C.diagnose force_sorted m) = C.check force_sorted m

(* The opt-in mode's verdict on documents without quantifier introductions is the default one. *)
let verified_is_check (force_sorted:bool) (m:C.marshaled) : bool =
  P.diagnostic_result (C.diagnose_verified force_sorted m).Z3VerifiedDocument.diagnostic = C.check force_sorted m

(* The position of the first failing definition-expansion check, 0 if none. *)
let expansion_failure () : int = Z3CheckedExpansionTests.first_failure ()

(* The base-sort name charge of the scope guard (U.sort_tasks_within) counts
   two equal names once and doubles the count (U.name_pair_units): a cost
   reduction only. For every pair below the units equal the previous charge
   name_length a + name_length b, and comparing BaseSort a with BaseSort b
   returns the previous result and work left with exactly enough work, one
   unit short (exhausted) and spare work: equal names (including
   300,000-character ones; the Cherry extraction folds equal constant
   strings into one static literal, so here equal names share storage), a
   prefix, equal lengths that differ, empty names, and non-ASCII UTF-8
   (two-byte and three-byte characters). Separately built equal strings and
   malformed byte strings (which cannot be written as F* literals) are
   covered by the OCaml bridge test. *)
let sort_eq_previous (a b:string) (w:nat) : bool =
  let units = 1 + U.name_length a + U.name_length b in
  U.sort_eq_within w (A.BaseSort a) (A.BaseSort b) =
    (if w < units then None else Some (a = b, w - units))

let pair_units_exact (a b:string) : bool =
  let units = 1 + U.name_length a + U.name_length b in
  U.name_pair_units a b = U.name_length a + U.name_length b &&
  sort_eq_previous a b (units - 1) && sort_eq_previous a b units && sort_eq_previous a b (units + 7)

let name_pair_units_scale () : bool =
  let huge_s = FStar.String.make 300000 'S' in
  let huge_s' = FStar.String.make 300000 'S' in
  let huge_t = FStar.String.make 300000 'T' in
  pair_units_exact "Term" "Term" && pair_units_exact "Term" "Term2" && pair_units_exact "Term2" "Term" &&
  pair_units_exact "abc" "abd" && pair_units_exact "" "" && pair_units_exact "" "x" &&
  pair_units_exact huge_s huge_s' && pair_units_exact huge_s huge_t &&
  pair_units_exact "é名" "é名" && pair_units_exact "é名" "é吊"

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
  binder_guard_stack () &&
  checked_name_units () &&
  verified_is_check false good && verified_is_check true good &&
  verified_is_check false bad_root && verified_is_check false missing_input &&
  verified_is_check false bad_rule && verified_is_check false pending &&
  Z3CheckedGuardTests.run () &&
  Z3CheckedGraphTests.run () &&
  Z3CheckedExpansionTests.run () &&
  nnf_replay_scale () &&
  nnf_premise_boundary () &&
  qi_regroup_scale () &&
  name_pair_units_scale () &&
  Z3NnfReplayCheckedTests.run () &&
  Z3SortedRouteTests.run ()
