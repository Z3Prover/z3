module Z3CherryTests

module A = Z3AstTheory
module P = Z3ProofDocument
module R = Z3ResolutionProofTheory
module U = Z3UnifiedProof
module C = Z3Cherry
module CR = Z3ConditionalRewrite
module N = Z3Native
module NP = Z3NativeProof
module LP = Z3LpCertificate
module L = FStar.List.Tot
module RP = Z3SortedRealProduct
module RL = Z3SortedReal

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
  if n = 0 then acc else int_sorts (n - 1) ((A.SortApp A.IntSymbol []) :: acc)

let rec nested_not (depth:nat) (acc:A.expr) : Tot A.expr (decreases depth) =
  if depth = 0 then acc else nested_not (depth - 1) (R.mk_not_expr acc)

let rec domain_nested (depth:nat) (acc:A.sort) : Tot A.sort (decreases depth) =
  if depth = 0 then acc else domain_nested (depth - 1) (A.ArraySort [acc] ((A.SortApp A.IntSymbol [])))

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
  let deep_sort = domain_nested 50000 ((A.SortApp A.IntSymbol [])) in
  let x = A.Var 0 deep_sort in
  let deep_sort_q = A.Quantifier A.Forall_k [deep_sort] A.bool_sort (R.mk_eq_expr x x) in
  hidden_term_pending (A.Quantifier A.Forall_k (int_sorts 200000 []) A.bool_sort R.true_expr) 42 = 0 &&
  hidden_term_pending (nested_not 200000 R.true_expr) 308 = 0 &&
  hidden_term_pending deep_sort_q 200 = 0 &&
  (* Structural Int comparisons need less work than the old name comparisons. *)
  hidden_term_pending deep_sort_q 40 = 1

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

(* The ITE laws of quant-intro rewrite leaves (Z3NnfReplay.ite_rewritten) at
   native scale in the Cherry checker (the OCaml counterpart is
   test_native_bridge.ml `sorted_quant_intro_ite_laws`): at sort Term the
   negated condition, the then merge by `or` and the else merge by a
   flattened `and` replay, and the then merge with its branches swapped is
   pending. Distinct guards f^d(a) and f^d(b), which pointer equality
   cannot short-circuit: at d = 4,000 the generated (recursive) C equality
   compares them at the normal stack (refused when they differ, accepted
   for an unshared equal copy); at d = 200,000 the depth admission (4,096
   levels) refuses them before any comparison. A shared guard with 2^16
   tree nodes replays with enough work and is pending without it; one with
   2^60 tree nodes is pending. *)
let qi_ite (c x y:A.expr) : A.expr = A.App (Z3SortedSemantics.ite_decl qi_term) [c; x; y]

let qi_y : A.expr = A.App { A.decl_name = "y"; A.domain = []; A.range = qi_term; A.interp = None; A.int_params = [] } []

let qi_ite_leaf (l r:A.expr) (pad:nat) : Z3NnfReplay.verdict =
  let h = A.App { A.decl_name = "h"; A.domain = []; A.range = qi_term; A.interp = None; A.int_params = [] } [] in
  let el = R.mk_eq_expr h l in
  let er = R.mk_eq_expr h r in
  Z3NnfReplay.replay [] ({ U.binder_entries =
      binder_entry "rewrite" (R.mk_eq_expr l r) [] ::
      binder_entry "monotonicity" (R.mk_eq_expr el er) [0] ::
      { U.binder_name = "quant-intro"; U.binder_formula = R.mk_eq_expr (qi_all el) (qi_all er);
        U.binder_premises = [1]; U.binder_sorts = Some [qi_term] } ::
      padding pad [];
    U.binder_root = 2 }) (U.Equal (qi_all el) (qi_all er))

let qi_ite_swap (g g':A.expr) : A.expr & A.expr =
  (qi_ite (R.mk_not_expr g) (A.Var 0 qi_term) qi_y, qi_ite g' qi_y (A.Var 0 qi_term))

let qi_ite_deep () : bool =
  let a = qi_atom "a" 0 in
  let b = qi_atom "b" 0 in
  let (l1, r1) = qi_ite_swap (qi_applied 4000 a) (qi_applied 4000 b) in
  let (l2, r2) = qi_ite_swap (qi_applied 4000 a) (qi_applied 4000 a) in
  let (l3, r3) = qi_ite_swap (qi_applied 200000 a) (qi_applied 200000 b) in
  let (l4, r4) = qi_ite_swap (qi_applied 200000 a) (qi_applied 200000 a) in
  not (Z3NnfReplay.ite_rewritten l1 r1) && qi_ite_leaf l1 r1 200 = Z3NnfReplay.Unreplayed &&
  Z3NnfReplay.ite_rewritten l2 r2 && qi_ite_leaf l2 r2 200 = Z3NnfReplay.Replayed &&
  not (Z3NnfReplay.ite_rewritten l3 r3) &&
  not (Z3NnfReplay.ite_rewritten l4 r4)

let qi_ite_scale () : bool =
  let x = A.Var 0 qi_term in
  let c1 = qi_atom "c" 1 in
  let c2 = qi_atom "c" 2 in
  let c3 = qi_atom "c" 3 in
  let c4 = qi_atom "c" 4 in
  let (l1, r1) = qi_ite_swap c1 c1 in
  let l2 = qi_ite c1 x (qi_ite c2 x qi_y) in
  let l3 = qi_ite (qi_and [c1; c3]) (qi_ite (qi_and [c2; c4]) x qi_y) qi_y in
  let (w1, w2) = qi_ite_swap (shared_expression 16 c1) (shared_expression 16 c1) in
  let (b1, b2) = qi_ite_swap (shared_expression 60 c1) (shared_expression 60 c1) in
  qi_ite_leaf l1 r1 0 = Z3NnfReplay.Replayed &&
  qi_ite_leaf l2 (qi_ite (qi_or [c1; c2]) x qi_y) 0 = Z3NnfReplay.Replayed &&
  qi_ite_leaf l3 (qi_ite (qi_and [c1; c3; c2; c4]) x qi_y) 0 = Z3NnfReplay.Replayed &&
  qi_ite_leaf l2 (qi_ite (qi_or [c1; c2]) qi_y x) 0 = Z3NnfReplay.Unreplayed &&
  qi_ite_deep () &&
  qi_ite_leaf w1 w2 2000 = Z3NnfReplay.Replayed &&
  qi_ite_leaf w1 w2 0 = Z3NnfReplay.Unreplayed &&
  qi_ite_leaf b1 b2 40 = Z3NnfReplay.Unreplayed

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

(* Typed Int/Real Farkas certificates on the forced Sorted route
   (Z3SortedProof.real_farkas inside check_document_epsilon), natively: the
   strict conflict {x > 0, x <= 0} and {x < y, y <= x} with rational weights
   are accepted; the satisfiable {0 < x, x < 1} (x = 1/2) and {x <= y, y <= x}
   (x = y), a zero weight on the strict premise, non-cancelling weights, a
   dropped premise, a counterfeit > and a same-spelled distinct constant stay
   pending. *)
let real_s : A.sort = (A.SortApp A.RealSymbol [])

let real_constant (name:string) (params:list int) : A.expr =
  A.App { A.decl_name = name; A.domain = []; A.range = real_s; A.interp = None; A.int_params = params } []

let real_numeral (n:int) (d:pos) : A.expr =
  A.App { A.decl_name = "num"; A.domain = []; A.range = real_s; A.interp = Some Z3ValueTheory.op_num_rational;
          A.int_params = [n; d] } []

let real_compare (name:string) (op:option A.decl_kind) (a b:A.expr) : A.expr =
  A.App { A.decl_name = name; A.domain = [real_s; real_s]; A.range = A.bool_sort; A.interp = op; A.int_params = [] }
    [a; b]

let real_farkas_document (a b:A.expr) (ids:list int) (cs:list Z3LinearArithmeticAst.coefficient) : C.marshaled =
  { C.document = {
      P.declarations = []; P.expressions = []; P.assertions = [a; b];
      P.entries = [{ P.rule = U.Asserted; P.formula = a; P.premise_ids = [] };
                   { P.rule = U.Asserted; P.formula = b; P.premise_ids = [] };
                   { P.rule = U.ArithmeticFarkas cs; P.formula = R.false_expr; P.premise_ids = ids }];
      P.root = 2 };
    C.schema = { Z3DatatypeSignature.sorts = []; Z3DatatypeSignature.cases = [] } }

let real_equality_controls () : bool =
  let x = real_constant "x" [] in
  let y = real_constant "y" [] in
  let zero = real_numeral 0 1 in
  let one = real_numeral 1 1 in
  let ge a b = A.App RL.real_ge_decl [a; b] in
  let le a b = A.App RL.real_le_decl [a; b] in
  let facts = [ge x one; le x one; ge y zero; le y zero] in
  let premise e : U.checked_fact = { U.conclusion = U.Holds e; U.hypotheses = [ge x one] } in
  let run kind facts =
    Z3SortedProof.check_node { Z3DatatypeSignature.sorts = []; Z3DatatypeSignature.cases = [] } []
      { U.kind = kind; U.conclusion = U.Equal one (A.App RL.real_plus_decl [x; y]);
        U.premises = L.map premise facts } in
  let preserves (result:option (U.checked_fact & nat)) = match result with
    | Some (fact, n) -> n = 0 && fact.U.hypotheses = [ge x one]
    | None -> false in
  let pending (result:option (U.checked_fact & nat)) = match result with | Some (_, n) -> n = 1 | None -> false in
  preserves (run (U.Unverified "th-lemma") facts) &&
  preserves (run U.RewriteRule facts) &&
  pending (run (U.Unverified "th-lemma") [le x one; ge y zero; le y zero]) &&
  pending (run (U.ArithmeticFarkas []) facts)

let real_product_controls () : bool =
  let x = real_constant "x" [] in
  let y = real_constant "y" [] in
  let z = real_constant "z" [] in
  let ge a b = A.App RL.real_ge_decl [a; b] in
  let le a b = A.App RL.real_le_decl [a; b] in
  let mul a b = A.App RL.real_times_decl [a; b] in
  let document a b c d : C.marshaled =
    { C.document = {
        P.declarations = []; P.expressions = []; P.assertions = [a; b; c; d];
        P.entries = [{ P.rule = U.Asserted; P.formula = a; P.premise_ids = [] };
                     { P.rule = U.Asserted; P.formula = b; P.premise_ids = [] };
                     { P.rule = U.Asserted; P.formula = c; P.premise_ids = [] };
                     { P.rule = U.Asserted; P.formula = d; P.premise_ids = [] };
                     { P.rule = U.Unverified "th-lemma"; P.formula = R.false_expr;
                       P.premise_ids = [0; 1; 2; 3] }];
        P.root = 4 };
      C.schema = { Z3DatatypeSignature.sorts = []; Z3DatatypeSignature.cases = [] } } in
  let check a b d = C.check true (document (ge z RP.zero) a b d) in
  let bound = le (mul x y) RP.zero in
  let indirect = R.mk_not_expr
    (ge (A.App RL.real_plus_decl [z; mul (A.App (RL.real_numeral_decl (-1) 1) []) x]) RP.zero) in
  let good = document (ge z RP.zero) indirect (RP.positive y) bound in
  check (RP.positive x) (RP.positive y) bound = Some 0 &&
  check indirect (R.mk_not_expr (le y RP.zero)) bound = Some 0 &&
  check (ge x RP.zero) (RP.positive y) bound = Some 1 &&
  check (RP.positive x) (ge y RP.zero) bound = Some 1 &&
  check (RP.positive x) (RP.positive y) (le (mul x z) RP.zero) = Some 1 &&
  C.check true { good with C.document = { good.document with P.assertions = [] } } = None

let real_farkas_controls () : bool =
  let x = real_constant "x" [] in
  let y = real_constant "y" [] in
  let twin = real_constant "x" [7] in
  let zero = real_numeral 0 1 in
  let one = real_numeral 1 1 in
  let gt = real_compare ">" (Some Z3ValueTheory.op_arith_gt) in
  let fake_gt = real_compare ">" None in
  let lt = real_compare "<" (Some Z3ValueTheory.op_arith_lt) in
  let le = real_compare "<=" (Some Z3ValueTheory.op_arith_le) in
  let check a b ids cs = C.check true (real_farkas_document a b ids cs) in
  check (gt x zero) (le x zero) [0; 1] [(1, 1); (1, 1)] = Some 0 &&
  check (lt x y) (le y x) [0; 1] [(1, 2); (2, 4)] = Some 0 &&
  check (lt zero x) (lt x one) [0; 1] [(1, 1); (1, 1)] = Some 1 &&
  check (le x y) (le y x) [0; 1] [(1, 1); (1, 1)] = Some 1 &&
  check (lt x y) (le y x) [0; 1] [(0, 1); (1, 1)] = Some 1 &&
  check (lt x y) (le y x) [0; 1] [(1, 2); (3, 7)] = Some 1 &&
  check (gt x zero) (le x zero) [0] [(1, 1)] = Some 1 &&
  check (fake_gt x zero) (le x zero) [0; 1] [(1, 1); (1, 1)] = Some 1 &&
  check (gt x zero) (le twin zero) [0; 1] [(1, 1); (1, 1)] = Some 1

(* The producer's premise-free closed ITE rewrite steps on the forced Sorted
   route (Z3SortedProof.ite_rewrite inside check_document_epsilon),
   natively: the else-branch merge by `and`, the then-branch merge by `or`
   and the negated-condition swap at an uninterpreted sort and at Real are
   accepted, also on a schema registering a datatype named Real (the Real
   gate closed); swapped branches, `or` for `and`, the opposite inner guard,
   a counterfeit ite and a same-spelled twin branch stay pending. *)
let ite_rewrite_document (schema:Z3DatatypeSignature.schema) (l r:A.expr) : C.marshaled =
  let e = R.mk_eq_expr l r in
  { C.document = {
      P.declarations = []; P.expressions = []; P.assertions = [R.mk_not_expr e];
      P.entries = [{ P.rule = U.Asserted; P.formula = R.mk_not_expr e; P.premise_ids = [] };
                   { P.rule = U.RewriteRule; P.formula = e; P.premise_ids = [] };
                   { P.rule = U.UnitResolution; P.formula = R.false_expr; P.premise_ids = [0; 1] }];
      P.root = 2 };
    C.schema = schema }

let direct_ite_controls () : bool =
  let core = { Z3DatatypeSignature.sorts = []; Z3DatatypeSignature.cases = [] } in
  let real_box = { A.decl_name = "real-box"; A.domain = []; A.range = real_s;
                   A.interp = Some Z3DatatypeLemma.op_constructor; A.int_params = [0; 0; 0] } in
  let is_real_box = { A.decl_name = "is-real-box"; A.domain = [real_s]; A.range = A.bool_sort;
                      A.interp = Some Z3DatatypeLemma.op_recognizer; A.int_params = [0; 0] } in
  let real_datatype = { Z3DatatypeSignature.sorts = [real_s];
                        Z3DatatypeSignature.cases = [{ Z3DatatypeSignature.constructor = real_box;
                                                       Z3DatatypeSignature.recognizer = is_real_box;
                                                       Z3DatatypeSignature.accessors = [] }] } in
  let c = qi_atom "c" 0 in
  let d = qi_atom "d" 0 in
  let x = A.App { A.decl_name = "x"; A.domain = []; A.range = qi_term; A.interp = None; A.int_params = [] } [] in
  let twin = A.App { A.decl_name = "x"; A.domain = []; A.range = qi_term; A.interp = None; A.int_params = [7] } [] in
  let rx = real_constant "x" [] in
  let ry = real_constant "y" [] in
  let rite (g a b:A.expr) : A.expr = A.App (Z3SortedSemantics.ite_decl real_s) [g; a; b] in
  let fake_ite = { Z3SortedSemantics.ite_decl qi_term with A.interp = None } in
  let check schema l r = C.check true (ite_rewrite_document schema l r) in
  check core (qi_ite c (qi_ite d x qi_y) qi_y) (qi_ite (qi_and [c; d]) x qi_y) = Some 0 &&
  check core (qi_ite c x (qi_ite d x qi_y)) (qi_ite (qi_or [c; d]) x qi_y) = Some 0 &&
  check core (qi_ite (R.mk_not_expr c) x qi_y) (qi_ite c qi_y x) = Some 0 &&
  check core (rite c (rite d rx ry) ry) (rite (qi_and [c; d]) rx ry) = Some 0 &&
  check real_datatype (qi_ite c (qi_ite d x qi_y) qi_y) (qi_ite (qi_and [c; d]) x qi_y) = Some 0 &&
  check real_datatype (qi_ite c x (qi_ite d x qi_y)) (qi_ite (qi_or [c; d]) x qi_y) = Some 0 &&
  check core (qi_ite c (qi_ite d x qi_y) qi_y) (qi_ite (qi_and [c; d]) qi_y x) = Some 1 &&
  check core (qi_ite c (qi_ite d x qi_y) qi_y) (qi_ite (qi_or [c; d]) x qi_y) = Some 1 &&
  check core (qi_ite c (qi_ite d x qi_y) qi_y) (qi_ite (qi_and [c; R.mk_not_expr d]) x qi_y) = Some 1 &&
  check core (qi_ite c (qi_ite d x qi_y) qi_y) (A.App fake_ite [qi_and [c; d]; x; qi_y]) = Some 1 &&
  check core (qi_ite c (qi_ite d x qi_y) qi_y) (qi_ite (qi_and [c; d]) twin qi_y) = Some 1

(* The Int product factor permutation natively in the Cherry checker (the
   OCaml counterparts are test_native_bridge.ml
   `sorted_int_factor_permutation` and `sorted_direct_product_rewrites`):
   quant-intro rewrite leaves under two Int binders (Z3NnfReplay.
   product_permuted) replay for the captured Euclid shape p1 * p0 ~ p0 * p1
   and a regrouped repeat, and stay pending for x*y ~ x*x and a shifted
   index; 64 factors are accepted in reverse order, 65 and a 100,000-factor
   product are refused by the factor bound, and a product candidate with a
   100,000-sort domain by its bounded admission; 64 unshared copies of a
   4,000-deep factor are accepted, and refused when one copy differs.
   Distinct factors f^d(a) and
   f^d(b), which pointer equality cannot short-circuit: at d = 4,000 the
   generated (recursive) C equality compares them at the normal stack
   (refused when they differ, accepted for an unshared equal copy); at
   d = 200,000 the depth admission (4,096 levels) refuses them before any
   comparison. A shared factor with 2^16 tree nodes replays with enough work
   and is pending without it; one with 2^60 tree nodes is pending. Closed
   premise-free RewriteRule documents (Z3SortedProof.product_rewrite on the
   forced Sorted route): x * y = y * x and a regrouped three-factor product
   are certified; x * y = x * x, a same-spelled twin factor and a look-alike
   `*` stay pending. *)
let qp_int : A.sort = A.SortApp A.IntSymbol []

let qp_mul (a b:A.expr) : A.expr =
  A.App { A.decl_name = "*"; A.domain = [qp_int; qp_int]; A.range = qp_int; A.interp = Some Z3ValueTheory.op_mul;
          A.int_params = [] } [a; b]

let rec qp_ints (xs:list A.expr) (acc:list A.sort) : Tot (list A.sort) (decreases xs) =
  match xs with [] -> acc | _ :: rest -> qp_ints rest (qp_int :: acc)

let qp_times (args:list A.expr) : A.expr =
  A.App { A.decl_name = "*"; A.domain = qp_ints args []; A.range = qp_int; A.interp = Some Z3ValueTheory.op_arith_mul;
          A.int_params = [] } args

let qp_atom (name:string) (k:int) : A.expr =
  A.App { A.decl_name = name; A.domain = []; A.range = qp_int; A.interp = None; A.int_params = [k] } []

let rec qp_atoms (n:nat) (acc:list A.expr) : Tot (list A.expr) (decreases n) =
  if n = 0 then acc else qp_atoms (n - 1) (qp_atom "v" n :: acc)

let qp_zero : A.expr =
  A.App { A.decl_name = "num"; A.domain = []; A.range = qp_int; A.interp = Some Z3ValueTheory.op_num_rational;
          A.int_params = [0; 1] } []

let qp_nonpositive (a:A.expr) : A.expr =
  A.App { A.decl_name = "<="; A.domain = [qp_int; qp_int]; A.range = A.bool_sort; A.interp = Some Z3ValueTheory.op_arith_le;
          A.int_params = [] } [a; qp_zero]

let qp_all (body:A.expr) : A.expr = A.Quantifier A.Forall_k [qp_int; qp_int] A.bool_sort body

let qp_leaf (l r:A.expr) (pad:nat) : Z3NnfReplay.verdict =
  let bl = qp_nonpositive l in
  let br = qp_nonpositive r in
  Z3NnfReplay.replay [] ({ U.binder_entries =
      binder_entry "rewrite" (R.mk_eq_expr l r) [] ::
      binder_entry "monotonicity" (R.mk_eq_expr bl br) [0] ::
      { U.binder_name = "quant-intro"; U.binder_formula = R.mk_eq_expr (qp_all bl) (qp_all br);
        U.binder_premises = [1]; U.binder_sorts = Some [qp_int; qp_int] } ::
      padding pad [];
    U.binder_root = 2 }) (U.Equal (qp_all bl) (qp_all br))

let qp_f : A.func_decl =
  { A.decl_name = "f"; A.domain = [qp_int]; A.range = qp_int; A.interp = None; A.int_params = [] }

let rec qp_applied (depth:nat) (acc:A.expr) : Tot A.expr (decreases depth) =
  if depth = 0 then acc else qp_applied (depth - 1) (A.App qp_f [acc])

let qp_shared : A.func_decl =
  { A.decl_name = "shared"; A.domain = [qp_int; qp_int]; A.range = qp_int; A.interp = None; A.int_params = [] }

let rec qp_dag (depth:nat) (acc:A.expr) : Tot A.expr (decreases depth) =
  if depth = 0 then acc else qp_dag (depth - 1) (A.App qp_shared [acc; acc])

let qp_swap (p q:A.expr) : A.expr & A.expr = (qp_mul p (qp_atom "y" 0), qp_mul (qp_atom "y" 0) q)

let rec qp_sorts (n:nat) (acc:list A.sort) : Tot (list A.sort) (decreases n) =
  if n = 0 then acc else qp_sorts (n - 1) (qp_int :: acc)

(* n unshared 4,000-deep factors f^4000(a), the one at position k f^4000(b). *)
let rec qp_copies (n k:nat) (a b:A.expr) (acc:list A.expr) : Tot (list A.expr) (decreases n) =
  if n = 0 then acc else qp_copies (n - 1) k a b (qp_applied 4000 (if n - 1 = k then b else a) :: acc)

let qi_product_scale () : bool =
  let i0 = A.Var 0 qp_int in
  let i1 = A.Var 1 qp_int in
  let a = qp_atom "a" 0 in
  let b = qp_atom "b" 0 in
  let vs64 = qp_atoms 64 [] in
  let vs65 = qp_atoms 65 [] in
  let wide = qp_times (qp_atoms 100000 []) in
  let long = A.App { A.decl_name = "*"; A.domain = qp_sorts 100000 []; A.range = qp_int;
                     A.interp = Some Z3ValueTheory.op_mul; A.int_params = [] } [a; b] in
  let (d1, e1) = qp_swap (qp_applied 4000 a) (qp_applied 4000 b) in
  let (d2, e2) = qp_swap (qp_applied 4000 a) (qp_applied 4000 a) in
  let (d3, e3) = qp_swap (qp_applied 200000 a) (qp_applied 200000 b) in
  let (d4, e4) = qp_swap (qp_applied 200000 a) (qp_applied 200000 a) in
  let (w1, w2) = qp_swap (qp_dag 16 a) (qp_dag 16 a) in
  let (b1, b2) = qp_swap (qp_dag 60 a) (qp_dag 60 a) in
  qp_leaf (qp_mul i1 i0) (qp_mul i0 i1) 0 = Z3NnfReplay.Replayed &&
  qp_leaf (qp_mul (qp_mul i1 i0) i1) (qp_mul i1 (qp_mul i0 i1)) 0 = Z3NnfReplay.Replayed &&
  qp_leaf (qp_mul i1 i0) (qp_mul i1 i1) 0 = Z3NnfReplay.Unreplayed &&
  qp_leaf (qp_mul i1 i0) (qp_mul i0 i0) 0 = Z3NnfReplay.Unreplayed &&
  Z3NnfReplay.product_permuted (qp_times vs64) (qp_times (FStar.List.Tot.rev vs64)) &&
  not (Z3NnfReplay.product_permuted (qp_times vs65) (qp_times (FStar.List.Tot.rev vs65))) &&
  not (Z3NnfReplay.product_permuted wide wide) &&
  not (Z3NnfReplay.product_permuted long long) &&
  Z3NnfReplay.product_permuted (qp_times (qp_copies 64 64 a b [])) (qp_times (qp_copies 64 64 a b [])) &&
  not (Z3NnfReplay.product_permuted (qp_times (qp_copies 64 64 a b [])) (qp_times (qp_copies 64 63 a b []))) &&
  not (Z3NnfReplay.product_permuted d1 e1) && qp_leaf d1 e1 200 = Z3NnfReplay.Unreplayed &&
  Z3NnfReplay.product_permuted d2 e2 && qp_leaf d2 e2 200 = Z3NnfReplay.Replayed &&
  not (Z3NnfReplay.product_permuted d3 e3) &&
  not (Z3NnfReplay.product_permuted d4 e4) &&
  qp_leaf w1 w2 2000 = Z3NnfReplay.Replayed &&
  qp_leaf w1 w2 0 = Z3NnfReplay.Unreplayed &&
  qp_leaf b1 b2 40 = Z3NnfReplay.Unreplayed

let direct_product_controls () : bool =
  let core = { Z3DatatypeSignature.sorts = []; Z3DatatypeSignature.cases = [] } in
  let x = qp_atom "x" 0 in
  let y = qp_atom "y" 0 in
  let z = qp_atom "z" 0 in
  let twin = qp_atom "x" 7 in
  let look_alike = A.App { A.decl_name = "*"; A.domain = [qp_int; qp_int]; A.range = qp_int;
                           A.interp = Some Z3ValueTheory.op_mul; A.int_params = [0] } [y; x] in
  let check l r = C.check true (ite_rewrite_document core l r) in
  check (qp_mul x y) (qp_mul y x) = Some 0 &&
  check (qp_mul (qp_mul x y) z) (qp_times [x; y; z]) = Some 0 &&
  check (qp_mul x y) (qp_mul x x) = Some 1 &&
  check (qp_mul x y) (qp_mul y twin) = Some 1 &&
  check (qp_mul x y) look_alike = Some 1

(* A sort merely NAMED Int is an opaque declaration identity (A.BaseSort), not the canonical Int sort:
   a product over it is no Int product, so no factor permutation. *)
let qp_named_int : A.sort = A.BaseSort "Int"

let qp_named_mul (a b:A.expr) : A.expr =
  A.App { A.decl_name = "*"; A.domain = [qp_named_int; qp_named_int]; A.range = qp_named_int;
          A.interp = Some Z3ValueTheory.op_mul; A.int_params = [] } [a; b]

let qp_named_atom (name:string) : A.expr =
  A.App { A.decl_name = name; A.domain = []; A.range = qp_named_int; A.interp = None; A.int_params = [] } []

let direct_named_int_control () : bool =
  let x = qp_named_atom "x" in
  let y = qp_named_atom "y" in
  not (Z3NnfReplay.product_permuted (qp_named_mul x y) (qp_named_mul y x)) &&
  not (Z3NnfReplay.product_permuted (qp_mul (qp_atom "x" 0) (qp_atom "y" 0)) (qp_named_mul x y))

(* elim-unused natively in the Cherry checker (the OCaml counterpart is
   test_native_bridge.ml `sorted_elim_unused`): quant-intro leaves under an
   Int binder (Z3NnfReplay.unused_eliminated) replay for the captured
   (forall [Term^k] true) = true (k = 1, 64), a lowered free index and a
   4,000-deep body; 65 binders, a dropped used binder and the reversed
   orientation stay pending, and a 200,000-deep body is refused by the depth
   admission. Closed premise-free ElimUnused documents
   (Z3SortedProof.unused_elimination on the forced Sorted route): the
   captured step is certified; a dropped used binder, the reversed
   orientation and the RewriteRule label stay pending. *)
let qe_term : A.sort = A.BaseSort "Term"

let qe_forall (bs:list A.sort) (body:A.expr) : A.expr = A.Quantifier A.Forall_k bs A.bool_sort body

let qe_pi (x:A.expr) : A.expr =
  A.App { A.decl_name = "pi"; A.domain = [qp_int]; A.range = A.bool_sort; A.interp = None; A.int_params = [] } [x]

let rec qe_terms (n:nat) (acc:list A.sort) : Tot (list A.sort) (decreases n) =
  if n = 0 then acc else qe_terms (n - 1) (qe_term :: acc)

let qe_or (a b:A.expr) : A.expr =
  A.App { A.decl_name = "or"; A.domain = [A.bool_sort; A.bool_sort]; A.range = A.bool_sort;
          A.interp = Some Z3ValueTheory.op_or; A.int_params = [] } [a; b]

let qe_leaf (q e:A.expr) (pad:nat) : Z3NnfReplay.verdict =
  let i0 = A.Var 0 qp_int in
  let lq = qe_or (qe_pi i0) q in
  let le = qe_or (qe_pi i0) e in
  Z3NnfReplay.replay [] ({ U.binder_entries =
      binder_entry "elim-unused" (R.mk_eq_expr q e) [] ::
      binder_entry "monotonicity" (R.mk_eq_expr lq le) [0] ::
      { U.binder_name = "quant-intro"; U.binder_formula = R.mk_eq_expr (qe_forall [qp_int] lq) (qe_forall [qp_int] le);
        U.binder_premises = [1]; U.binder_sorts = Some [qp_int] } ::
      padding pad [];
    U.binder_root = 2 }) (U.Equal (qe_forall [qp_int] lq) (qe_forall [qp_int] le))

let rec qe_applied (depth:nat) (acc:A.expr) : Tot A.expr (decreases depth) =
  if depth = 0 then acc else qe_applied (depth - 1) (A.App qp_f [acc])

let qi_elim_scale () : bool =
  let i0 = A.Var 0 qp_int in
  let i1 = A.Var 1 qp_int in
  qe_leaf (qe_forall [qe_term] R.true_expr) R.true_expr 0 = Z3NnfReplay.Replayed &&
  qe_leaf (qe_forall (qe_terms 64 []) R.true_expr) R.true_expr 0 = Z3NnfReplay.Replayed &&
  qe_leaf (qe_forall [qe_term] (qe_pi i1)) (qe_pi i0) 0 = Z3NnfReplay.Replayed &&
  qe_leaf (qe_forall [qe_term] (qe_pi (qe_applied 4000 i1))) (qe_pi (qe_applied 4000 i0)) 200 = Z3NnfReplay.Replayed &&
  qe_leaf (qe_forall (qe_terms 65 []) R.true_expr) R.true_expr 0 = Z3NnfReplay.Unreplayed &&
  qe_leaf (qe_forall [qp_int] (qe_pi (A.Var 0 qp_int))) R.true_expr 0 = Z3NnfReplay.Unreplayed &&
  qe_leaf R.true_expr (qe_forall [qe_term] R.true_expr) 0 = Z3NnfReplay.Unreplayed &&
  not (Z3NnfReplay.unused_eliminated (qe_forall [qe_term] (qe_pi (qe_applied 200000 i1))) (qe_pi (qe_applied 200000 i0)))

let elim_document (rule:U.rule) (q e:A.expr) : C.marshaled =
  let f = R.mk_eq_expr q e in
  { C.document = {
      P.declarations = []; P.expressions = []; P.assertions = [R.mk_not_expr f];
      P.entries = [{ P.rule = U.Asserted; P.formula = R.mk_not_expr f; P.premise_ids = [] };
                   { P.rule = rule; P.formula = f; P.premise_ids = [] };
                   { P.rule = U.UnitResolution; P.formula = R.false_expr; P.premise_ids = [0; 1] }];
      P.root = 2 };
    C.schema = { Z3DatatypeSignature.sorts = []; Z3DatatypeSignature.cases = [] } }

let direct_elim_controls () : bool =
  let captured = qe_forall [qe_term] R.true_expr in
  let used = qe_forall [qp_int] (qe_pi (A.Var 0 qp_int)) in
  C.check true (elim_document U.ElimUnused captured R.true_expr) = Some 0 &&
  C.check true (elim_document U.ElimUnused used R.true_expr) = Some 1 &&
  C.check true (elim_document U.ElimUnused R.true_expr captured) = Some 1 &&
  C.check true (elim_document U.RewriteRule captured R.true_expr) = Some 1

(* der natively in the Cherry checker (the OCaml counterpart is
   test_native_bridge.ml `sorted_der`): a quant-intro leaf under an Int
   binder (Z3NnfReplay.der_step) replays for the captured shape
   (forall [Int] (or (not (= #1 #0)) (pi #0))) = (forall [Int] (pi #1)) and,
   in the producer's flatten_or order (the last literal first),
   (forall [Int] (or (not (= #1 #0)) (pi #0) (forall [Int] (pi #1)))) =
   (forall [Int] (or (forall [Int] (pi #2)) (pi #1))); it stays pending for
   an unsubstituted, an unlifted or a literal-dropping target; closed
   premise-free DestructiveEquality documents (Z3SortedProof.der_rewrite)
   certify the step with a constant in both orders and stay pending for a
   wrong substitution, a different operator and under the RewriteRule
   label. *)
let qd_neq (a b:A.expr) : A.expr = R.mk_not_expr (R.mk_eq_expr a b)

let qd_or3 (a b c:A.expr) : A.expr =
  A.App { A.decl_name = "or"; A.domain = [A.bool_sort; A.bool_sort; A.bool_sort]; A.range = A.bool_sort;
          A.interp = Some Z3ValueTheory.op_or; A.int_params = [] } [a; b; c]

let qd_and (a b:A.expr) : A.expr =
  A.App { A.decl_name = "and"; A.domain = [A.bool_sort; A.bool_sort]; A.range = A.bool_sort;
          A.interp = Some Z3ValueTheory.op_and; A.int_params = [] } [a; b]

let qd_leaf (q e:A.expr) : Z3NnfReplay.verdict =
  let i0 = A.Var 0 qp_int in
  let lq = qe_or (qe_pi i0) q in
  let le = qe_or (qe_pi i0) e in
  Z3NnfReplay.replay [] ({ U.binder_entries =
      binder_entry "der" (R.mk_eq_expr q e) [] ::
      binder_entry "monotonicity" (R.mk_eq_expr lq le) [0] ::
      { U.binder_name = "quant-intro"; U.binder_formula = R.mk_eq_expr (qe_forall [qp_int] lq) (qe_forall [qp_int] le);
        U.binder_premises = [1]; U.binder_sorts = Some [qp_int] } :: [];
    U.binder_root = 2 }) (U.Equal (qe_forall [qp_int] lq) (qe_forall [qp_int] le))

let der_controls () : bool =
  let i0 = A.Var 0 qp_int in
  let i1 = A.Var 1 qp_int in
  let i2 = A.Var 2 qp_int in
  let k = qp_atom "k" 0 in
  let m = qp_atom "m" 0 in
  let open_q = qe_forall [qp_int] (qe_or (qd_neq i1 i0) (qe_pi i0)) in
  let closed_q = qe_forall [qp_int] (qe_or (qd_neq i0 k) (qe_pi i0)) in
  let flat_q = qe_forall [qp_int] (qd_or3 (qd_neq i1 i0) (qe_pi i0) (qe_forall [qp_int] (qe_pi i1))) in
  let closed3 = qe_forall [qp_int] (qd_or3 (qd_neq i0 k) (qe_pi i0) (qe_pi (qp_atom "n" 0))) in
  qd_leaf open_q (qe_forall [qp_int] (qe_pi i1)) = Z3NnfReplay.Replayed &&
  qd_leaf open_q (qe_forall [qp_int] (qe_pi i0)) = Z3NnfReplay.Unreplayed &&
  qd_leaf flat_q (qe_forall [qp_int] (qe_or (qe_forall [qp_int] (qe_pi i2)) (qe_pi i1))) = Z3NnfReplay.Replayed &&
  qd_leaf flat_q (qe_forall [qp_int] (qe_or (qe_forall [qp_int] (qe_pi i1)) (qe_pi i1))) = Z3NnfReplay.Unreplayed &&
  qd_leaf flat_q (qe_forall [qp_int] (qe_forall [qp_int] (qe_pi i2))) = Z3NnfReplay.Unreplayed &&
  C.check true (elim_document U.DestructiveEquality closed_q (qe_forall [qp_int] (qe_pi k))) = Some 0 &&
  C.check true (elim_document U.DestructiveEquality closed_q (qe_forall [qp_int] (qe_pi m))) = Some 1 &&
  C.check true (elim_document U.RewriteRule closed_q (qe_forall [qp_int] (qe_pi k))) = Some 1 &&
  C.check true (elim_document U.DestructiveEquality closed3
                  (qe_forall [qp_int] (qe_or (qe_pi (qp_atom "n" 0)) (qe_pi k)))) = Some 0 &&
  C.check true (elim_document U.DestructiveEquality closed3
                  (qe_forall [qp_int] (qe_or (qe_pi k) (qe_pi (qp_atom "n" 0))))) = Some 0 &&
  C.check true (elim_document U.DestructiveEquality closed3
                  (qe_forall [qp_int] (qd_and (qe_pi (qp_atom "n" 0)) (qe_pi k)))) = Some 1

(* pull-quant natively in the Cherry checker (the OCaml counterpart is
   test_native_bridge.ml `sorted_pull_quant`): a quant-intro leaf under an
   Int binder (Z3NnfReplay.pull_ok) replays for (or (pi #0) (forall [Int]
   (pi #1))) = (forall [Int] (or (pi #1) (pi #1))) and for a flattened
   nested forall, and stays pending for an unlifted child and the reversed
   orientation. *)
let qpq_leaf (e q:A.expr) : Z3NnfReplay.verdict =
  let i0 = A.Var 0 qp_int in
  let le = qe_or (qe_pi i0) e in
  let lq = qe_or (qe_pi i0) q in
  Z3NnfReplay.replay [] ({ U.binder_entries =
      binder_entry "pull-quant" (R.mk_eq_expr e q) [] ::
      binder_entry "monotonicity" (R.mk_eq_expr le lq) [0] ::
      { U.binder_name = "quant-intro"; U.binder_formula = R.mk_eq_expr (qe_forall [qp_int] le) (qe_forall [qp_int] lq);
        U.binder_premises = [1]; U.binder_sorts = Some [qp_int] } :: [];
    U.binder_root = 2 }) (U.Equal (qe_forall [qp_int] le) (qe_forall [qp_int] lq))

let pull_controls () : bool =
  let i0 = A.Var 0 qp_int in
  let i1 = A.Var 1 qp_int in
  let i2 = A.Var 2 qp_int in
  let e = qe_or (qe_pi i0) (qe_forall [qp_int] (qe_pi i1)) in
  let q = qe_forall [qp_int] (qe_or (qe_pi i1) (qe_pi i1)) in
  let nested = qe_forall [qp_int] (qe_forall [qp_int] (qe_or (qe_pi i0) (qe_pi i2))) in
  let flat = qe_forall [qp_int; qp_int] (qe_or (qe_pi i0) (qe_pi i2)) in
  qpq_leaf e q = Z3NnfReplay.Replayed &&
  qpq_leaf nested flat = Z3NnfReplay.Replayed &&
  qpq_leaf e (qe_forall [qp_int] (qe_or (qe_pi i0) (qe_pi i1))) = Z3NnfReplay.Unreplayed &&
  qpq_leaf q e = Z3NnfReplay.Unreplayed

(* Real equality/order clauses (Z3SortedProof.real_order) natively in the Cherry checker, on the forced
   Sorted route (the OCaml counterpart is test_native_bridge.ml `sorted_real_order_clauses`): the
   producer's triangle clauses over Real terms are accepted (a bound against the numeral 0 on the
   difference x + (-1)*y in either operand order, a reversed bound, the three-literal antisymmetric
   clause), and a strict bound, a wrong coefficient, a wrong target, a counterfeit `=`, a twin
   operand, a fourth literal and the closed Real gate of a schema registering a datatype named Real
   stay pending. The clause must be shallow (4,096 levels, iterative) before any comparison: with
   unshared equal deep operands f^n(a) n = 4,093 is accepted and n = 4,094 refused, a mismatch at the
   bottom of f^4093 is refused after the comparison, and 200,000 levels are refused by the walk. *)
let rec ro_bools (xs:list A.expr) (acc:list A.sort) : Tot (list A.sort) (decreases xs) =
  match xs with [] -> acc | _ :: rest -> ro_bools rest (A.bool_sort :: acc)

let ro_or (args:list A.expr) : A.expr =
  A.App { A.decl_name = "or"; A.domain = ro_bools args []; A.range = A.bool_sort;
          A.interp = Some Z3ValueTheory.op_or; A.int_params = [] } args

let ro_binary (name:string) (op:A.decl_kind) (a b:A.expr) : A.expr =
  A.App { A.decl_name = name; A.domain = [real_s; real_s]; A.range = real_s; A.interp = Some op; A.int_params = [] } [a; b]

let ro_plus (a b:A.expr) : A.expr = ro_binary "+" Z3ValueTheory.op_arith_add a b
let ro_times (a b:A.expr) : A.expr = ro_binary "*" Z3ValueTheory.op_arith_mul a b
let ro_num (n:int) : A.expr = real_numeral n 1
let ro_diff (a b:A.expr) : A.expr = ro_plus a (ro_times (ro_num (-1)) b)
let ro_eq (a b:A.expr) : A.expr = R.mk_eq_expr a b
let ro_not (a:A.expr) : A.expr = R.mk_not_expr a
let ro_le (a b:A.expr) : A.expr = real_compare "<=" (Some Z3ValueTheory.op_arith_le) a b
let ro_ge (a b:A.expr) : A.expr = real_compare ">=" (Some Z3ValueTheory.op_arith_ge) a b
let ro_lt (a b:A.expr) : A.expr = real_compare "<" (Some Z3ValueTheory.op_arith_lt) a b

let ro_f : A.func_decl =
  { A.decl_name = "f"; A.domain = [real_s]; A.range = real_s; A.interp = None; A.int_params = [] }

let rec ro_chain (n:nat) (acc:A.expr) : Tot A.expr (decreases n) =
  if n = 0 then acc else ro_chain (n - 1) (A.App ro_f [acc])

(* not (f^n(bottom) = f^n(bottom)) \/ f^n(bottom) <= f^n(other), all four chains unshared. *)
let ro_deep (n:nat) (bottom other:A.expr) : A.expr =
  ro_or [ro_not (ro_eq (ro_chain n bottom) (ro_chain n bottom)); ro_le (ro_chain n bottom) (ro_chain n other)]

let ro_clause_document (schema:Z3DatatypeSignature.schema) (clause:A.expr) : C.marshaled =
  { C.document = {
      P.declarations = []; P.expressions = []; P.assertions = [R.mk_not_expr clause];
      P.entries = [{ P.rule = U.Asserted; P.formula = R.mk_not_expr clause; P.premise_ids = [] };
                   { P.rule = U.Unverified "th-lemma"; P.formula = clause; P.premise_ids = [] };
                   { P.rule = U.UnitResolution; P.formula = R.false_expr; P.premise_ids = [0; 1] }];
      P.root = 2 };
    C.schema = schema }

let ro_real_datatype : Z3DatatypeSignature.schema =
  let real_box = { A.decl_name = "real-box"; A.domain = []; A.range = real_s;
                   A.interp = Some Z3DatatypeLemma.op_constructor; A.int_params = [0; 0; 0] } in
  let is_real_box = { A.decl_name = "is-real-box"; A.domain = [real_s]; A.range = A.bool_sort;
                      A.interp = Some Z3DatatypeLemma.op_recognizer; A.int_params = [0; 0] } in
  { Z3DatatypeSignature.sorts = [real_s];
    Z3DatatypeSignature.cases = [{ Z3DatatypeSignature.constructor = real_box;
                                   Z3DatatypeSignature.recognizer = is_real_box;
                                   Z3DatatypeSignature.accessors = [] }] }

let real_order_controls () : bool =
  let core = { Z3DatatypeSignature.sorts = []; Z3DatatypeSignature.cases = [] } in
  let x = real_constant "x" [] in
  let y = real_constant "y" [] in
  let z = real_constant "z" [] in
  let twin = real_constant "x" [7] in
  let zero = ro_num 0 in
  let fake_eq (a b:A.expr) : A.expr =
    A.App { A.decl_name = "="; A.domain = [real_s; real_s]; A.range = A.bool_sort; A.interp = None; A.int_params = [] } [a; b] in
  let check clause = C.check true (ro_clause_document core clause) in
  let a = real_constant "a" [] in
  let b = real_constant "b" [] in
  let wide = ro_or [ro_not (ro_eq x y); ro_le x y; ro_le y x; ro_le x y] in
  check (ro_or [ro_not (ro_eq x y); ro_le x y]) = Some 0 &&
  check (ro_or [ro_not (ro_eq x y); ro_ge x y]) = Some 0 &&
  check (ro_or [ro_not (ro_eq zero x); ro_ge x zero]) = Some 0 &&
  check (ro_or [ro_not (ro_eq x y); ro_ge (ro_diff x y) zero]) = Some 0 &&
  check (ro_or [ro_not (ro_eq x y); ro_le (ro_plus (ro_times (ro_num (-1)) y) x) zero]) = Some 0 &&
  check (ro_or [ro_not (ro_eq x y); ro_le (ro_diff y x) zero]) = Some 0 &&
  check (ro_or [ro_eq x y; ro_not (ro_le (ro_diff x y) zero); ro_not (ro_ge (ro_diff x y) zero)]) = Some 0 &&
  check (ro_or [ro_not (ro_le x y); ro_eq x y; ro_not (ro_le y x)]) = Some 0 &&
  check (ro_or [ro_not (ro_eq x y); ro_lt (ro_diff x y) zero]) = Some 1 &&
  check (ro_or [ro_not (ro_eq x y); ro_lt x y]) = Some 1 &&
  check (ro_or [ro_not (ro_eq x y); ro_le (ro_plus x (ro_times (ro_num 1) y)) zero]) = Some 1 &&
  check (ro_or [ro_not (ro_eq x y); ro_ge (ro_plus x (ro_times (ro_num (-2)) y)) zero]) = Some 1 &&
  check (ro_or [ro_not (ro_eq x y); ro_le (ro_diff x z) zero]) = Some 1 &&
  check (ro_or [ro_not (ro_eq x y); ro_le twin y]) = Some 1 &&
  check (ro_or [ro_not (fake_eq x y); ro_le x y]) = Some 1 &&
  check (ro_or [ro_eq x y; ro_not (ro_le (ro_diff x y) zero); ro_not (ro_ge (ro_diff y x) zero)]) = Some 1 &&
  check (ro_or [ro_eq x y; ro_le x y]) = Some 1 &&
  check wide = Some 1 &&
  C.check true (ro_clause_document ro_real_datatype (ro_or [ro_not (ro_eq x y); ro_le x y])) = Some 1 &&
  C.check true (ro_clause_document core (ro_deep 4093 a a)) = Some 0 &&
  C.check true (ro_clause_document core (ro_deep 4094 a a)) = Some 1 &&
  C.check true (ro_clause_document core (ro_deep 4093 a b)) = Some 1 &&
  Z3SortedProof.real_order_clause (ro_deep 4093 a a) &&
  not (Z3SortedProof.real_order_clause (ro_deep 4094 a a)) &&
  not (Z3SortedProof.real_order_clause (ro_deep 200000 a a))

(* Guarded Int div/mod clauses (Z3SortedProof.division_order) natively in the Cherry checker, on the
   forced Sorted route (the OCaml counterpart is test_native_bridge.ml `sorted_int_division_clauses`):
   the five producer templates over Int terms are accepted in both literal orders
     d = 0 \/ mod x d >= 0,  d <= 0 \/ (mod x d) + (-1)*d <= -1,  d >= 0 \/ (mod x d) + d <= -1,
     d = 0 \/ x = d*(div x d) + mod x d  (and the equation's sides swapped),
   and a missing guard (a unit clause), a guard of the wrong sign for its bound, a wrong bound, mod
   and div exchanged, a guard on x, a wrong operand of the decomposition, a lookalike mod (no kind
   tag, the div tag, a twin parameter, another name), a counterfeit `=` and an unguarded alias of a
   division with its div0 stay pending, as do valid clauses in an unsupported shape (a weaker guard,
   a commuted product, a third literal). The clause must be shallow (4,096 levels, iterative) before
   any comparison: with unshared equal deep operands f^n(x), f^n(d) n = 4,093 is accepted and
   n = 4,094 refused, a mismatch at the bottom of f^4093 is refused after the comparison, and
   200,000 levels are refused by the walk. *)
let dv_int : A.sort = qp_int

let dv_const (name:string) (params:list int) : A.expr =
  A.App { A.decl_name = name; A.domain = []; A.range = dv_int; A.interp = None; A.int_params = params } []

let dv_num (n:int) : A.expr =
  A.App { A.decl_name = "num"; A.domain = []; A.range = dv_int; A.interp = Some Z3ValueTheory.op_num_rational;
          A.int_params = [n; 1] } []

let dv_binary (name:string) (op:A.decl_kind) (a b:A.expr) : A.expr =
  A.App { A.decl_name = name; A.domain = [dv_int; dv_int]; A.range = dv_int; A.interp = Some op; A.int_params = [] } [a; b]

let dv_plus (a b:A.expr) : A.expr = dv_binary "+" Z3ValueTheory.op_arith_add a b
let dv_times (a b:A.expr) : A.expr = dv_binary "*" Z3ValueTheory.op_arith_mul a b
let dv_diff (a b:A.expr) : A.expr = dv_plus a (dv_times (dv_num (-1)) b)

let dv_compare (name:string) (op:option A.decl_kind) (a b:A.expr) : A.expr =
  A.App { A.decl_name = name; A.domain = [dv_int; dv_int]; A.range = A.bool_sort; A.interp = op; A.int_params = [] } [a; b]

let dv_le (a b:A.expr) : A.expr = dv_compare "<=" (Some Z3ValueTheory.op_arith_le) a b
let dv_ge (a b:A.expr) : A.expr = dv_compare ">=" (Some Z3ValueTheory.op_arith_ge) a b
let dv_lt (a b:A.expr) : A.expr = dv_compare "<" (Some Z3ValueTheory.op_arith_lt) a b

let dv_rem (a b:A.expr) : A.expr = dv_binary "mod" Z3IntegerDivision.op_mod a b
let dv_quot (a b:A.expr) : A.expr = dv_binary "div" Z3IntegerDivision.op_idiv a b

let dv_f : A.func_decl =
  { A.decl_name = "f"; A.domain = [dv_int]; A.range = dv_int; A.interp = None; A.int_params = [] }

let rec dv_chain (n:nat) (acc:A.expr) : Tot A.expr (decreases n) =
  if n = 0 then acc else dv_chain (n - 1) (A.App dv_f [acc])

(* d' = 0 \/ mod x' d'' >= 0, with f^n applied to unshared copies of x and of both d's. *)
let dv_deep (n:nat) (x d d':A.expr) : A.expr =
  ro_or [ro_eq (dv_chain n d) (dv_num 0); dv_ge (dv_rem (dv_chain n x) (dv_chain n d')) (dv_num 0)]

(* The NEW validator (Z3SortedProof.division_order, called directly) against the whole checker. A clause the new
   validator accepts must be accepted by the checker (Some 0); a clause it refuses must stay pending in the whole
   checker (Some 1), i.e. no pre-existing kernel accepts it as a fallback; anything else is None. So an expected Some 0
   is support of the new division kernel, never of an old fallback, and an expected Some 1 is refused by both. *)
let dv_node (clause:A.expr) : U.proof_node =
  { U.kind = U.Unverified "th-lemma"; U.conclusion = U.Holds clause; U.premises = [] }

let dv_check (clause:A.expr) : option nat =
  let core = { Z3DatatypeSignature.sorts = []; Z3DatatypeSignature.cases = [] } in
  let verdict = C.check true (ro_clause_document core clause) in
  if Z3SortedProof.division_order (dv_node clause)
  then (if verdict = Some 0 then Some 0 else None)
  else (if verdict = Some 1 then Some 1 else None)

let int_division_controls () : bool =
  let x = dv_const "x" [] in
  let d = dv_const "d" [] in
  let e = dv_const "e" [] in
  let zero = dv_num 0 in
  let m1 = dv_num (-1) in
  let rem_decl_with (f:A.func_decl -> A.func_decl) (a b:A.expr) : A.expr =
    match dv_rem a b with A.App k args -> A.App (f k) args | other -> other in
  let check = dv_check in
  let sum = dv_plus (dv_times d (dv_quot x d)) (dv_rem x d) in
  let lower = ro_or [ro_eq d zero; dv_ge (dv_rem x d) zero] in
  check lower = Some 0 &&
  check (ro_or [dv_ge (dv_rem x d) zero; ro_eq d zero]) = Some 0 &&
  check (ro_or [dv_le d zero; dv_le (dv_diff (dv_rem x d) d) m1]) = Some 0 &&
  check (ro_or [dv_le (dv_plus (dv_times m1 d) (dv_rem x d)) m1; dv_le d zero]) = Some 0 &&
  check (ro_or [dv_ge d zero; dv_le (dv_plus (dv_rem x d) d) m1]) = Some 0 &&
  check (ro_or [ro_eq d zero; ro_eq x sum]) = Some 0 &&
  check (ro_or [ro_eq sum x; ro_eq d zero]) = Some 0 &&
  (* a numeral divisor: the guard 3 = 0 is false and mod x 3 >= 0 is valid, a POSITIVE control accepted by the new validator *)
  check (ro_or [ro_eq (dv_num 3) zero; dv_ge (dv_rem x (dv_num 3)) zero]) = Some 0 &&
  (* the numeral instance x = 7, d = -2 (7 div -2 = -3, 7 mod -2 = 1) of every template is accepted *)
  check (ro_or [ro_eq (dv_num (-2)) zero; dv_ge (dv_rem (dv_num 7) (dv_num (-2))) zero]) = Some 0 &&
  check (ro_or [dv_ge (dv_num (-2)) zero; dv_le (dv_plus (dv_rem (dv_num 7) (dv_num (-2))) (dv_num (-2))) m1]) = Some 0 &&
  check (ro_or [dv_le (dv_num 2) zero; dv_le (dv_diff (dv_rem (dv_num 7) (dv_num 2)) (dv_num 2)) m1]) = Some 0 &&
  check (ro_or [ro_eq (dv_num (-2)) zero;
                ro_eq (dv_num 7) (dv_plus (dv_times (dv_num (-2)) (dv_quot (dv_num 7) (dv_num (-2))))
                                    (dv_rem (dv_num 7) (dv_num (-2))))]) = Some 0 &&
  (* the zero-divisor controls at numerals: no guard, or a guard on the dividend instead of the divisor *)
  check (dv_ge (dv_rem (dv_num 7) zero) zero) = Some 1 &&
  check (ro_or [ro_eq (dv_num 7) zero; dv_ge (dv_rem (dv_num 7) zero) zero]) = Some 1 &&
  check (dv_ge (dv_rem x d) zero) = Some 1 &&
  check (ro_or [ro_eq x zero; dv_ge (dv_rem x d) zero]) = Some 1 &&
  check (ro_or [dv_ge d zero; dv_le (dv_diff (dv_rem x d) d) m1]) = Some 1 &&
  check (ro_or [dv_le d zero; dv_le (dv_plus (dv_rem x d) d) m1]) = Some 1 &&
  check (ro_or [dv_le d zero; dv_le (dv_diff (dv_rem x d) d) (dv_num (-2))]) = Some 1 &&
  check (ro_or [ro_eq d zero; dv_ge (dv_quot x d) zero]) = Some 1 &&
  check (ro_or [ro_eq d zero; ro_eq x (dv_plus (dv_times d (dv_quot d x)) (dv_rem x d))]) = Some 1 &&
  check (ro_or [ro_eq d zero; ro_eq x (dv_plus (dv_times d (dv_quot x d)) (dv_times (dv_num 2) (dv_rem x d)))]) = Some 1 &&
  check (ro_eq x sum) = Some 1 &&
  check (ro_eq (dv_quot x d) (dv_binary "div0" Z3IntegerDivision.op_idiv x d)) = Some 1 &&
  check (ro_or [ro_eq d zero; dv_ge (rem_decl_with (fun k -> { k with A.interp = None }) x d) zero]) = Some 1 &&
  check (ro_or [ro_eq d zero; dv_ge (rem_decl_with (fun k -> { k with A.interp = Some Z3IntegerDivision.op_idiv }) x d) zero]) = Some 1 &&
  check (ro_or [ro_eq d zero; dv_ge (rem_decl_with (fun k -> { k with A.int_params = [1] }) x d) zero]) = Some 1 &&
  check (ro_or [ro_eq d zero; dv_ge (rem_decl_with (fun k -> { k with A.decl_name = "remainder" }) x d) zero]) = Some 1 &&
  check (ro_or [A.App { A.decl_name = "="; A.domain = [dv_int; dv_int]; A.range = A.bool_sort; A.interp = None;
                        A.int_params = [] } [d; zero]; dv_ge (dv_rem x d) zero]) = Some 1 &&
  check (ro_or [dv_le d zero; dv_ge (dv_rem x d) zero]) = Some 1 &&
  check (ro_or [ro_eq d zero; ro_eq x (dv_plus (dv_times (dv_quot x d) d) (dv_rem x d))]) = Some 1 &&
  check (ro_or [ro_eq d zero; dv_ge (dv_rem x d) zero; dv_le x zero]) = Some 1 &&
  check (ro_or [ro_eq d zero; dv_ge (dv_rem x d) (dv_num 1)]) = Some 1 &&
  check (ro_or [ro_eq e zero; dv_ge (dv_rem x d) zero]) = Some 1 &&
  check (dv_deep 4093 x d d) = Some 0 &&
  check (dv_deep 4094 x d d) = Some 1 &&
  check (dv_deep 4093 x d e) = Some 1 &&
  Z3SortedProof.division_clause (dv_deep 4093 x d d) &&
  not (Z3SortedProof.division_clause (dv_deep 4094 x d d)) &&
  not (Z3SortedProof.division_clause (dv_deep 200000 x d d))

(* Real equation rewrites (Z3SortedRealLinear.real_equivalent) natively on the forced Sorted route:
   the renormalized, commuted and proportional difference forms and the equations of constants are
   accepted as closed premise-free rewrite steps; a wrong sign, offset, target and constant, a
   counterfeit `=` and the closed Real gate stay pending. A quant-intro leaf with a Real equation
   under two Real binders replays with the Real gate and not without it, its mutants not at all. *)
let re_all (body:A.expr) : A.expr = A.Quantifier A.Forall_k [real_s; real_s] A.bool_sort body

let re_leaf (gate:bool) (l r:A.expr) : Z3NnfReplay.verdict =
  Z3NnfReplay.replay_with gate [] ({ U.binder_entries =
      binder_entry "rewrite" (R.mk_eq_expr l r) [] ::
      { U.binder_name = "quant-intro"; U.binder_formula = R.mk_eq_expr (re_all l) (re_all r);
        U.binder_premises = [0]; U.binder_sorts = Some [real_s; real_s] } :: [];
    U.binder_root = 1 }) (U.Equal (re_all l) (re_all r))

let real_equation_controls () : bool =
  let core = { Z3DatatypeSignature.sorts = []; Z3DatatypeSignature.cases = [] } in
  let x = real_constant "x" [] in
  let y = real_constant "y" [] in
  let z = real_constant "z" [] in
  let zero = ro_num 0 in
  let check l r = C.check true (ite_rewrite_document core l r) in
  let fake_eq (a b:A.expr) : A.expr =
    A.App { A.decl_name = "="; A.domain = [real_s; real_s]; A.range = A.bool_sort; A.interp = None; A.int_params = [] } [a; b] in
  let v0 = A.Var 0 real_s in
  let v1 = A.Var 1 real_s in
  check (ro_eq x y) (ro_eq (ro_diff x y) zero) = Some 0 &&
  check (ro_eq x (ro_times (ro_num 2) y)) (ro_eq (ro_plus x (ro_times (ro_num (-2)) y)) zero) = Some 0 &&
  check (ro_eq x y) (ro_eq y x) = Some 0 &&
  check (ro_eq x y) (ro_eq (ro_plus (ro_times (ro_num 3) x) (ro_times (ro_num (-3)) y)) zero) = Some 0 &&
  check (ro_eq (ro_num 2) zero) R.false_expr = Some 0 &&
  check (ro_eq (ro_num 2) (ro_num 2)) R.true_expr = Some 0 &&
  check (ro_eq (real_numeral 1 2) (real_numeral 2 4)) R.true_expr = Some 0 &&
  check (ro_eq x y) (ro_eq (ro_plus x y) zero) = Some 1 &&
  check (ro_eq x y) (ro_eq (ro_diff x y) (ro_num 1)) = Some 1 &&
  check (ro_eq x y) (ro_eq (ro_diff x z) zero) = Some 1 &&
  check (ro_eq (ro_num 2) zero) R.true_expr = Some 1 &&
  check (ro_eq (ro_num 2) (ro_num 2)) R.false_expr = Some 1 &&
  check (fake_eq x y) (ro_eq (ro_diff x y) zero) = Some 1 &&
  C.check true (ite_rewrite_document ro_real_datatype (ro_eq x y) (ro_eq (ro_diff x y) zero)) = Some 1 &&
  re_leaf true (ro_eq v0 (ro_times (ro_num 2) v1)) (ro_eq (ro_plus v0 (ro_times (ro_num (-2)) v1)) zero) =
    Z3NnfReplay.Replayed &&
  re_leaf false (ro_eq v0 (ro_times (ro_num 2) v1)) (ro_eq (ro_plus v0 (ro_times (ro_num (-2)) v1)) zero) =
    Z3NnfReplay.Unreplayed &&
  re_leaf true (ro_eq v0 (ro_times (ro_num 2) v1)) (ro_eq (ro_plus v0 (ro_times (ro_num 2) v1)) zero) =
    Z3NnfReplay.Unreplayed &&
  re_leaf true (ro_eq v0 (ro_times (ro_num 2) v1)) (ro_eq (ro_plus v0 (ro_times (ro_num (-2)) v1)) (ro_num 1)) =
    Z3NnfReplay.Unreplayed &&
  re_leaf true (ro_eq v0 (ro_times (ro_num 2) v1)) (ro_eq (ro_plus v1 (ro_times (ro_num (-2)) v0)) zero) =
    Z3NnfReplay.Unreplayed

(* Native LP contexts, through Z3NativeProof.marshal_parameters and parameter_expressions.
   An LP context has one native parameter per coefficient, index and variable: 83,270 for
   the Pulse query FStar.UInt128-3 (14,347 of them expressions). A walk that used one C
   stack frame per parameter overflowed the normal 8 MiB stack on it (the frame is 96 to
   128 bytes, depending on the C compiler, so 65,000 to 87,000 parameters are enough).
   Both walks are tail recursive now. The two ASTs come from the native test (real Z3 ASTs,
   `false` and `true`); every list is built here. Their elements interleave every kind of
   parameter with repeated expressions, negative, huge and zero denominators (marshaling
   carries them verbatim; only the certificate decoder judges them), so the result must
   keep each parameter's kind, content and position. *)
let big_numerator : int = 123456789012345678901234567890

(* Parameter i of the mixed list: an expression at every sixth position. *)
let parameter_at (a0 a1:N.ast) (i:nat) : N.parameter_view =
  if i % 6 = 0 then N.ParameterExpression (if i % 12 = 0 then a0 else a1)
  else if i % 6 = 3 then N.ParameterUnsupported
  else if i % 6 = 5 then N.ParameterRational big_numerator (0 - (i % 7))
  else N.ParameterRational (i - 40) (1 + i % 4)

let expected_parameter (e0 e1:A.expr) (i:nat) : LP.raw_parameter =
  if i % 6 = 0 then LP.Expression (if i % 12 = 0 then e0 else e1)
  else if i % 6 = 3 then LP.Unsupported
  else if i % 6 = 5 then LP.Rational big_numerator (0 - (i % 7))
  else LP.Rational (i - 40) (1 + i % 4)

let rec mixed_parameters (a0 a1:N.ast) (count:nat) (acc:list N.parameter_view)
  : Tot (list N.parameter_view) (decreases count) =
  if count = 0 then acc
  else mixed_parameters a0 a1 (count - 1) (parameter_at a0 a1 (count - 1) :: acc)

(* Only expressions, alternating a0 and a1: the walk that collects them has most to do. *)
let rec dense_parameters (a0 a1:N.ast) (count:nat) (acc:list N.parameter_view)
  : Tot (list N.parameter_view) (decreases count) =
  if count = 0 then acc
  else dense_parameters a0 a1 (count - 1)
         (N.ParameterExpression (if (count - 1) % 2 = 0 then a0 else a1) :: acc)

let rec parameters_match (e0 e1:A.expr) (n i:nat) (raw:list LP.raw_parameter)
  : Tot bool (decreases raw) =
  match raw with
  | [] -> i = n
  | r :: rest ->
    if r = expected_parameter e0 e1 i then parameters_match e0 e1 n (i + 1) rest else false

(* The j-th expression parameter is a0 for even j and a1 for odd j, in both lists. *)
let rec expressions_match (a0 a1:N.ast) (n j:nat) (xs:list N.ast) : FStar.All.ML bool =
  match xs with
  | [] -> j = n
  | x :: rest ->
    if N.ast_id x = N.ast_id (if j % 2 = 0 then a0 else a1)
    then expressions_match a0 a1 n (j + 1) rest else false

let native_parameters ([@@@FStar.Attributes.cherry_borrowed] asts:list N.ast) : FStar.All.ML bool =
  match asts with
  | [a0; a1] ->
    let st = NP.marshal_expressions (NP.empty_state ()) asts in
    let e0 = NP.cached_expression st a0 in
    let e1 = NP.cached_expression st a1 in
    let small = [N.ParameterRational (-3) 4; N.ParameterExpression a0; N.ParameterUnsupported;
                 N.ParameterExpression a1; N.ParameterRational big_numerator (-2);
                 N.ParameterRational 0 0; N.ParameterExpression a0] in
    let small_raw = [LP.Rational (-3) 4; LP.Expression e0; LP.Unsupported; LP.Expression e1;
                     LP.Rational big_numerator (-2); LP.Rational 0 0; LP.Expression e0] in
    let count = 200000 in
    let mixed = mixed_parameters a0 a1 count [] in
    let dense = dense_parameters a0 a1 400000 [] in
    NP.marshal_parameters st [] = [] &&
    NP.marshal_parameters st small = small_raw &&
    expressions_match a0 a1 3 0 (NP.parameter_expressions small) &&
    expressions_match a0 a1 0 0 (NP.parameter_expressions []) &&
    parameters_match e0 e1 count 0 (NP.marshal_parameters st mixed) &&
    expressions_match a0 a1 ((count + 5) / 6) 0 (NP.parameter_expressions mixed) &&
    expressions_match a0 a1 400000 0 (NP.parameter_expressions dense)
  | _ -> false

(* The certificate decoder (Z3LpCertificate.decode) reads every count-prefixed list in a loop. A
   certificate with 14,347 variables overflowed the normal stack near 26,000 elements of one list
   (four C frames per element); the list below has 100,000 coefficient terms. The two variables are
   Int constants; the second one's definition is the terms (k + 1)/1 * variable 0 for k < 100,000,
   so the decoded polynomial must keep every term and its position. The one step is a plain input. *)
let lp_rat (n:int) : LP.raw_parameter = LP.Rational n 1

let lp_int_constant (name:string) : A.expr =
  A.App { A.decl_name = name; A.domain = []; A.range = Z3LinearArithmeticAst.int_s;
          A.interp = None; A.int_params = [] } []

let lp_absent : int = 4294967295

let lp_input_step : list LP.raw_parameter =
  [lp_rat 0;
   lp_rat 0; lp_rat 0; lp_rat 0; lp_rat 0; lp_rat 0;
   lp_rat 0; lp_rat lp_absent; lp_rat 0;
   lp_rat 0; lp_rat 0; lp_rat 0; lp_rat 0; lp_rat 0;
   lp_rat lp_absent; lp_rat lp_absent; lp_rat lp_absent;
   lp_rat 1; lp_rat 0; lp_rat 0]

let rec lp_terms (count:nat) (acc:list LP.raw_parameter)
  : Tot (list LP.raw_parameter) (decreases count) =
  if count = 0 then acc
  else lp_terms (count - 1) (lp_rat count :: lp_rat 0 :: acc)

let lp_certificate (declared terms:nat) : list LP.raw_parameter =
  let x0 = lp_int_constant "x0" in
  let x1 = lp_int_constant "x1" in
  Z3List.append
    [lp_rat 1; lp_rat 2; LP.Expression x0; lp_rat 1; lp_rat 0; LP.Expression x1; lp_rat 1; lp_rat declared]
    (Z3List.append (lp_terms terms [])
       (Z3List.append [lp_rat 0; lp_rat 1] (Z3List.append lp_input_step [lp_rat 0])))

let rec lp_terms_match (k n:nat) (p:LP.polynomial) : Tot bool (decreases p) =
  match p with
  | [] -> k = n
  | ((c, d), j) :: rest ->
    if c = k + 1 && d = 1 && j = 0 then lp_terms_match (k + 1) n rest else false

let lp_decode_scale () : bool =
  let terms = 100000 in
  let kept (declared count:nat) : bool =
    match LP.decode (lp_certificate declared count) with
    | Some c ->
      (match c.LP.variables with
       | [_; v] -> L.length c.LP.steps = 1 && lp_terms_match 0 count v.LP.definition
       | _ -> false)
    | None -> false in
  kept 2 2 && kept terms terms &&
  (* a declared length beyond the parameters, or too few terms for it, is refused *)
  None? (LP.decode (lp_certificate (terms + 1) terms)) &&
  None? (LP.decode (lp_certificate (terms - 1) terms))

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
  nnf_replay_scale () &&
  nnf_premise_boundary () &&
  qi_regroup_scale () &&
  qi_ite_scale () &&
  real_farkas_controls () &&
  real_equality_controls () &&
  real_product_controls () &&
  real_order_controls () &&
  real_equation_controls () &&
  int_division_controls () &&
  direct_ite_controls () &&
  qi_product_scale () &&
  direct_product_controls () &&
  direct_named_int_control () &&
  qi_elim_scale () &&
  direct_elim_controls () &&
  der_controls () &&
  pull_controls () &&
  name_pair_units_scale () &&
  lp_decode_scale ()
