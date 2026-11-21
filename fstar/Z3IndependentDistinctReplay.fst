module Z3IndependentDistinctReplay

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module D = Z3ExprScope
module A = Z3DistinctAst
module T = Z3SortedSemantics
module K = Z3SortedDistinct
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module SR = Z3SortedRoot

let eligible (entry:P.entry) : bool =
  entry.P.rule = U.RewriteRule && entry.P.premise_ids = [] &&
  (match entry.P.formula with
   | App f [a; b] -> f = R.eq_decl bool_sort && A.duplicate_rewrite a b &&
                      D.scoped [] entry.P.formula
   | _ -> false)

let rec extra_assertions (entries:list P.entry) : Tot (list expr) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    if eligible e then e.P.formula :: extra_assertions rest else extra_assertions rest

let rec any_candidate (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest -> eligible e || any_candidate rest

let has_candidates (doc:P.document) : bool = any_candidate doc.P.entries

let rec replay_entries_acc (entries:list P.entry) (acc:list P.entry)
  : Tot (list P.entry) (decreases entries) =
  match entries with
  | [] -> acc
  | e :: rest ->
    replay_entries_acc rest ((if eligible e then { e with P.rule = U.Asserted } else e) :: acc)

let replay_entries (entries:list P.entry) : list P.entry =
  rev (replay_entries_acc entries [])

let augment (doc:P.document) : P.document =
  { doc with P.assertions = doc.P.assertions @ extra_assertions doc.P.entries;
             P.entries = replay_entries doc.P.entries }

let lemma_eligible (u:TR.uninterpreted) (schema:S.checked_schema) (model:TR.interp u schema)
                   (entry:P.entry)
  : Lemma (requires eligible entry /\ TR.root_model u schema model /\
                    K.model schema (TR.booleans u) (SR.root_scalars u) model)
          (ensures Root.root_holds u schema model entry.P.formula) =
  match entry.P.formula with
  | App _ [a; b] ->
    let rho = Root.empty_root u schema in
    K.lemma_duplicate_rewrite schema (TR.booleans u) (SR.root_scalars u) model [] rho a b;
    T.lemma_boolean_equality_at schema (TR.booleans u) (SR.root_scalars u) model [] rho a b;
    Root.lemma_holds_agreement u schema model entry.P.formula
  | _ -> ()

let rec lemma_extras (u:TR.uninterpreted) (schema:S.checked_schema) (model:TR.interp u schema)
                     (entries:list P.entry)
  : Lemma (requires TR.root_model u schema model /\
                    K.model schema (TR.booleans u) (SR.root_scalars u) model)
          (ensures Root.root_truths u schema model (extra_assertions entries))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    if eligible e then lemma_eligible u schema model e;
    lemma_extras u schema model rest

let rec lemma_append (u:TR.uninterpreted) (schema:S.checked_schema) (model:TR.interp u schema)
                     (xs ys:list expr)
  : Lemma (Root.root_truths u schema model (xs @ ys) ==
           (Root.root_truths u schema model xs && Root.root_truths u schema model ys))
          (decreases xs) =
  match xs with [] -> () | _ :: rest -> lemma_append u schema model rest ys

let lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
                    (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires Root.check_root_document_epsilon schema (augment doc) == Root.RootCertified /\
                    TR.root_model u schema model /\
                    K.model schema (TR.booleans u) (SR.root_scalars u) model)
          (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  lemma_extras u schema model doc.P.entries;
  lemma_append u schema model doc.P.assertions (extra_assertions doc.P.entries);
  Root.lemma_root_certified_epsilon u schema (augment doc) model

let test_augmentation () : Lemma True =
  let int_s = SortApp IntSymbol [] in
  let x = App { decl_name = "x"; domain = []; range = int_s;
                interp = None; int_params = [] } [] in
  let y = App { decl_name = "y"; domain = []; range = int_s;
                interp = None; int_params = [] } [] in
  let eq a b = App (R.eq_decl bool_sort) [a; b] in
  let distinct = A.mk_distinct_expr int_s [x; y; x] in
  let formula = eq distinct R.false_expr in
  let entry = { P.rule = U.RewriteRule; P.formula = formula; P.premise_ids = [] } in
  let doc = { P.declarations = []; P.expressions = [];
              P.assertions = []; P.entries = [entry]; P.root = 0 } in
  assert_norm (eligible entry);
  assert_norm (has_candidates doc);
  assert_norm ((augment doc).P.assertions = [formula]);
  assert_norm ((augment doc).P.entries = [{ entry with P.rule = U.Asserted }]);
  assert_norm (not (eligible { entry with P.premise_ids = [0] }));
  assert_norm (not (eligible { entry with P.rule = U.Hypothesis }));
  assert_norm (not (eligible { entry with P.formula = eq (A.mk_distinct_expr int_s [x; y]) R.false_expr }));
  assert_norm (not (eligible { entry with P.formula = eq distinct R.true_expr }));
  assert_norm (not (eligible { entry with P.formula =
    eq (App { A.distinct_decl int_s 3 with int_params = [1] } [x; y; x]) R.false_expr }));
  assert_norm (not (eligible { entry with P.formula =
    eq (A.mk_distinct_expr int_s [Var 0 int_s; Var 0 int_s]) R.false_expr }))

let test_int_sort = SortApp IntSymbol []
let test_x = App { decl_name = "x"; domain = []; range = test_int_sort;
                   interp = None; int_params = [] } []
let test_distinct = A.mk_distinct_expr test_int_sort [test_x; test_x]
let test_formula = App (R.eq_decl bool_sort) [test_distinct; R.false_expr]
let test_negated = R.mk_not_expr test_formula
let test_rewrite = { P.rule = U.RewriteRule; P.formula = test_formula; P.premise_ids = [] }
let test_refutation = { P.declarations = []; P.expressions = []; P.assertions = [test_negated];
  P.entries = [test_rewrite; { test_rewrite with P.rule = U.Asserted; P.formula = test_negated };
               { test_rewrite with P.rule = U.UnitResolution; P.formula = R.false_expr;
                                   P.premise_ids = [0; 1] }]; P.root = 2 }
let test_schema = { S.sorts = []; S.cases = [] }
let test_unsupported_sort = ArraySort [] test_int_sort
let test_unsupported = Quantifier Forall_k [test_unsupported_sort] bool_sort
  (App { decl_name = "q"; domain = [test_unsupported_sort]; range = bool_sort;
         interp = None; int_params = [] } [Var 0 test_unsupported_sort])

let test_refutation_replay () : Lemma True =
  assert_norm (Root.check_root_document_epsilon test_schema test_refutation = Root.RootPending 1);
  assert_norm (Root.check_root_document_epsilon test_schema (augment test_refutation) = Root.RootCertified);
  assert_norm (Root.check_root_document_epsilon test_schema
    (augment { test_refutation with P.assertions = [test_negated; test_unsupported] }) = Root.RootUncovered)
