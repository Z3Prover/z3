module Z3NnfAssertionReplayTests

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module O = Z3ObservationalSyntax
module NR = Z3NnfReplay
module Distinct = Z3DistinctAst

let integer : sort = SortApp IntSymbol []
let p : expr = App { decl_name = "p"; domain = []; range = bool_sort; interp = None; int_params = [] } []
let q : expr = App { decl_name = "q"; domain = []; range = bool_sort; interp = None; int_params = [] } []
let distinct_x : expr = App { decl_name = "distinct-rewrite-x"; domain = []; range = integer; interp = None; int_params = [] } []
let distinct_y : expr = App { decl_name = "distinct-rewrite-y"; domain = []; range = integer; interp = None; int_params = [] } []
let distinct_z : expr = App { decl_name = "distinct-rewrite-z"; domain = []; range = integer; interp = None; int_params = [] } []
let distinct_zero : expr = App {
  decl_name = "integer"; domain = []; range = integer;
  interp = Some Z3OperatorTags.op_num_rational; int_params = [0; 1]
} []
let distinct_binary = Distinct.mk_distinct_expr integer [distinct_x; distinct_zero]
let distinct_binary_expanded = Distinct.expanded [distinct_x; distinct_zero]
let distinct_ternary = Distinct.mk_distinct_expr integer [distinct_x; distinct_y; distinct_z]
let distinct_ternary_expanded = Distinct.expanded [distinct_x; distinct_y; distinct_z]

let binary_distinct_rewrite_is_exact ()
  : Lemma (NR.rewrite_ok distinct_binary distinct_binary_expanded /\
           not (NR.rewrite_ok distinct_binary (R.mk_eq_expr distinct_x distinct_zero)) /\
           not (NR.rewrite_ok distinct_ternary distinct_ternary_expanded)) =
  assert_norm (NR.rewrite_ok distinct_binary distinct_binary_expanded);
  assert_norm (not (NR.rewrite_ok distinct_binary (R.mk_eq_expr distinct_x distinct_zero)));
  assert_norm (not (NR.rewrite_ok distinct_ternary distinct_ternary_expanded))

let oeq (a b:expr) : expr = O.mk_oeq_expr a b
let forall_ (bs:list sort) (body:expr) : expr = Quantifier Forall_k bs bool_sort body

let be (name:string) (formula:expr) (premises:list int) : U.binder_entry =
  { U.binder_name = name; binder_formula = formula; binder_premises = premises; binder_sorts = None }

let bq (name:string) (bs:list sort) (formula:expr) (premises:list int) : U.binder_entry =
  { U.binder_name = name; binder_formula = formula; binder_premises = premises; binder_sorts = Some bs }

let refl (e:expr) : U.binder_entry = be "refl" (oeq e e) []

let cert (entries:list U.binder_entry) (root:int) : U.binder_certificate =
  { U.binder_entries = entries; binder_root = root }

let assertion_entries : list U.binder_entry =
  [be "asserted" (R.mk_eq_expr p q) [];
   refl p;
   be "mp" (R.mk_eq_expr p q) [0; 1];
   be "symm" (R.mk_eq_expr q p) [2];
   bq "quant-intro" [integer] (oeq (forall_ [integer] q) (forall_ [integer] p)) [3]]

let assertion_entries_are_guarded ()
  : Lemma (NR.replay [R.mk_eq_expr p q] (cert assertion_entries 4)
              (U.Observational (forall_ [integer] q) (forall_ [integer] p)) == NR.Replayed /\
           NR.replay [] (cert assertion_entries 4)
              (U.Observational (forall_ [integer] q) (forall_ [integer] p)) == NR.Unreplayed /\
           NR.replay [R.mk_eq_expr p p] (cert assertion_entries 4)
              (U.Observational (forall_ [integer] q) (forall_ [integer] p)) == NR.Unreplayed) =
  assert_norm (NR.replay [R.mk_eq_expr p q] (cert assertion_entries 4)
                (U.Observational (forall_ [integer] q) (forall_ [integer] p)) == NR.Replayed);
  assert_norm (NR.replay [] (cert assertion_entries 4)
                (U.Observational (forall_ [integer] q) (forall_ [integer] p)) == NR.Unreplayed);
  assert_norm (NR.replay [R.mk_eq_expr p p] (cert assertion_entries 4)
                (U.Observational (forall_ [integer] q) (forall_ [integer] p)) == NR.Unreplayed)
