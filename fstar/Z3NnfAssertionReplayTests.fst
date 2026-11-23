module Z3NnfAssertionReplayTests

open Z3AstTheory
module TR = Z3TypedRoot
module U = Z3UnifiedProof
module R = Z3ResolutionProofTheory
module O = Z3ObservationalEquality
module NR = Z3NnfReplay

let integer : sort = TR.int_s
let p : expr = App { decl_name = "p"; domain = []; range = bool_sort; interp = None; int_params = [] } []
let q : expr = App { decl_name = "q"; domain = []; range = bool_sort; interp = None; int_params = [] } []

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
