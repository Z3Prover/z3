module Z3BoundedBoolEquivTests

open Z3BoundedBoolEquiv
module Ast = Z3AstTheory
module Basic = Z3BasicExprTheory

let rec domain (arity:nat) : Tot (list Ast.sort) (decreases arity) =
  if arity = 0 then [] else Ast.bool_sort :: domain (arity - 1)

let decl (op:Basic.basic_op) (arity:nat) : Ast.func_decl =
  { decl_name = "boolean";
    domain = domain arity;
    range = Ast.bool_sort;
    interp = Some (Basic.decl_kind_of op);
    int_params = [] }

let app (op:Basic.basic_op) (args:list expr) : expr =
  Ast.App (decl op (FStar.List.Tot.length args)) args

let atom (n:nat) : expr =
  Ast.Var n Ast.bool_sort

let literal (b:bool) : expr =
  app (if b then Basic.Op_true else Basic.Op_false) []

let conj (args:list expr) : expr = app Basic.Op_and args
let disj (args:list expr) : expr = app Basic.Op_or args
let xor (args:list expr) : expr = app Basic.Op_xor args
let neg (a:expr) : expr = app Basic.Op_not [a]
let implies (a b:expr) : expr = app Basic.Op_implies [a; b]
let iff (a b:expr) : expr = app Basic.Op_eq [a; b]

let p : expr = atom 0
let q : expr = atom 1
let r : expr = atom 2

let test_connectives () : Lemma True =
  assert_norm (bounded_bool_equiv 2 3
    (neg (conj [p; q; r])) (disj [neg p; neg q; neg r]));
  assert_norm (bounded_bool_equiv 3 3
    (conj [p; disj [q; r]]) (disj [conj [p; q]; conj [p; r]]));
  assert_norm (bounded_bool_equiv 3 3
    (xor [p; q; r]) (neg (iff (xor [p; q]) r)));
  assert_norm (bounded_bool_equiv 2 2
    (implies p q) (disj [neg p; q]));
  assert_norm (bounded_bool_equiv 2 2
    (iff p q) (conj [implies p q; implies q p]));
  assert_norm (bounded_bool_equiv 1 1 (xor [p; p; p]) p);
  assert_norm (bounded_bool_equiv 1 2 (conj [p; q; p]) (conj [q; p]))

let test_empty_and_constant () : Lemma True =
  assert_norm (bounded_bool_equiv 1 0 (conj []) (literal true));
  assert_norm (bounded_bool_equiv 1 0 (disj []) (literal false));
  assert_norm (bounded_bool_equiv 1 0 (xor []) (literal false));
  assert_norm (bounded_bool_equiv 1 0 (neg (literal false)) (literal true));
  assert_norm (not (bounded_bool_equiv 0 0 (literal false) (literal true)));
  assert_norm (bounded_bool_equiv 0 0 (conj [p; q]) (conj [p; q]))

let deep : expr = implies (xor [p; q; r]) (conj [p; neg q])

let test_frontier_and_budgets () : Lemma True =
  assert_norm (bounded_bool_equiv 1 1
    (conj [deep; deep]) (disj [deep]));
  assert_norm (not (bounded_bool_equiv 1 0
    (conj [deep; deep]) (disj [deep])));
  assert_norm (not (bounded_bool_equiv 0 3
    (conj [p; q]) (conj [q; p])));
  assert_norm (not (bounded_bool_equiv 2 1
    (implies p q) (disj [neg p; q])));
  assert_norm (not (bounded_bool_equiv 3 3 p q));
  assert_norm (not (bounded_bool_equiv 3 3 p (neg p)));
  assert_norm (not (bounded_bool_equiv 3 3
    (xor [p; q; r]) (disj [p; q; r])))

let test_expected_depths () : Lemma True =
  assert_norm (bounded_bool_equiv 3 3 (xor [p; q; r]) (xor [r; p; q]));
  assert_norm (bounded_bool_equiv 4 3 (xor [p; q; r]) (xor [r; p; q]));
  assert_norm (bounded_bool_equiv 5 3 (xor [p; q; r]) (xor [r; p; q]));
  assert_norm (bounded_bool_equiv 6 3 (xor [p; q; r]) (xor [r; p; q]))

let ten : list expr =
  [atom 0; atom 1; atom 2; atom 3; atom 4;
   atom 5; atom 6; atom 7; atom 8; atom 9]

let test_1024_rows () : Lemma True =
  assert_norm (bounded_bool_equiv 2 10
    (neg (conj ten)) (disj (FStar.List.Tot.map neg ten)));
  assert_norm (not (bounded_bool_equiv 2 9
    (neg (conj ten)) (disj (FStar.List.Tot.map neg ten))))

let spoofed_and : expr =
  Ast.App { (decl Basic.Op_and 2) with decl_name = "and"; interp = None } [p; q]

let int_eq : expr =
  Ast.App
    { (decl Basic.Op_eq 2) with
      domain = [Ast.BaseSort "Int"; Ast.BaseSort "Int"] }
    [Ast.Var 0 (Ast.BaseSort "Int"); Ast.Var 1 (Ast.BaseSort "Int")]

let quantified : expr =
  Ast.Quantifier Ast.Forall_k [Ast.bool_sort] Ast.bool_sort (iff p p)

let test_native_ast () : Lemma True =
  assert_norm (cut 6 spoofed_and = Atom spoofed_and);
  assert_norm (cut 6 int_eq = Atom int_eq);
  assert_norm (cut 6 quantified = Atom quantified);
  assert_norm (bounded_bool_equiv 2 1 (neg (neg quantified)) quantified);
  assert_norm (bounded_bool_equiv 2 1 (neg (neg int_eq)) int_eq);
  assert_norm (not (bounded_bool_equiv 2 2 spoofed_and (conj [p; q])));
  assert_norm (cut 6 (Ast.App (decl Basic.Op_not 1) [p; q]) =
    Atom (Ast.App (decl Basic.Op_not 1) [p; q]));
  assert_norm (cut 6 (Ast.App (decl Basic.Op_and 2)
    [p; Ast.Var 0 (Ast.BaseSort "Int")]) =
    Atom (Ast.App (decl Basic.Op_and 2)
      [p; Ast.Var 0 (Ast.BaseSort "Int")]));
  assert_norm (not (bounded_bool_equiv 2 2
    (Ast.Var 0 (Ast.BaseSort "Int")) (Ast.Var 1 (Ast.BaseSort "Int"))))

let test_native_evaluation (fallback:Ast.interpretation bool) (rho:Ast.env bool)
  : Lemma
      (Ast.eval (boolean_interpretation fallback) (implies p q) rho ==
       Ast.eval (boolean_interpretation fallback) (disj [neg p; q]) rho)
= assert_norm (bounded_bool_equiv 2 2 (implies p q) (disj [neg p; q]));
  lemma_bounded_bool_equiv_boolean_sound 2 2
    (implies p q) (disj [neg p; q]) fallback rho

let rec neg_chain (n:nat) (e:expr) : Tot expr (decreases n) =
  if n = 0 then e else neg (neg_chain (n - 1) e)

let large_shared : expr = neg_chain 40 (conj ten)
let y : expr = atom 100
let z : expr = atom 101

let shared_lhs : expr = conj [disj [conj [large_shared; y]; z]; y]
let shared_rhs : expr = conj [y; disj [large_shared; z]]
let shared_boundaries = common_boundaries 3 shared_lhs shared_rhs
let shared_cs = cut_with_boundaries shared_boundaries 3 shared_lhs
let shared_ct = cut_with_boundaries shared_boundaries 3 shared_rhs
let nested_boundaries = common_boundaries 6 (conj [deep; deep]) (disj [deep])
let hidden_shared : expr =
  Ast.Quantifier Ast.Forall_k [Ast.bool_sort] Ast.bool_sort large_shared
let malformed_shared : expr =
  Ast.App (decl Basic.Op_not 1) [large_shared; y]

let test_shared_outermost_boundary () : Lemma True =
  assert_norm (FStar.List.Tot.mem large_shared shared_boundaries);
  assert_norm (shared_cs =
    Nary And [Nary Or [Nary And [Atom large_shared; Atom y]; Atom z]; Atom y]);
  assert_norm (shared_ct =
    Nary And [Atom y; Nary Or [Atom large_shared; Atom z]]);
  assert_norm (FStar.List.Tot.length
    (unique (FStar.List.Tot.append (support shared_cs) (support shared_ct))) = 3);
  assert_norm (bounded_bool_equiv 3 3 shared_lhs shared_rhs);
  assert_norm (bounded_bool_equiv 4 3 shared_lhs shared_rhs);
  assert_norm (bounded_bool_equiv 6 3 shared_lhs shared_rhs);
  assert_norm (not (bounded_bool_equiv 3 2 shared_lhs shared_rhs));
  assert_norm (not (FStar.List.Tot.mem large_shared
    (common_boundaries 2 shared_lhs shared_rhs)));
  assert_norm (not (bounded_bool_equiv 2 3 shared_lhs shared_rhs))

let test_root_boundary_and_nested_candidates () : Lemma True =
  assert_norm (bounded_bool_equiv 1 1 (conj [large_shared; large_shared])
    large_shared);
  assert_norm (bounded_bool_equiv 1 1 large_shared
    (conj [large_shared; large_shared]));
  assert_norm (FStar.List.Tot.mem deep nested_boundaries);
  assert_norm (FStar.List.Tot.mem p nested_boundaries);
  assert_norm (cut_with_boundaries nested_boundaries 6 (conj [deep; deep]) =
    Nary And [Atom deep; Atom deep]);
  assert_norm (cut_with_boundaries nested_boundaries 6 (disj [deep]) =
    Nary Or [Atom deep]);
  assert_norm (bounded_bool_equiv 6 1 (conj [deep; deep]) (disj [deep]));
  assert_norm (not (bounded_bool_equiv 3 2
    (disj [disj [p; q]; p]) (disj [p; q])))

let test_bounded_candidate_discovery () : Lemma True =
  assert_norm (candidate_nodes 0 large_shared = [large_shared]);
  assert_norm (candidate_nodes 6 (literal true) = []);
  assert_norm (candidate_nodes 6 hidden_shared = [hidden_shared]);
  assert_norm (not (FStar.List.Tot.mem large_shared
    (common_boundaries 6 hidden_shared (neg large_shared))));
  assert_norm (candidate_nodes 6 malformed_shared = [malformed_shared]);
  assert_norm (not (FStar.List.Tot.mem large_shared
    (common_boundaries 6 malformed_shared (neg large_shared))))

let test_shared_boundary_native_evaluation (fallback:Ast.interpretation bool)
    (rho:Ast.env bool)
  : Lemma
      (Ast.eval (boolean_interpretation fallback) shared_lhs rho ==
       Ast.eval (boolean_interpretation fallback) shared_rhs rho)
= assert_norm (bounded_bool_equiv 3 3 shared_lhs shared_rhs);
  lemma_bounded_bool_equiv_boolean_sound 3 3 shared_lhs shared_rhs fallback rho
