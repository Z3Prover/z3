module Z3SkolemSyntaxTests

open Z3AstTheory
module K = Z3SkolemSyntax
module R = Z3ClauseSyntax

let integer = SortApp IntSymbol []
let witness (name:string) (domain:list sort) : func_decl =
  { decl_name = name; domain = domain; range = integer; interp = None; int_params = [] }
let constant = witness "sk" []
let dependent = witness "sk_dep" [integer]
let other = witness "sk_other" []
let equality (a b:expr) = R.mk_eq_expr a b
let body = equality (Var 0 integer) (Var 1 integer)
let source = Quantifier Exists_k [integer] bool_sort body
let target = equality (App dependent [Var 0 integer]) (Var 0 integer)
let closed_body = equality (Var 0 integer) (Var 0 integer)
let closed_source = Quantifier Exists_k [integer] bool_sort closed_body
let closed_target = equality (App constant []) (App constant [])
let first : K.definition =
  { K.bound_sorts = [integer]; negative = false; body = closed_body;
    dependencies = []; witnesses = [(0, constant)] }
let later : K.definition =
  { K.bound_sorts = [integer]; negative = false;
    body = equality (Var 0 integer) (App constant []);
    dependencies = []; witnesses = [(0, other)] }

let dependent_recognition_and_negative_polarity ()
  : Lemma (
      (match K.definition_of source target with
       | Some d -> d.K.dependencies == [(0, integer)] /\
                   d.K.witnesses == [(0, dependent)] /\
                   K.instantiation d == Some target
       | None -> False) /\
      (match K.definition_of
               (R.mk_not_expr (Quantifier Forall_k [integer] bool_sort body))
               (R.mk_not_expr target) with
       | Some d -> d.K.negative == true /\ K.instantiation d == Some (R.mk_not_expr target)
       | None -> False))
  = assert_norm (
      (match K.definition_of source target with
       | Some d -> d.K.dependencies == [(0, integer)] /\
                   d.K.witnesses == [(0, dependent)] /\
                   K.instantiation d == Some target
       | None -> False) /\
      (match K.definition_of
               (R.mk_not_expr (Quantifier Forall_k [integer] bool_sort body))
               (R.mk_not_expr target) with
       | Some d -> d.K.negative == true /\ K.instantiation d == Some (R.mk_not_expr target)
       | None -> False))

let substitution_respects_binder_depth_and_sort ()
  : Lemma (
      K.substitute 0 1 [(0, integer)] [(0, dependent)]
        (Quantifier Forall_k [integer] bool_sort
          (equality (Var 1 integer) (Var 0 integer))) ==
        Some (Quantifier Forall_k [integer] bool_sort
          (equality (App dependent [Var 1 integer]) (Var 0 integer))) /\
      K.substitute 0 1 [] [(0, constant)] (Var 0 bool_sort) == None /\
      K.substitute 0 1 [] [] (Var 0 integer) == None /\
      K.substitute 0 1 [] [] (Var 2 integer) == Some (Var 1 integer))
  = assert_norm (
      K.substitute 0 1 [(0, integer)] [(0, dependent)]
        (Quantifier Forall_k [integer] bool_sort
          (equality (Var 1 integer) (Var 0 integer))) ==
        Some (Quantifier Forall_k [integer] bool_sort
          (equality (App dependent [Var 1 integer]) (Var 0 integer))) /\
      K.substitute 0 1 [] [(0, constant)] (Var 0 bool_sort) == None /\
      K.substitute 0 1 [] [] (Var 0 integer) == None /\
      K.substitute 0 1 [] [] (Var 2 integer) == Some (Var 1 integer))

let malformed_witnesses_and_vacuous_blocks ()
  : Lemma (
      K.definition_of source (equality (App constant []) (Var 0 integer)) == None /\
      not (K.valid_dependencies [(0, integer); (0, bool_sort)]) /\
      not (K.valid_witnesses [integer] [] [(0, constant); (0, other)]) /\
      K.vacuous (Quantifier Exists_k [integer] bool_sort R.true_expr) R.true_expr /\
      not (K.vacuous closed_source closed_target))
  = assert_norm (
      K.definition_of source (equality (App constant []) (Var 0 integer)) == None /\
      not (K.valid_dependencies [(0, integer); (0, bool_sort)]) /\
      not (K.valid_witnesses [integer] [] [(0, constant); (0, other)]) /\
      K.vacuous (Quantifier Exists_k [integer] bool_sort R.true_expr) R.true_expr /\
      not (K.vacuous closed_source closed_target))

let context_ordering_preserves_dependencies_and_rejects_conflicts ()
  : Lemma (
      K.order_context 2 [first; later] == Some [later; first] /\
      K.add_definition [first] first == Some [first] /\
      K.add_definition [first] { first with K.negative = true } == None /\
      K.fresh_inputs [first] [R.true_expr] /\
      not (K.fresh_inputs [first] [closed_target]))
  = assert_norm (
      K.order_context 2 [first; later] == Some [later; first] /\
      K.add_definition [first] first == Some [first] /\
      K.add_definition [first] { first with K.negative = true } == None /\
      K.fresh_inputs [first] [R.true_expr] /\
      not (K.fresh_inputs [first] [closed_target]))
