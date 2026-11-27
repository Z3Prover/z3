module Z3BooleanSyntaxTests

open Z3AstTheory
open Z3OperatorTags
module B = Z3BoundedBoolEquiv
module S = Z3BooleanSyntax
module R = Z3ClauseSyntax
module D = Z3DistinctAst

let p = Var 0 bool_sort
let q = Var 1 bool_sort
let integer = Var 0 (SortApp IntSymbol [])
let conjunction (es:list expr) = App (R.and_decl es) es
let hidden =
  App { decl_name = "hidden"; domain = [bool_sort]; range = bool_sort;
        interp = None; int_params = [] } [R.mk_not_expr q]
let tree = conjunction [R.true_expr; R.mk_not_expr p; hidden]
let malformed_and =
  { decl_name = "and"; domain = [bool_sort]; range = bool_sort;
    interp = Some op_and; int_params = [1] }

let canonical_shapes_and_opaque_mutations ()
  : Lemma (S.native_bool_op (R.and_decl []) [] == B.BNary B.And /\
           S.native_bool_op (R.or_decl []) [] == B.BNary B.Or /\
           S.native_bool_op malformed_and [p] == B.Opaque /\
           S.native_bool_op (R.and_decl [p; q]) [p] == B.Opaque /\
           S.native_bool_op (R.and_decl [integer]) [integer] == B.Opaque)
  = assert_norm (S.native_bool_op (R.and_decl []) [] == B.BNary B.And /\
                 S.native_bool_op (R.or_decl []) [] == B.BNary B.Or /\
                 S.native_bool_op malformed_and [p] == B.Opaque /\
                 S.native_bool_op (R.and_decl [p; q]) [p] == B.Opaque /\
                 S.native_bool_op (R.and_decl [integer]) [integer] == B.Opaque)

let bounded_traversal_preserves_order_and_opaque_leaves ()
  : Lemma (S.boolean_nodes 0 tree == [tree] /\
           S.boolean_nodes 1 tree == [tree; R.mk_not_expr p; hidden] /\
           S.boolean_nodes_args 2 [tree; R.false_expr] ==
             [tree; R.mk_not_expr p; p; hidden] /\
           S.boolean_nodes 1 (conjunction [p; p]) == [conjunction [p; p]; p; p])
  = assert_norm (S.boolean_nodes 0 tree == [tree] /\
                 S.boolean_nodes 1 tree == [tree; R.mk_not_expr p; hidden] /\
                 S.boolean_nodes_args 2 [tree; R.false_expr] ==
                   [tree; R.mk_not_expr p; p; hidden] /\
                 S.boolean_nodes 1 (conjunction [p; p]) == [conjunction [p; p]; p; p])

let distinct_expansion_arity_and_pair_order ()
  : Lemma (D.expanded [] == R.true_expr /\
           D.expanded [p] == R.true_expr /\
           D.expanded [p; q] == R.mk_not_expr (R.mk_eq_expr p q) /\
           D.expanded [p; q; p] ==
             conjunction [R.mk_not_expr (R.mk_eq_expr p q);
                          R.mk_not_expr (R.mk_eq_expr p p);
                          R.mk_not_expr (R.mk_eq_expr q p)] /\
           D.duplicate_rewrite (D.mk_distinct_expr bool_sort [p; q; p]) R.false_expr)
  = assert_norm (D.expanded [] == R.true_expr /\
                 D.expanded [p] == R.true_expr /\
                 D.expanded [p; q] == R.mk_not_expr (R.mk_eq_expr p q) /\
                 D.expanded [p; q; p] ==
                   conjunction [R.mk_not_expr (R.mk_eq_expr p q);
                                R.mk_not_expr (R.mk_eq_expr p p);
                                R.mk_not_expr (R.mk_eq_expr q p)] /\
                 D.duplicate_rewrite (D.mk_distinct_expr bool_sort [p; q; p]) R.false_expr)
