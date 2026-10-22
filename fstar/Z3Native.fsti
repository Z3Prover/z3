(* Foreign handles remain owned by the official Z3 OCaml binding. No
   foreign operation constructs checker expressions or checked facts. *)
module Z3Native
open FStar.All

new val ast : Type0
new val native_sort : Type0

type operator =
  | Not | And | Or | Implies | Eq | Oeq | True | False | Ite | Xor | Distinct
  | Select | Store | ArrayExt | ConstArray | Bvand | Bvor | Bvxor | Bvnot
  | Bvadd | Bvmul | Bvsub | Bvneg | Bvudiv | Bvurem | Bvextract | Bvconcat | Bvmkbv
  | Bvult | Bvule | Bvuge | Concat
  | DatatypeConstructor | DatatypeRecognizer | DatatypeAccessor
  | Add | Mul | Sub | Div | IDiv | Mod | Le | Lt | Ge | Gt | ToReal
  | Rational | BvNumeral
  | Opaque

noeq
type sort_view =
  | Base : name:string -> sort_view
  | Array : domains:list native_sort -> range:native_sort -> sort_view

noeq
type declaration = {
  id: nat;
  name: string;
  unique_name: string;
  op: operator;
  range: native_sort;
  numeral: option (int & int);
  native_kind: int;
  parameters: list int;
}

noeq
type expression_view =
  | Variable : index:nat -> sort:native_sort -> expression_view
  | Application : decl:declaration -> args:list ast -> expression_view
  | Quantified : kind:Z3AstTheory.quantifier_kind -> sorts:list native_sort -> body:ast -> expression_view

noeq
type parameter_view =
  | ParameterRational : int -> int -> parameter_view
  | ParameterExpression : ast -> parameter_view
  | ParameterUnsupported : parameter_view

noeq
type proof_view = {
  proof_name: string;
  premises: list ast;
  conclusion: ast;
  farkas: option (list (int & int));
  assumed: option string;
  lp_data: option (string & list parameter_view);
  binding: option (list native_sort & ast);
  instantiations: list ast;
}

type clause_action =
  | InputClause
  | LearnedClause
  | TheoryClause
  | DeleteClause

noeq
type clause_view = {
  action: clause_action;
  formula: ast;
  literals: list ast;
  certificate: option ast;
}

noeq
type solve_result =
  | Unsat : assertions:list ast -> proof:ast -> solve_result
  | Sat
  | Unknown : reason:string -> solve_result

val ast_id : ast -> ML nat
val sort_id : native_sort -> ML nat
val view_sort : native_sort -> ML sort_view
val view_expression : ast -> ML expression_view
val view_datatypes : roots:list native_sort -> ML Z3DatatypeSignature.schema
val view_proof : ast -> ML proof_view
val view_clause_trail : ast -> ML (option (list clause_view & ast))
val solve : smtlib:string -> timeout_ms:nat -> ML solve_result
val solve_with_clause_proofs : smtlib:string -> timeout_ms:nat -> clause_proofs:bool -> ML solve_result
val fail : #a:Type -> message:string -> ML a
