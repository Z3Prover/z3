module Z3IndependentArrayReplay

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module D = Z3ExprScope
module TR = Z3TypedRoot
module AR = Z3IndependentArrayRoot
module AI = Z3IndependentArrayInterpretation
module Syntax = Z3ArraySyntax
module R = Z3ClauseSyntax
module Root = Z3SortedRootDocument
module A = Z3SortedArray
module AF = Z3IndependentArrayFamily
module SR = Z3SortedRoot

let max_nodes : nat = 65536
let search_fuel : nat = 4

let rec supported (sigma:V.signature) (e:expr) : Tot bool (decreases e) =
  (match get_sort e with
   | ArraySort [index] element -> AR.supports sigma index element
   | _ -> true) &&
  (match e with
   | App _ args -> supported_args sigma args
   | Quantifier _ _ _ body -> supported sigma body
   | _ -> true)

and supported_args (sigma:V.signature) (es:list expr) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: rest -> supported sigma e && supported_args sigma rest

let clause (sigma:V.signature) (e:expr) : Tot bool =
  if None? (expression_budget max_nodes e) then false
  else D.scoped [] e && get_sort e = bool_sort && supported sigma e && Syntax.array_lemma e

let rewrite (sigma:V.signature) (a b:expr) : Tot bool =
  if None? (arguments_budget max_nodes [a; b]) then false
  else D.scoped [] a && D.scoped [] b && get_sort a = get_sort b &&
       supported sigma a && supported sigma b && Syntax.equivalent search_fuel a b

val lemma_clause_model (u:TR.uninterpreted) (sch:S.checked_schema)
  (model:TR.interp u sch) (e:expr)
  : Lemma (requires TR.root_model u sch model /\
                    A.model sch (TR.booleans u) (SR.root_scalars u) model
                      (AF.family u (S.signature sch)) /\
                    clause (S.signature sch) e)
          (ensures Root.root_holds u sch model e)

val lemma_clause (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch) (e:expr)
  : Lemma (requires clause (S.signature sch) e)
          (ensures Root.root_holds u sch (TR.standard u sch (AI.symbols u sch uf)) e)

val lemma_rewrite_model (u:TR.uninterpreted) (sch:S.checked_schema)
  (model:TR.interp u sch) (a b:expr)
  : Lemma (requires TR.root_model u sch model /\
                    A.model sch (TR.booleans u) (SR.root_scalars u) model
                      (AF.family u (S.signature sch)) /\
                    rewrite (S.signature sch) a b)
          (ensures Root.root_holds u sch model (R.mk_eq_expr a b))

val lemma_rewrite (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch) (a b:expr)
  : Lemma (requires rewrite (S.signature sch) a b)
          (ensures Root.root_holds u sch (TR.standard u sch (AI.symbols u sch uf))
                    (R.mk_eq_expr a b))
