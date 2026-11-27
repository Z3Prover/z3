module Z3IndependentArrayReplayTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module TR = Z3TypedRoot
module A = Z3SortedArray
module R = Z3ClauseSyntax
module AI = Z3IndependentArrayInterpretation
module Replay = Z3IndependentArrayReplay
module Root = Z3SortedRootDocument

let int_s = TR.int_s
let arr_s = ArraySort [int_s] int_s
let schema : S.checked_schema = { S.sorts = []; S.cases = [] }
let constant (name:string) (s:sort) : expr =
  App { decl_name = name; domain = []; range = s; interp = None; int_params = [] } []
let a = constant "a" arr_s
let b = constant "b" arr_s
let i = constant "i" int_s
let j = constant "j" int_s
let v = constant "v" int_s
let store = App (A.store_decl int_s int_s) [a; i; v]
let read_same = App (A.select_decl int_s int_s) [store; i]
let read_other = App (A.select_decl int_s int_s) [store; j]
let original_read = App (A.select_decl int_s int_s) [a; j]
let same_clause = R.mk_eq_expr read_same v
let other_clause =
  let p = R.mk_eq_expr i j in
  let q = R.mk_eq_expr read_other original_read in
  App (R.or_decl [p; q]) [p; q]
let ext_index = App (A.ext_decl int_s int_s) [a; b]
let other_ext_clause =
  let p = R.mk_eq_expr i ext_index in
  let q = R.mk_eq_expr
    (App (A.select_decl int_s int_s) [store; ext_index])
    (App (A.select_decl int_s int_s) [a; ext_index]) in
  App (R.or_decl [p; q]) [p; q]
let ext_clause =
  let p = R.mk_eq_expr a b in
  let q = R.mk_not_expr (R.mk_eq_expr
    (App (A.select_decl int_s int_s) [a; ext_index])
    (App (A.select_decl int_s int_s) [b; ext_index])) in
  App (R.or_decl [p; q]) [p; q]
let malformed_read = App { A.select_decl int_s int_s with int_params = [1] } [store; i]
let data_s = BaseSort "data"
let ctor : func_decl =
  { decl_name = "ctor"; domain = []; range = data_s; interp = None; int_params = [] }
let data_arr = constant "data-array" (ArraySort [data_s] int_s)
let data_i = constant "data-index" data_s
let unsupported =
  let stored = App (A.store_decl data_s int_s) [data_arr; data_i; v] in
  R.mk_eq_expr (App (A.select_decl data_s int_s) [stored; data_i]) v

let replay_controls ()
  : Lemma (
    Replay.clause [] same_clause /\ Replay.clause [] (R.mk_eq_expr v read_same) /\
    Replay.clause [] other_clause /\ Replay.clause [] other_ext_clause /\ Replay.clause [] ext_clause /\
    Replay.rewrite [] read_same v /\
    not (Replay.clause [] (R.mk_eq_expr malformed_read v)) /\
    not (Replay.clause [ctor] unsupported) /\
    not (Replay.clause [] (R.mk_eq_expr (Var 0 int_s) i)) /\
    not (Replay.rewrite [] read_other v) /\
    not (Replay.rewrite [] (Var 0 int_s) (Var 0 int_s))) =
  assert_norm (Replay.clause [] same_clause);
  assert_norm (Replay.clause [] (R.mk_eq_expr v read_same));
  assert_norm (Replay.clause [] other_clause);
  assert_norm (Replay.clause [] other_ext_clause);
  assert_norm (Replay.clause [] ext_clause);
  assert_norm (Replay.rewrite [] read_same v);
  assert_norm (not (Replay.clause [] (R.mk_eq_expr malformed_read v)));
  assert_norm (not (Replay.clause [ctor] unsupported));
  assert_norm (not (Replay.clause [] (R.mk_eq_expr (Var 0 int_s) i)));
  assert_norm (not (Replay.rewrite [] read_other v));
  assert_norm (not (Replay.rewrite [] (Var 0 int_s) (Var 0 int_s)))

let sound_controls (u:TR.uninterpreted) (uf:TR.symbols u schema)
  : Lemma (
    let root = TR.standard u schema (AI.symbols u schema uf) in
    Root.root_holds u schema root same_clause /\
    Root.root_holds u schema root other_clause /\
    Root.root_holds u schema root other_ext_clause /\
    Root.root_holds u schema root ext_clause /\
    Root.root_holds u schema root (R.mk_eq_expr read_same v)) =
  replay_controls ();
  Replay.lemma_clause u schema uf same_clause;
  Replay.lemma_clause u schema uf other_clause;
  Replay.lemma_clause u schema uf other_ext_clause;
  Replay.lemma_clause u schema uf ext_clause;
  Replay.lemma_rewrite u schema uf read_same v
