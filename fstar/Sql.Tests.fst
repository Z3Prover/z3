module Sql.Tests

open Sql.Core
module Q = Sql.Query

#set-options "--fuel 2 --ifuel 1 --z3rlimit 10"

let db : database = fun t ->
  if t = 0 then [[num 1]; [num 2]; [Null]]
  else [[num 2]; [num 2]]

let lemma_null_logic ()
  : Lemma (sql_eq Null Null == Unknown /\
           sql_not Unknown == Unknown /\
           sql_or Unknown Yes == Yes /\
           sql_and Unknown No == No /\
           in_values Null [] == No /\
           in_values (num 1) [Null; num 1] == Yes /\
           in_values (num 1) [Null; num 2] == Unknown /\
           same_value Null Null /\ same_value (Number 1 2) (Number 2 4))
  = assert_norm (sql_eq Null Null == Unknown /\
                 sql_not Unknown == Unknown /\
                 sql_or Unknown Yes == Yes /\
                 sql_and Unknown No == No /\
                 in_values Null [] == No /\
                 in_values (num 1) [Null; num 1] == Yes /\
                 in_values (num 1) [Null; num 2] == Unknown /\
                 same_value Null Null /\ same_value (Number 1 2) (Number 2 4))

let lemma_aggregate_edges ()
  : Lemma (aggregates [CountStar; Count false (column 0); Sum false (column 0);
                       Avg false (column 0); Min (column 0); Max (column 0)] [] ==
             [num 0; num 0; Null; Null; Null; Null] /\
           aggregates [Sum false (column 0); Avg false (column 0)] [[Null]] == [Null; Null] /\
           same_row (aggregates [Avg false (column 0)] [[num 1]; [num 2]]) [Number 3 2] /\
           aggregates [Count true (column 0)] [[Null]; [num 1]; [Number 2 2]] == [num 1])
  = assert_norm (aggregates [CountStar; Count false (column 0); Sum false (column 0);
                             Avg false (column 0); Min (column 0); Max (column 0)] [] ==
                   [num 0; num 0; Null; Null; Null; Null] /\
                 aggregates [Sum false (column 0); Avg false (column 0)] [[Null]] == [Null; Null] /\
                 same_row (aggregates [Avg false (column 0)] [[num 1]; [num 2]]) [Number 3 2] /\
                 aggregates [Count true (column 0)] [[Null]; [num 1]; [Number 2 2]] == [num 1])

let groups = grouped [column 0] [CountStar] [[Null]; [num 1]; [Null]]
let having = select (fun r -> sql_lt (num 1) (column 1 r)) groups
let lemma_group_having ()
  : Lemma (groups == [[num 1; num 1]; [Null; num 2]] /\
           having == [[Null; num 2]] /\
           grouped [column 0] [CountStar] [] == [] /\
           global_aggregate [CountStar] [] == [[num 0]])
  = assert_norm (groups == [[num 1; num 1]; [Null; num 2]] /\
                 having == [[Null; num 2]] /\
                 grouped [column 0] [CountStar] [] == [] /\
                 global_aggregate [CountStar] [] == [[num 0]])

let correlated =
  Q.Select [Q.col 0]
    (Q.Where (Q.exists_query
       (Q.Where (Q.equal (Q.col 0) (Q.outer_col 0)) (Q.Table 1))) (Q.Table 0))
let in_subquery = Q.Where (Q.in_query (Q.col 0) (Q.Table 1)) (Q.Table 0)
let lemma_subqueries ()
  : Lemma (Q.eval db [] correlated == [[num 2]] /\
           Q.eval db [] in_subquery == [[num 2]] /\
           scalar_subquery [] == Some Null /\
           scalar_subquery [[num 1]] == Some (num 1) /\
           scalar_subquery [[num 1]; [num 2]] == None)
  = assert_norm (Q.eval db [] correlated == [[num 2]] /\
                 Q.eval db [] in_subquery == [[num 2]] /\
                 scalar_subquery [] == Some Null /\
                 scalar_subquery [[num 1]] == Some (num 1) /\
                 scalar_subquery [[num 1]; [num 2]] == None)

let lemma_set_and_slice ()
  : Lemma (except_all [[num 1]; [num 1]; [Null]] [[num 1]] == [[num 1]; [Null]] /\
           intersect_all [[num 1]; [num 1]; [Null]] [[num 1]; [Null]] == [[num 1]; [Null]] /\
           intersect [[Null]; [Null]; [num 2]] [[Null]] == [[Null]] /\
           except [[Null]; [num 2]] [[Null]] == [[num 2]] /\
           take 1 (drop 1 [[num 1]; [num 2]; [num 3]]) == [[num 2]])
  = assert_norm (except_all [[num 1]; [num 1]; [Null]] [[num 1]] == [[num 1]; [Null]] /\
                 intersect_all [[num 1]; [num 1]; [Null]] [[num 1]; [Null]] == [[num 1]; [Null]] /\
                 intersect [[Null]; [Null]; [num 2]] [[Null]] == [[Null]] /\
                 except [[Null]; [num 2]] [[Null]] == [[num 2]] /\
                 take 1 (drop 1 [[num 1]; [num 2]; [num 3]]) == [[num 2]])

let lemma_like_and_arithmetic ()
  : Lemma (like_chars [LiteralChar 'a'; AnyString; LiteralChar 'z'] ['a'; 'b'; 'z'] /\
           like_chars [AnyString; AnyString] [] /\
           not (like_chars [AnyChar] []) /\
           like_chars [LiteralChar '%'] ['%'] /\
           sql_like Null [AnyString] == Unknown /\
           same_value (sql_add (Number 1 2) (Number 1 3)) (Number 5 6) /\
           same_value (sql_div (num 3) (num (-2))) (Number (-3) 2) /\
           sql_div (num 1) (num 0) == Null /\
           sql_case Unknown (num 1) (num 2) == num 2)
  = assert_norm (like_chars [LiteralChar 'a'; AnyString; LiteralChar 'z'] ['a'; 'b'; 'z'] /\
                 like_chars [AnyString; AnyString] [] /\
                 not (like_chars [AnyChar] []) /\
                 like_chars [LiteralChar '%'] ['%'] /\
                 sql_like Null [AnyString] == Unknown /\
                 same_value (sql_add (Number 1 2) (Number 1 3)) (Number 5 6) /\
                 same_value (sql_div (num 3) (num (-2))) (Number (-3) 2) /\
                 sql_div (num 1) (num 0) == Null /\
                 sql_case Unknown (num 1) (num 2) == num 2)
