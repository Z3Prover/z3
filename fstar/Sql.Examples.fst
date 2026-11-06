module Sql.Examples

open Sql.Core
open Sql.Laws
module Q = Sql.Query

#set-options "--fuel 2 --ifuel 1 --z3rlimit 10"

(* Column layouts and exact source SQL are recorded in FSTAR_SQL_REPORT.md.
   Each parameterized lemma covers all finite databases, not just fixtures. *)
let income_source (r:row) = sql_eq (column 1 r) (Text "Fundraising")
let income_date (r:row) = sql_eq (column 2 r) (Text "2019-09-14")
let income_filter (r:row) = sql_and (income_source r) (income_date r)
let b297_left (db:database) =
  project (fun r -> [column 0 r]) (select income_filter (db 0))
let b297_right (db:database) =
  project (fun r -> [column 0 r]) (select income_source (select income_date (db 0)))
let e01_bird297 (db:database)
  : Lemma (bag_equal (b297_left db) (b297_right db))
  = assert_norm (income_filter == (fun r -> sql_and (income_source r) (income_date r)));
    lemma_select_fusion income_source income_date (db 0);
    lemma_bag_of_equal (b297_left db) (b297_right db)

let borderless (r:row) = sql_eq (column 1 r) (Text "borderless")
let missing_kingdom (r:row) =
  sql_or (of_bool (is_null (column 2 r))) (of_bool (is_null (column 3 r)))
let id_order = [{ expression = column 0; ascending = true; nulls_first = true }]
let card_ids (rs:relation) = order_by id_order (project (fun r -> [column 0 r]) rs)
let b49_left (db:database) =
  card_ids (select (fun r -> sql_and (borderless r) (missing_kingdom r)) (db 0))
let b49_right (db:database) = card_ids (select borderless (select missing_kingdom (db 0)))
let e02_bird49 (db:database)
  : Lemma (b49_left db == b49_right db /\ bag_equal (b49_left db) (b49_right db))
  = lemma_select_fusion borderless missing_kingdom (db 0);
    lemma_bag_of_equal (b49_left db) (b49_right db)

(* cards = [id; uuid; borderColor], legalities = [uuid; status; format]. *)
let card_join (r:row) = sql_eq (column 1 r) (column 3 r)
let banned_white (r:row) =
  sql_and (sql_eq (column 4 r) (Text "Banned"))
          (sql_eq (column 2 r) (Text "white"))
let distinct_cards = [Count true (column 0)]
let b55_left (db:database) =
  global_aggregate distinct_cards (select banned_white (inner_join card_join (db 0) (db 1)))
let b55_right (db:database) =
  global_aggregate distinct_cards
    (inner_join (fun r -> sql_and (card_join r) (banned_white r)) (db 0) (db 1))
let e03_bird55 (db:database)
  : Lemma (bag_equal (b55_left db) (b55_right db))
  = lemma_join_filter banned_white card_join (db 0) (db 1);
    lemma_bag_of_equal (b55_left db) (b55_right db)

let e04_spider_count_one (db:database)
  : Lemma (bag_equal (global_aggregate [CountStar] (db 0))
                    (global_aggregate [Count false (fun _ -> num 1)] (db 0)))
  = lemma_count_one (db 0);
    lemma_bag_of_equal (global_aggregate [CountStar] (db 0))
                      (global_aggregate [Count false (fun _ -> num 1)] (db 0))

let stadium_between (r:row) = sql_between (column 2 r) (num 5000) (num 10000)
let stadium_bounds (r:row) =
  sql_and (sql_le (num 5000) (column 2 r)) (sql_le (column 2 r) (num 10000))
let e05_spider_between (db:database)
  : Lemma (project (fun r -> [column 0 r; column 1 r]) (select stadium_between (db 0)) ==
           project (fun r -> [column 0 r; column 1 r]) (select stadium_bounds (db 0)))
  = assert_norm (stadium_between == stadium_bounds)

let e06_nullable_count (db:database)
  : Lemma (bag_equal
      (global_aggregate [Count false (column 2)] (db 0))
      (global_aggregate [CountStar]
        (select (fun r -> of_bool (not (is_null (column 2 r)))) (db 0))))
  = lemma_count_nullable (column 2) (db 0);
    lemma_bag_of_equal
      (global_aggregate [Count false (column 2)] (db 0))
      (global_aggregate [CountStar]
        (select (fun r -> of_bool (not (is_null (column 2 r)))) (db 0)))

let e07_count_case (p:predicate) (db:database)
  : Lemma (bag_equal
      (global_aggregate [Count false (fun r -> sql_case (p r) (num 1) Null)] (db 0))
      (global_aggregate [CountStar] (select p (db 0))))
  = lemma_count_case p (db 0);
    lemma_bag_of_equal
      (global_aggregate [Count false (fun r -> sql_case (p r) (num 1) Null)] (db 0))
      (global_aggregate [CountStar] (select p (db 0)))

let e08_union_all_filter (p:predicate) (db:database)
  : Lemma (bag_equal (select p (append (db 0) (db 1)))
                    (append (select p (db 0)) (select p (db 1))))
  = lemma_select_append p (db 0) (db 1);
    lemma_bag_of_equal (select p (append (db 0) (db 1)))
                      (append (select p (db 0)) (select p (db 1)))

let e09_union_all_commute (db:database)
  : Lemma (bag_equal (append (db 0) (db 1)) (append (db 1) (db 0)))
  = lemma_union_all_commute (db 0) (db 1)

let e10_projection_pushdown (p:predicate) (f:row -> Tot row) (db:database)
  : Lemma (bag_equal (select p (project f (db 0)))
                    (project f (select (fun r -> p (f r)) (db 0))))
  = lemma_select_project p f (db 0);
    lemma_bag_of_equal (select p (project f (db 0)))
                      (project f (select (fun r -> p (f r)) (db 0)))

(* Every negative result includes two evaluated outputs and a row whose
   multiplicity differs, which refutes bag equality on this database. *)
let lemma_separates (w:row) (a b:relation)
  : Lemma (requires multiplicity w a <> multiplicity w b)
          (ensures ~(bag_equal a b)) = ()

let sample_db (a b:relation) : database =
  fun table -> if table = 0 then a else if table = 1 then b else []

(* BIRD 9: numeric CAST(CDSCode) is represented by a numeric code.
   schools = [CDSCode; NCESSchool], frpm = [CDSCode; enrollment]. *)
let eligible_code (v:value) =
  in_values v [num 1751010130583; num 1612910137588; num 1611760134270]
let b9_population (db:database) =
  select (fun r -> eligible_code (column 0 r)) (db 1)
let b9_joined (db:database) =
  select (fun r -> eligible_code (column 2 r))
    (inner_join (fun r -> sql_eq (column 0 r) (column 2 r)) (db 0) (db 1))
let b9_left (db:database) =
  let maximum = eval_aggregate (Max (column 1)) (b9_population db) in
  project (fun r -> [column 1 r])
    (select (fun r -> sql_eq (column 3 r) maximum) (b9_joined db))
let b9_right (db:database) =
  project (fun r -> [column 1 r])
    (take 1 (order_by [{ expression = column 3; ascending = false; nulls_first = false };
                       { expression = column 0; ascending = false; nulls_first = false }]
                     (b9_joined db)))
let b9_db = sample_db
  [[num 1751010130583; Text "00001"]; [num 1612910137588; Text "00002"]]
  [[num 1751010130583; num 100]; [num 1612910137588; num 100]]
let n01_bird9 ()
  : Lemma (b9_left b9_db == [[Text "00001"]; [Text "00002"]] /\
           b9_right b9_db == [[Text "00001"]] /\
           ~(bag_equal (b9_left b9_db) (b9_right b9_db)) /\
           ~(equivalent b9_left b9_right))
  = assert_norm (b9_left b9_db == [[Text "00001"]; [Text "00002"]] /\
                 b9_right b9_db == [[Text "00001"]]);
    assert_norm (multiplicity [Text "00002"] (b9_left b9_db) <>
                 multiplicity [Text "00002"] (b9_right b9_db));
    lemma_separates [Text "00002"] (b9_left b9_db) (b9_right b9_db);
    lemma_not_equivalent b9_left b9_right b9_db [Text "00002"]

let b55_db = sample_db [[num 1; Text "u"; Text "white"]]
  [[Text "u"; Text "Banned"; Text "modern"]; [Text "u"; Text "Banned"; Text "legacy"]]
let b55_without_distinct (db:database) =
  global_aggregate [Count false (column 0)]
    (select banned_white (inner_join card_join (db 0) (db 1)))
let n02_bird55 ()
  : Lemma (b55_left b55_db == [[num 1]] /\
           b55_without_distinct b55_db == [[num 2]] /\
           ~(bag_equal (b55_left b55_db) (b55_without_distinct b55_db)) /\
           ~(equivalent b55_left b55_without_distinct))
  = assert_norm (b55_left b55_db == [[num 1]] /\
                 b55_without_distinct b55_db == [[num 2]]);
    assert_norm (multiplicity [num 1] (b55_left b55_db) <>
                 multiplicity [num 1] (b55_without_distinct b55_db));
    lemma_separates [num 1] (b55_left b55_db) (b55_without_distinct b55_db);
    lemma_not_equivalent b55_left b55_without_distinct b55_db [num 1]

(* superhero = [id; alignment_id], alignment = [id; alignment]. *)
let alignment_on (r:row) = sql_eq (column 1 r) (column 2 r)
let neither (r:row) =
  sql_or (of_bool (is_null (column 3 r)))
    (sql_not (in_values (column 3 r) [Text "Good"; Text "Bad"]))
let b346_left (db:database) =
  global_aggregate [CountStar] (select neither (left_join 2 alignment_on (db 0) (db 1)))
let b346_inner (db:database) =
  global_aggregate [CountStar] (select neither (inner_join alignment_on (db 0) (db 1)))
let b346_db = sample_db [[num 1; Null]] []
let n03_bird346 ()
  : Lemma (b346_left b346_db == [[num 1]] /\ b346_inner b346_db == [[num 0]] /\
           ~(bag_equal (b346_left b346_db) (b346_inner b346_db)) /\
           ~(equivalent b346_left b346_inner))
  = assert_norm (b346_left b346_db == [[num 1]] /\ b346_inner b346_db == [[num 0]]);
    assert_norm (multiplicity [num 1] (b346_left b346_db) <>
                 multiplicity [num 1] (b346_inner b346_db));
    lemma_separates [num 1] (b346_left b346_db) (b346_inner b346_db);
    lemma_not_equivalent b346_left b346_inner b346_db [num 1]

let singer_null = [[Text "Ada"; Text "France"; Null]]
let count_star = global_aggregate [CountStar] singer_null
let count_age = global_aggregate [Count false (column 2)] singer_null
let n04_spider_count_age ()
  : Lemma (count_star == [[num 1]] /\ count_age == [[num 0]] /\
           ~(bag_equal count_star count_age))
  = assert_norm (count_star == [[num 1]] /\ count_age == [[num 0]]);
    assert_norm (multiplicity [num 1] count_star <> multiplicity [num 1] count_age);
    lemma_separates [num 1] count_star count_age

let stadiums = [[num 1; Text "A"]]
let concerts = [[Null]]
let not_in_stadiums =
  project (fun r -> [column 1 r])
    (select (fun r -> sql_not (in_values (column 0 r) (values (column 0) concerts))) stadiums)
let not_exists_stadiums =
  project (fun r -> [column 1 r])
    (select (fun r -> sql_not (exists_rows
      (select (fun c -> sql_eq (column 0 r) (column 0 c)) concerts))) stadiums)
let n05_spider_not_in ()
  : Lemma (not_in_stadiums == [] /\ not_exists_stadiums == [[Text "A"]] /\
           ~(bag_equal not_in_stadiums not_exists_stadiums))
  = assert_norm (not_in_stadiums == [] /\ not_exists_stadiums == [[Text "A"]]);
    assert_norm (multiplicity [Text "A"] not_in_stadiums <>
                 multiplicity [Text "A"] not_exists_stadiums);
    lemma_separates [Text "A"] not_in_stadiums not_exists_stadiums

let adult_singers =
  [[Text "Ada"; Text "France"; num 21]; [Text "Bea"; Text "France"; num 22]]
let countries =
  project (fun r -> [column 1 r])
    (select (fun r -> sql_lt (num 20) (column 2 r)) adult_singers)
let n06_spider_distinct ()
  : Lemma (countries == [[Text "France"]; [Text "France"]] /\
           distinct countries == [[Text "France"]] /\
           ~(bag_equal countries (distinct countries)))
  = assert_norm (countries == [[Text "France"]; [Text "France"]] /\
                 distinct countries == [[Text "France"]]);
    assert_norm (multiplicity [Text "France"] countries <>
                 multiplicity [Text "France"] (distinct countries));
    lemma_separates [Text "France"] countries (distinct countries)

let empty_sum = global_aggregate [Sum false (column 0)] []
let empty_zero = [[coalesce (eval_aggregate (Sum false (column 0)) []) (num 0)]]
let n07_sum_empty ()
  : Lemma (empty_sum == [[Null]] /\ empty_zero == [[num 0]] /\
           ~(bag_equal empty_sum empty_zero))
  = assert_norm (empty_sum == [[Null]] /\ empty_zero == [[num 0]]);
    assert_norm (multiplicity [Null] empty_sum <> multiplicity [Null] empty_zero);
    lemma_separates [Null] empty_sum empty_zero

let nullable_numbers = [[num 2]; [Null]]
let actual_average = global_aggregate [Avg false (column 0)] nullable_numbers
let wrong_average =
  [[sql_div (eval_aggregate (Sum false (column 0)) nullable_numbers)
            (eval_aggregate CountStar nullable_numbers)]]
let n08_average_null ()
  : Lemma (actual_average == [[Number 2 1]] /\ wrong_average == [[Number 2 2]] /\
           ~(bag_equal actual_average wrong_average))
  = assert_norm (actual_average == [[Number 2 1]] /\ wrong_average == [[Number 2 2]]);
    assert_norm (multiplicity [num 2] actual_average <> multiplicity [num 2] wrong_average);
    lemma_separates [num 2] actual_average wrong_average

let unequal_groups = [[num 0; num 2]; [num 0; num 4]; [num 1; num 12]]
let overall_average = global_aggregate [Avg false (column 1)] unequal_groups
let average_of_averages =
  global_aggregate [Avg false (column 1)]
    (grouped [column 0] [Avg false (column 1)] unequal_groups)
let n09_average_of_averages ()
  : Lemma (same_row [num 6] (aggregates [Avg false (column 1)] unequal_groups) /\
           ~(bag_equal overall_average average_of_averages))
  = assert_norm (same_row [num 6] (aggregates [Avg false (column 1)] unequal_groups));
    assert_norm (multiplicity [num 6] overall_average <>
                 multiplicity [num 6] average_of_averages);
    lemma_separates [num 6] overall_average average_of_averages

let union_bag = append [[num 1]] [[num 1]]
let union_set = union [[num 1]] [[num 1]]
let n10_union ()
  : Lemma (~(bag_equal union_bag union_set))
  = assert_norm (multiplicity [num 1] union_bag <> multiplicity [num 1] union_set);
    lemma_separates [num 1] union_bag union_set

let outer_on (r:row) = sql_eq (column 0 r) (column 1 r)
let right_positive (r:row) = sql_lt (num 0) (column 2 r)
let outer_where = select right_positive (left_join 2 outer_on [[num 1]] [])
let outer_pushed =
  left_join 2 (fun r -> sql_and (outer_on r) (right_positive r)) [[num 1]] []
let n11_outer_predicate ()
  : Lemma (outer_where == [] /\ outer_pushed == [[num 1; Null; Null]] /\
           ~(bag_equal outer_where outer_pushed))
  = assert_norm (outer_where == [] /\ outer_pushed == [[num 1; Null; Null]]);
    assert_norm (multiplicity [num 1; Null; Null] outer_where <>
                 multiplicity [num 1; Null; Null] outer_pushed);
    lemma_separates [num 1; Null; Null] outer_where outer_pushed

let limited_descending =
  take 1 (order_by [{ expression = column 0; ascending = false; nulls_first = false }]
                  [[num 2]; [num 1]])
let limited_ordered = take 1 (order_by id_order [[num 2]; [num 1]])
let n12_order_limit ()
  : Lemma (limited_descending == [[num 2]] /\ limited_ordered == [[num 1]] /\
           ~(bag_equal limited_descending limited_ordered))
  = assert_norm (limited_descending == [[num 2]] /\ limited_ordered == [[num 1]]);
    assert_norm (multiplicity [num 1] limited_descending <>
                 multiplicity [num 1] limited_ordered);
    lemma_separates [num 1] limited_descending limited_ordered
