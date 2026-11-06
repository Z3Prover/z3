module Sql.Laws

open Sql.Core
module Q = Sql.Query

#set-options "--fuel 2 --ifuel 1 --z3rlimit 10"

let lemma_bag_of_equal (a b:relation)
  : Lemma (requires a == b) (ensures bag_equal a b) = ()

let lemma_not_equivalent (a b:database -> Tot relation) (db:database) (w:row)
  : Lemma (requires multiplicity w (a db) <> multiplicity w (b db))
          (ensures ~(equivalent a b)) = ()

let lemma_and_passes (a b:truth)
  : Lemma (passes (sql_and a b) == (passes a && passes b))
  = match a, b with
    | Yes, Yes | Yes, No | Yes, Unknown
    | No, Yes | No, No | No, Unknown
    | Unknown, Yes | Unknown, No | Unknown, Unknown -> ()

let lemma_de_morgan (a b:truth)
  : Lemma (sql_not (sql_and a b) == sql_or (sql_not a) (sql_not b))
  = match a, b with
    | Yes, Yes | Yes, No | Yes, Unknown
    | No, Yes | No, No | No, Unknown
    | Unknown, Yes | Unknown, No | Unknown, Unknown -> ()

let rec lemma_select_fusion (p q:predicate) (rs:relation)
  : Lemma (select p (select q rs) ==
           select (fun r -> sql_and (p r) (q r)) rs)
  = match rs with
    | [] -> ()
    | r::rest -> lemma_and_passes (p r) (q r); lemma_select_fusion p q rest

let rec lemma_select_commute (p q:predicate) (rs:relation)
  : Lemma (select p (select q rs) == select q (select p rs))
  = match rs with [] -> () | _::rest -> lemma_select_commute p q rest

let rec lemma_select_idempotent (p:predicate) (rs:relation)
  : Lemma (select p (select p rs) == select p rs)
  = match rs with [] -> () | _::rest -> lemma_select_idempotent p rest

let rec lemma_select_append (p:predicate) (a b:relation)
  : Lemma (select p (append a b) == append (select p a) (select p b))
  = match a with [] -> () | _::rest -> lemma_select_append p rest b

let rec lemma_project_append (f:row -> Tot row) (a b:relation)
  : Lemma (project f (append a b) == append (project f a) (project f b))
  = match a with [] -> () | _::rest -> lemma_project_append f rest b

let rec lemma_project_fusion (f g:row -> Tot row) (rs:relation)
  : Lemma (project f (project g rs) == project (fun r -> f (g r)) rs)
  = match rs with [] -> () | _::rest -> lemma_project_fusion f g rest

let rec lemma_select_project (p:predicate) (f:row -> Tot row) (rs:relation)
  : Lemma (select p (project f rs) ==
           project f (select (fun r -> p (f r)) rs))
  = match rs with [] -> () | _::rest -> lemma_select_project p f rest

let rec lemma_multiplicity_append (r:row) (a b:relation)
  : Lemma (multiplicity r (append a b) == multiplicity r a + multiplicity r b)
  = match a with [] -> () | _::rest -> lemma_multiplicity_append r rest b

let lemma_union_all_commute_at (r:row) (a b:relation)
  : Lemma (multiplicity r (append a b) == multiplicity r (append b a))
  = lemma_multiplicity_append r a b; lemma_multiplicity_append r b a

let lemma_union_all_commute (a b:relation)
  : Lemma (bag_equal (append a b) (append b a))
  = FStar.Classical.forall_intro (fun r -> lemma_union_all_commute_at r a b)

let rec lemma_nonnull_count (e:scalar) (rs:relation)
  : Lemma (FStar.List.Tot.length (nonnull (values e rs)) ==
           FStar.List.Tot.length (select (fun r -> of_bool (not (is_null (e r)))) rs))
  = match rs with [] -> () | _::rest -> lemma_nonnull_count e rest

let lemma_count_nullable (e:scalar) (rs:relation)
  : Lemma (eval_aggregate (Count false e) rs ==
           eval_aggregate CountStar (select (fun r -> of_bool (not (is_null (e r)))) rs))
  = lemma_nonnull_count e rs

let rec lemma_count_constant (rs:relation)
  : Lemma (FStar.List.Tot.length (nonnull (values (fun _ -> num 1) rs)) ==
           FStar.List.Tot.length rs)
  = match rs with [] -> () | _::rest -> lemma_count_constant rest

let lemma_count_one (rs:relation)
  : Lemma (eval_aggregate (Count false (fun _ -> num 1)) rs ==
           eval_aggregate CountStar rs)
  = lemma_count_constant rs

let rec lemma_count_case_length (p:predicate) (rs:relation)
  : Lemma (FStar.List.Tot.length
             (nonnull (values (fun r -> sql_case (p r) (num 1) Null) rs)) ==
           FStar.List.Tot.length (select p rs))
  = match rs with [] -> () | _::rest -> lemma_count_case_length p rest

let lemma_count_case (p:predicate) (rs:relation)
  : Lemma (eval_aggregate (Count false (fun r -> sql_case (p r) (num 1) Null)) rs ==
           eval_aggregate CountStar (select p rs))
  = lemma_count_case_length p rs

let rec lemma_matches_filter (p q:predicate) (r:row) (rs:relation)
  : Lemma (select p (matches q r rs) ==
           matches (fun joined -> sql_and (q joined) (p joined)) r rs)
  = match rs with
    | [] -> ()
    | x::xs -> lemma_and_passes (q (append r x)) (p (append r x));
               lemma_matches_filter p q r xs

let rec lemma_join_filter (p q:predicate) (a b:relation)
  : Lemma (select p (inner_join q a b) ==
           inner_join (fun r -> sql_and (q r) (p r)) a b)
  = match a with
    | [] -> ()
    | r::rest ->
      lemma_select_append p (matches q r b) (inner_join q rest b);
      lemma_matches_filter p q r b;
      lemma_join_filter p q rest b

#push-options "--fuel 4"
let lemma_query_where_fusion (db:database) (outer:row)
                             (p q:Q.condition) (s:Q.query)
  : Lemma (Q.eval db outer (Q.Where p (Q.Where q s)) ==
           Q.eval db outer (Q.Where (Q.conjunction p q) s))
  = assert_norm (Q.eval db outer (Q.Where p (Q.Where q s)) ==
                 select (p db outer) (select (q db outer) (Q.eval db outer s)));
    assert_norm (Q.eval db outer (Q.Where (Q.conjunction p q) s) ==
                 select (fun r -> sql_and (p db outer r) (q db outer r))
                        (Q.eval db outer s));
    lemma_select_fusion (p db outer) (q db outer) (Q.eval db outer s)
#pop-options
