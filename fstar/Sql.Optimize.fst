module Sql.Optimize

open Sql.Core
open Sql.Laws
module U = FStar.UInt64
module L = FStar.List.Tot

#set-options "--fuel 2 --ifuel 1 --z3rlimit 10"

type atom = U.t
type mapping =
  | Identity
  | Mapping : atom -> mapping
  | Compose : mapping -> mapping -> mapping
type condition =
  | Always
  | Never
  | Predicate : atom -> condition
  | Both : condition -> condition -> condition
  | Preimage : condition -> mapping -> condition
  | NotNull : atom -> condition
type plan =
  | Base : atom -> plan
  | Empty
  | Filter : condition -> plan -> plan
  | Project : mapping -> plan -> plan
  | UnionAll : plan -> plan -> plan
  | Cross : plan -> plan -> plan
  | Join : condition -> plan -> plan -> plan
  | CountRows : plan -> plan
  | CountOne : plan -> plan
  | CountValue : atom -> plan -> plan
  | CountWhen : condition -> plan -> plan
  | AddCounts : plan -> plan -> plan

noeq type interpretation = {
  tables: atom -> Tot relation;
  predicates: atom -> Tot predicate;
  mappings: atom -> row -> Tot row;
  scalars: atom -> Tot scalar
}

let rec eval_mapping (i:interpretation) (f:mapping) (r:row) : Tot row =
  match f with
  | Identity -> r
  | Mapping a -> i.mappings a r
  | Compose f g -> eval_mapping i f (eval_mapping i g r)
let rec eval_condition (i:interpretation) (p:condition) (r:row) : Tot truth =
  match p with
  | Always -> Yes
  | Never -> No
  | Predicate a -> i.predicates a r
  | Both p q -> sql_and (eval_condition i p r) (eval_condition i q r)
  | Preimage p f -> eval_condition i p (eval_mapping i f r)
  | NotNull a -> of_bool (not (is_null (i.scalars a r)))
let first (rs:relation) : row = match rs with [] -> [] | r::_ -> r
let cross (a b:relation) : relation = inner_join (fun _ -> Yes) a b
let rec denote (i:interpretation) (q:plan) : Tot relation =
  match q with
  | Base a -> i.tables a
  | Empty -> []
  | Filter p a -> select (eval_condition i p) (denote i a)
  | Project f a -> project (eval_mapping i f) (denote i a)
  | UnionAll a b -> append (denote i a) (denote i b)
  | Cross a b -> cross (denote i a) (denote i b)
  | Join p a b -> inner_join (eval_condition i p) (denote i a) (denote i b)
  | CountRows a -> global_aggregate [CountStar] (denote i a)
  | CountOne a -> global_aggregate [Count false (fun _ -> num 1)] (denote i a)
  | CountValue e a -> global_aggregate [Count false (i.scalars e)] (denote i a)
  | CountWhen p a ->
    global_aggregate [Count false (fun r -> sql_case (eval_condition i p r) (num 1) Null)] (denote i a)
  | AddCounts a b ->
    [[sql_add (column 0 (first (denote i a))) (column 0 (first (denote i b)))]]

let rec lemma_append_right (#a:Type) (xs:list a)
  : Lemma (append xs [] == xs)
  = match xs with [] -> () | _::rest -> lemma_append_right rest
let rec lemma_append_assoc (#t:Type) (a b c:list t)
  : Lemma (append (append a b) c == append a (append b c))
  = match a with [] -> () | _::rest -> lemma_append_assoc rest b c
let rec lemma_append_length (#t:Type) (a b:list t)
  : Lemma (L.length (append a b) == L.length a + L.length b)
  = match a with [] -> () | _::rest -> lemma_append_length rest b
let rec lemma_filter_constant (rs:relation)
  : Lemma (select (fun _ -> Yes) rs == rs /\ select (fun _ -> No) rs == [])
  = match rs with [] -> () | _::rest -> lemma_filter_constant rest
let rec lemma_project_identity (rs:relation)
  : Lemma (project (fun r -> r) rs == rs)
  = match rs with [] -> () | _::rest -> lemma_project_identity rest
let rec lemma_matches_never (r:row) (rs:relation)
  : Lemma (matches (fun _ -> No) r rs == [])
  = match rs with [] -> () | _::rest -> lemma_matches_never r rest
let rec lemma_join_never (a b:relation)
  : Lemma (inner_join (fun _ -> No) a b == [])
  = match a with
    | [] -> ()
    | r::rest -> lemma_matches_never r b; lemma_join_never rest b
let rec lemma_join_empty (p:predicate) (rs:relation)
  : Lemma (inner_join p rs [] == [])
  = match rs with [] -> () | _::rest -> lemma_join_empty p rest
let rec lemma_matches_append (p:predicate) (r:row) (a b:relation)
  : Lemma (matches p r (append a b) == append (matches p r a) (matches p r b))
  = match a with [] -> () | _::rest -> lemma_matches_append p r rest b
let rec lemma_join_union_left (p:predicate) (a b c:relation)
  : Lemma (inner_join p (append a b) c == append (inner_join p a c) (inner_join p b c))
  = match a with
    | [] -> ()
    | r::rest ->
      lemma_join_union_left p rest b c;
      lemma_append_assoc (matches p r c) (inner_join p rest c) (inner_join p b c)

(* A total, oriented one-step repertoire: no inverse expansions, predicate
   commutation loops, or bag-only equalities under sequence operators. *)
let rewrite (q:plan) : option plan =
  match q with
  | Filter Always a -> Some a
  | Filter Never _ -> Some Empty
  | Filter _ Empty -> Some Empty
  | Filter p (Filter q a) ->
    if p = q then Some (Filter p a) else Some (Filter (Both p q) a)
  | Filter p (Project f a) -> Some (Project f (Filter (Preimage p f) a))
  | Filter p (UnionAll a b) -> Some (UnionAll (Filter p a) (Filter p b))
  | Filter p (Join q a b) -> Some (Join (Both q p) a b)
  | Project _ Empty -> Some Empty
  | Project Identity a -> Some a
  | Project f (Project g a) -> Some (Project (Compose f g) a)
  | Project f (UnionAll a b) -> Some (UnionAll (Project f a) (Project f b))
  | UnionAll Empty a -> Some a
  | UnionAll a Empty -> Some a
  | UnionAll (UnionAll a b) c -> Some (UnionAll a (UnionAll b c))
  | Cross Empty _ | Cross _ Empty -> Some Empty
  | Cross (UnionAll a b) c -> Some (UnionAll (Cross a c) (Cross b c))
  | Join Never _ _ -> Some Empty
  | Join _ Empty _ | Join _ _ Empty -> Some Empty
  | Join Always a b -> Some (Cross a b)
  | Join p (UnionAll a b) c -> Some (UnionAll (Join p a c) (Join p b c))
  | CountOne a -> Some (CountRows a)
  | CountValue e a -> Some (CountRows (Filter (NotNull e) a))
  | CountWhen p a -> Some (CountRows (Filter p a))
  | CountRows (UnionAll a b) -> Some (AddCounts (CountRows a) (CountRows b))
  | _ -> None

#push-options "--fuel 4"
let lemma_rewrite (i:interpretation) (q:plan)
  : Lemma (match rewrite q with None -> True | Some r -> denote i q == denote i r)
  = assert_norm (eval_condition i Always == (fun _ -> Yes));
    assert_norm (eval_condition i Never == (fun _ -> No));
    assert_norm (eval_mapping i Identity == (fun r -> r));
    match q with
    | Filter Always a -> lemma_filter_constant (denote i a)
    | Filter Never a -> lemma_filter_constant (denote i a)
    | Filter _ Empty -> ()
    | Filter p (Filter q a) ->
      assert_norm (eval_condition i (Both p q) ==
                   (fun r -> sql_and (eval_condition i p r) (eval_condition i q r)));
      if p = q then lemma_select_idempotent (eval_condition i p) (denote i a)
      else lemma_select_fusion (eval_condition i p) (eval_condition i q) (denote i a)
    | Filter p (Project f a) ->
      assert_norm (eval_condition i (Preimage p f) ==
                   (fun r -> eval_condition i p (eval_mapping i f r)));
      lemma_select_project (eval_condition i p) (eval_mapping i f) (denote i a)
    | Filter p (UnionAll a b) -> lemma_select_append (eval_condition i p) (denote i a) (denote i b)
    | Filter p (Join q a b) ->
      assert_norm (eval_condition i (Both q p) ==
                   (fun r -> sql_and (eval_condition i q r) (eval_condition i p r)));
      lemma_join_filter (eval_condition i p) (eval_condition i q) (denote i a) (denote i b)
    | Project _ Empty -> ()
    | Project Identity a -> lemma_project_identity (denote i a)
    | Project f (Project g a) ->
      assert_norm (eval_mapping i (Compose f g) ==
                   (fun r -> eval_mapping i f (eval_mapping i g r)));
      lemma_project_fusion (eval_mapping i f) (eval_mapping i g) (denote i a)
    | Project f (UnionAll a b) -> lemma_project_append (eval_mapping i f) (denote i a) (denote i b)
    | UnionAll Empty _ -> ()
    | UnionAll a Empty -> lemma_append_right (denote i a)
    | UnionAll (UnionAll a b) c -> lemma_append_assoc (denote i a) (denote i b) (denote i c)
    | Cross Empty _ -> ()
    | Cross a Empty -> lemma_join_empty (fun _ -> Yes) (denote i a)
    | Cross (UnionAll a b) c -> lemma_join_union_left (fun _ -> Yes) (denote i a) (denote i b) (denote i c)
    | Join Never a b -> lemma_join_never (denote i a) (denote i b)
    | Join _ Empty _ -> ()
    | Join p a Empty -> lemma_join_empty (eval_condition i p) (denote i a)
    | Join Always _ _ -> ()
    | Join p (UnionAll a b) c -> lemma_join_union_left (eval_condition i p) (denote i a) (denote i b) (denote i c)
    | CountOne a -> lemma_count_one (denote i a)
    | CountValue e a ->
      assert_norm (eval_condition i (NotNull e) ==
                   (fun r -> of_bool (not (is_null (i.scalars e r)))));
      lemma_count_nullable (i.scalars e) (denote i a)
    | CountWhen p a ->
      assert_norm (denote i (CountWhen p a) ==
        [[eval_aggregate (Count false (fun r -> sql_case (eval_condition i p r) (num 1) Null))
                         (denote i a)]]);
      assert_norm (denote i (CountRows (Filter p a)) ==
        [[eval_aggregate CountStar (select (eval_condition i p) (denote i a))]]);
      lemma_count_case (eval_condition i p) (denote i a)
    | CountRows (UnionAll a b) -> lemma_append_length (denote i a) (denote i b)
    | _ -> ()
#pop-options
