module Z3DemodVisited
(* Model of match_args_aux_proc (demodulator_rewriter.cpp) visiting nodes of a term DAG.
   PR change: for_each_expr(proc, arg) -> for_each_expr(proc, visited, arg), i.e. each
   distinct node is visited once instead of once per path. Non-var/non-quantifier apps are no-ops. *)
type node = | V : nat -> node | Q : node | A : node

(* substitution on variables: None = unbound, Some b = bound to b; "self" binding means b = k *)
type st = nat -> option nat

let upd (s:st) (k:nat) : st = fun j -> if j = k then Some k else s j

let visit (s:st) (n:node) : option st =
  match n with
  | Q -> None
  | A -> Some s
  | V k -> (match s k with
            | Some b -> if b = k then Some s else None
            | None -> Some (upd s k))

let rec run (s:st) (l:list node) : Tot (option st) (decreases l) =
  match l with
  | [] -> Some s
  | n :: r -> (match visit s n with None -> None | Some s' -> run s' r)

(* O1: revisiting a node right after visiting it is a no-op *)
let visit_idem (s:st) (n:node) : Lemma
  (match visit s n with None -> True | Some s' -> visit s' n == Some s') = ()

(* O2: a visited-node is stable: any later visit of n after n has been visited succeeds
   unchanged, provided intervening visits only add bindings (never rebind). *)
let visit_preserves (s:st) (n m:node) : Lemma
  (match visit s n with
   | None -> True
   | Some s' -> forall k. s k =!= None ==> s' k == s k) = ()

let rec run_preserves (s:st) (l:list node) : Lemma (ensures
  (match run s l with None -> True | Some s' -> forall k. Some? (s k) ==> s' k == s k))
  (decreases l) =
  match l with
  | [] -> ()
  | n :: r -> (match visit s n with None -> () | Some s' -> run_preserves s' r)

let rec app (a b:list node) : Tot (list node) (decreases a) =
  match a with [] -> b | h :: t -> h :: app t b

(* x is already visited in s: a visit of x is a no-op *)
let seen (s:st) (x:node) : prop =
  match x with V k -> s k == Some k | _ -> True

let seen_visit (s:st) (x:node) : Lemma (requires seen s x /\ x <> Q)
  (ensures visit s x == Some s) = ()

(* O3: dropping a repeat of an already-visited node preserves the result of the traversal *)
let rec dup_ok (s:st) (x:node) (l2 l3:list node) : Lemma
  (requires seen s x /\ x <> Q)
  (ensures run s (app l2 (x :: l3)) == run s (app l2 l3))
  (decreases l2) =
  match l2 with
  | [] -> seen_visit s x
  | n :: r ->
    (match visit s n with
     | None -> ()
     | Some s' ->
       visit_preserves s n n;
       (match x with V k -> (match s k with Some _ -> () | None -> ()) | _ -> ());
       dup_ok s' x r l3)
