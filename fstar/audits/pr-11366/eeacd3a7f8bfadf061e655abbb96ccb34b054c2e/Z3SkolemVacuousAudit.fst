module Z3SkolemVacuousAudit

(* Independent audit of PR #11366 head eeacd3a7: mirrors `block_parts`/`vacuous`
   from the PR and reuses the unchanged base `substitute`, `source`,
   `instantiation`, `negative_body` from Z3Skolemization (base 48a710a9). *)
open Z3AstTheory
open Z3ResolutionProofTheory
open Z3Skolemization
module L = FStar.List.Tot

let block_parts_m (a b:expr) : option (bool & list sort & expr & expr) =
  match a with
  | Quantifier Exists_k bs s body ->
    if s = bool_sort && get_sort b = bool_sort then Some (false, bs, body, b) else None
  | App n [Quantifier Forall_k bs s body] ->
    if n <> not_decl || s <> bool_sort || get_sort b <> bool_sort then None
    else (match negative_body b with
      | Some target -> Some (true, bs, body, target)
      | None ->
        if Some? (negative_body body) then Some (true, bs, body, mk_not_expr b) else None)
  | _ -> None

let vacuous_m (a b:expr) : bool =
  match block_parts_m a b with
  | Some (negative, sorts, body, _) ->
    let d = { bound_sorts = sorts; negative = negative; body = body;
              dependencies = []; witnesses = [] } in
    get_sort body = bool_sort && source d = a && instantiation d = Some b
  | None -> false

let int_s : sort = BaseSort "Int"

(* O1: z3test 4013 step `exists a:Int. false ~ false` is accepted. *)
let o1 () : Lemma (vacuous_m (Quantifier Exists_k [int_s] bool_sort false_expr) false_expr = true) =
  assert_norm (vacuous_m (Quantifier Exists_k [int_s] bool_sort false_expr) false_expr = true)

(* O2: a used bound variable is rejected, with and without negation. *)
let used : expr = Var 0 bool_sort
let o2 () : Lemma (vacuous_m (Quantifier Exists_k [bool_sort] bool_sort used) used = false /\
                   vacuous_m (Quantifier Exists_k [bool_sort] bool_sort used) false_expr = false) =
  assert_norm (vacuous_m (Quantifier Exists_k [bool_sort] bool_sort used) used = false);
  assert_norm (vacuous_m (Quantifier Exists_k [bool_sort] bool_sort used) false_expr = false)

(* O3: with no witnesses, a successful substitution implies no variable of the block
   (indices depth .. depth+count-1) occurs; this is the PR's central claim. *)
let rec occurs (depth count:nat) (e:expr) : Tot bool (decreases e) =
  match e with
  | Var n _ -> n >= depth && n < depth + count
  | App _ args -> occurs_args depth count args
  | Quantifier _ bs _ b -> occurs (depth + L.length bs) count b
and occurs_args (depth count:nat) (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> false
  | a :: r -> occurs depth count a || occurs_args depth count r

let rec subst_no_occ (depth count:nat) (e:expr)
  : Lemma (ensures (Some? (substitute depth count [] [] e) ==> not (occurs depth count e)))
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ args -> subst_args_no_occ depth count args
  | Quantifier _ bs _ b -> subst_no_occ (depth + L.length bs) count b
and subst_args_no_occ (depth count:nat) (args:list expr)
  : Lemma (ensures (Some? (substitute_args depth count [] [] args) ==> not (occurs_args depth count args)))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: r -> subst_no_occ depth count a; subst_args_no_occ depth count r

(* Converse: if no variable occurs, substitution succeeds (so acceptance is exact). *)
let rec no_occ_subst (depth count:nat) (e:expr)
  : Lemma (ensures (not (occurs depth count e) ==> Some? (substitute depth count [] [] e)))
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ args -> no_occ_args depth count args
  | Quantifier _ bs _ b -> no_occ_subst (depth + L.length bs) count b
and no_occ_args (depth count:nat) (args:list expr)
  : Lemma (ensures (not (occurs_args depth count args) ==> Some? (substitute_args depth count [] [] args)))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: r -> no_occ_subst depth count a; no_occ_args depth count r
