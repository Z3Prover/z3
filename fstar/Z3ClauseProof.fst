module Z3ClauseProof

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3UnifiedProof
open Z3ProofIndex
open FStar.List.Tot
module P = Z3ProofDocument
module L = FStar.List.Tot

(* This elaborator produces ordinary hypotheses, unit resolutions, and
   discharged lemmas. The document kernel checks every selected proof step;
   neither literal IDs nor the elaborator's propagation results are trusted. *)
type literal = {
  atom: nat;
  negative: bool;
  formula: expr;
}

type clause = {
  literals: list literal;
  formula: expr;
  proof_id: nat;
}

type builder = {
  entries: list P.entry;
  next: nat;
}

type assigned_literal = {
  negative: bool;
  proof_id: nat;
}

type assignment = index_tree assigned_literal

noeq
type database = {
  clauses: index_tree (option clause);
  occurrences: index_tree (list nat);
  fingerprints: index_tree (list nat);
  copies: index_tree nat;
  units: list nat;
  next_clause: nat;
  literal_count: nat;
  cached_values: assignment;
  cached_conflict: option nat;
  pending_clauses: list nat;
}

let proof_index (id:nat) : int = id

let emit (b:builder) (kind:rule) (formula:expr) (premises:list int) : nat & builder =
  b.next, { entries = { P.rule = kind; P.formula = formula;
                       P.premise_ids = premises } :: b.entries; next = b.next + 1 }

let key (atom:nat) (negative:bool) : nat = 2 * atom + (if negative then 1 else 0)

let rec member (lit:literal) (lits:list literal) : Tot bool (decreases lits) =
  match lits with
  | [] -> false
  | l :: rest -> (l.atom = lit.atom && l.negative = lit.negative) || member lit rest

let rec unique (lits:list literal) : Tot (list literal) (decreases lits) =
  match lits with
  | [] -> []
  | l :: rest -> if member l rest then unique rest else l :: unique rest

let rec same_clause (left right:list literal) : Tot bool (decreases left) =
  match left with
  | [] -> true
  | l :: rest -> member l right && same_clause rest right

let rec fingerprint (lits:list literal) : Tot nat (decreases lits) =
  match lits with
  | [] -> 0
  | l :: rest ->
    let k = key l.atom l.negative in
    ((k + 1) * (k + 3) + fingerprint rest) % 1048573

let rec find_duplicate (db:database) (lits:list literal) (ids:list nat)
  : Tot (option nat) (decreases ids) =
  match ids with
  | [] -> None
  | id :: rest ->
    match index_get db.clauses id with
    | Some (Some c) ->
      if same_clause lits c.literals && same_clause c.literals lits then Some id
      else find_duplicate db lits rest
    | _ -> find_duplicate db lits rest

let rec index_literals (index:index_tree (list nat)) (id:nat) (lits:list literal)
  : Tot (index_tree (list nat)) (decreases lits) =
  match lits with
  | [] -> index
  | l :: rest ->
    let k = key l.atom l.negative in
    let old = match index_get index k with Some ids -> ids | None -> [] in
    index_literals (index_put index k (id :: old)) id rest

let add (db:database) (c:clause) : database =
  let literals = unique c.literals in
  let hash = fingerprint literals in
  let candidates = match index_get db.fingerprints hash with Some ids -> ids | None -> [] in
  match find_duplicate db literals candidates with
  | Some id ->
    let copies = match index_get db.copies id with Some n -> n | None -> 0 in
    { db with copies = index_put db.copies id (copies + 1) }
  | None ->
  { clauses = index_put db.clauses db.next_clause (Some c);
    occurrences = index_literals db.occurrences db.next_clause literals;
    fingerprints = index_put db.fingerprints hash (db.next_clause :: candidates);
    copies = index_put db.copies db.next_clause 1;
    units = if L.length literals <= 1 then db.next_clause :: db.units else db.units;
    next_clause = db.next_clause + 1;
    literal_count = db.literal_count + L.length c.literals;
    cached_values = db.cached_values;
    cached_conflict = db.cached_conflict;
    pending_clauses = db.next_clause :: db.pending_clauses }

let empty (b:builder) : database & builder =
  let truth, b = emit b DefAxiom true_expr [] in
  let not_false = mk_not_expr false_expr in
  let falsehood, b = emit b DefAxiom not_false [] in
  let db = { clauses = Empty; occurrences = Empty; fingerprints = Empty; copies = Empty;
             units = [];
             next_clause = 0; literal_count = 0;
             cached_values = Empty; cached_conflict = None; pending_clauses = [] } in
  let db = add db { literals = [{ atom = 0; negative = false; formula = true_expr }];
                    formula = true_expr; proof_id = truth } in
  let db = add db { literals = [{ atom = 1; negative = true; formula = not_false }];
                    formula = not_false; proof_id = falsehood } in
  db, b

let affected (db:database) (lit:literal) : list nat =
  match index_get db.occurrences (key lit.atom (not lit.negative)) with
  | Some ids -> ids
  | None -> []

let rec delete_from (db:database) (lits:list literal) (ids:list nat)
  : Tot database (decreases ids) =
  match ids with
  | [] -> db
  | id :: rest ->
    (match index_get db.clauses id with
     | Some (Some c) ->
       if same_clause lits c.literals && same_clause c.literals lits then
         let copies = match index_get db.copies id with Some n -> n | None -> 0 in
         if copies > 1 then { db with copies = index_put db.copies id (copies - 1) }
         else
           { db with clauses = index_put db.clauses id None;
                     cached_values = Empty; cached_conflict = None;
                     pending_clauses = db.units }
       else delete_from db lits rest
     | _ -> delete_from db lits rest)

let delete (db:database) (lits:list literal) : database =
  let candidates =
    match lits with
    | [] -> db.units
    | l :: _ ->
      (match index_get db.occurrences (key l.atom l.negative) with
       | Some ids -> ids | None -> []) in
  delete_from db lits candidates

type residual =
  | Satisfied
  | Residual : unknown:list literal -> units:list int -> residual

let rec reduce_clause (values:assignment) (lits unknown:list literal) (units:list int)
  : Tot residual (decreases lits) =
  match lits with
  | [] -> Residual unknown units
  | l :: rest ->
    (match index_get values l.atom with
     | Some a ->
       if a.negative = l.negative then Satisfied
       else reduce_clause values rest unknown (a.proof_id :: units)
     | None ->
       reduce_clause values rest (if member l unknown then unknown else l :: unknown) units)

noeq
type propagation =
  | Conflict : proof_id:nat -> builder:builder -> propagation
  | Pending : values:assignment -> jobs:list nat -> builder:builder -> propagation

let assign (db:database) (b:builder) (values:assignment) (jobs:list nat)
           (lit:literal) (id:nat) : propagation =
  match index_get values lit.atom with
  | Some a ->
    if a.negative = lit.negative then Pending values jobs b
    else
      let contradiction, b = emit b UnitResolution false_expr [a.proof_id; id] in
      Conflict contradiction b
  | None ->
    let values = index_put values lit.atom { negative = lit.negative; proof_id = id } in
    Pending values (affected db lit @ jobs) b

let rec propagate (fuel:nat) (db:database) (b:builder)
                  (values:assignment) (jobs:list nat)
  : Tot propagation (decreases %[fuel; L.length jobs]) =
  match jobs with
  | [] -> Pending values [] b
  | id :: rest ->
    match index_get db.clauses id with
    | Some (Some c) ->
      (match reduce_clause values c.literals [] [] with
       | Residual [] units ->
         let contradiction, b = emit b UnitResolution false_expr (c.proof_id :: units) in
         Conflict contradiction b
       | Residual [lit] units ->
         if fuel = 0 then Pending values jobs b else
         let id, b = emit b UnitResolution lit.formula (c.proof_id :: units) in
         (match assign db b values rest lit id with
          | Conflict contradiction b -> Conflict contradiction b
          | Pending values jobs b -> propagate (fuel - 1) db b values jobs)
       | _ -> propagate fuel db b values rest)
    | _ -> propagate fuel db b values rest

let opposite (lit:literal) : literal =
  { atom = lit.atom; negative = not lit.negative;
    formula = match lit.formula with
              | App d [e] -> if d.interp = Some op_not then e else mk_not_expr lit.formula
              | _ -> mk_not_expr lit.formula }

let rec hypotheses (db:database) (b:builder) (values:assignment)
                   (jobs:list nat) (lits:list literal) : Tot propagation (decreases lits) =
  match lits with
  | [] -> Pending values jobs b
  | l :: rest ->
    let l = opposite l in
    let id, b = emit b Hypothesis l.formula [] in
    match assign db b values jobs l id with
    | Conflict contradiction b -> Conflict contradiction b
    | Pending values jobs b -> hypotheses db b values jobs rest

let prove_cached (db:database) (b:builder) (lits:list literal) (formula:expr)
  : option (nat & builder & database) =
  let fuel = db.literal_count + L.length lits + 3 in
  let base = match db.cached_conflict with
    | Some id -> Conflict id b
    | None -> propagate fuel db b db.cached_values db.pending_clauses in
  let db = match base with
    | Conflict id _ -> { db with cached_conflict = Some id; pending_clauses = [] }
    | Pending values [] _ -> { db with cached_values = values; pending_clauses = [] }
    | _ -> db in
  let contradiction : option (nat & builder) =
    match base with
    | Conflict id b -> Some (id, b)
    | Pending values [] b ->
      (match hypotheses db b values [] lits with
       | Conflict id b -> Some (id, b)
       | Pending values jobs b ->
         match propagate fuel db b values jobs with
         | Conflict id b -> Some (id, b)
         | _ -> None)
    | _ -> None in
  contradiction >>= (fun (id, b) ->
    let lemma, b = emit b LemmaRule formula [id] in
    Some (lemma, b, db))

let prove (db:database) (b:builder) (lits:list literal) (formula:expr)
  : option (nat & builder) =
  prove_cached db b lits formula >>= (fun (id, b, _) -> Some (id, b))

let rec mark_premises (needed:index_tree bool) (ids:list int)
  : Tot (index_tree bool) (decreases ids) =
  match ids with
  | [] -> needed
  | id :: rest ->
    mark_premises (if id < 0 then needed else index_put needed id true) rest

let rec select_entries (entries:list P.entry) (remaining:nat) (needed:index_tree bool)
                       (selected:list (nat & P.entry))
  : Tot (option (list (nat & P.entry))) (decreases entries) =
  match entries with
  | [] -> Some selected
  | e :: rest ->
    if remaining = 0 then None else
    let id = remaining - 1 in
    if index_get needed id = Some true then
      select_entries rest id (mark_premises needed e.P.premise_ids) ((id, e) :: selected)
    else select_entries rest id needed selected

let rec reindex (entries:list (nat & P.entry)) (indices:index_tree nat)
                (next:nat) (result:list P.entry)
  : Tot (option (index_tree nat & list P.entry)) (decreases entries) =
  match entries with
  | [] -> Some (indices, L.rev result)
  | (id, e) :: rest ->
    opt_map (fun old -> index_find indices old >>= (fun fresh -> Some (proof_index fresh)))
      e.P.premise_ids >>= (fun premises ->
    reindex rest (index_put indices id next) (next + 1)
      ({ e with P.premise_ids = premises } :: result))

let prune (b:builder) (root:nat) : option (list P.entry & nat) =
  select_entries b.entries b.next (index_put Empty root true) [] >>= (fun entries ->
  reindex entries Empty 0 [] >>= (fun (indices, entries) ->
  index_get indices root >>= (fun root -> Some (entries, root))))
