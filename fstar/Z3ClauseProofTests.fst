module Z3ClauseProofTests

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3UnifiedProof
open Z3ProofIndex
module C = Z3ClauseProof
module P = Z3ProofDocument

let p_decl : func_decl =
  { decl_name = "p"; domain = []; range = bool_sort; interp = None; int_params = [] }
let q_decl : func_decl = { p_decl with decl_name = "q" }
let or_decl : func_decl =
  { decl_name = "or"; domain = [bool_sort; bool_sort]; range = bool_sort;
    interp = Some op_or; int_params = [] }
let p = App p_decl []
let q = App q_decl []
let np = mk_not_expr p
let nq = mk_not_expr q
let disjunction = App or_decl [p; q]
let lp : C.literal = { C.atom = 2; C.negative = false; C.formula = p }
let lq : C.literal = { C.atom = 3; C.negative = false; C.formula = q }
let lnp = C.opposite lp
let lnq = C.opposite lq

let input (db:C.database) (b:C.builder) (formula:expr) (literals:list C.literal)
  : C.database & C.builder =
  let id, b = C.emit b Asserted formula [] in
  C.add db { C.literals = literals; C.formula = formula; C.proof_id = id }, b

let inputs (aliased:bool) : C.database & C.builder =
  let db, b = C.empty { C.entries = []; C.next = 0 } in
  let db, b = input db b disjunction [lp; if aliased then { lq with C.atom = 2 } else lq] in
  input db b np [lnp]

let finish (b:C.builder) (root:nat) (assertions:list expr) : option P.document =
  C.prune b root >>= (fun (entries, root) ->
  Some { P.declarations = [p_decl; q_decl; or_decl];
         P.expressions = [p; q; np; nq; disjunction; mk_not_expr disjunction; false_expr];
         P.assertions = assertions; P.entries = entries; P.root = root })

let refutation () : option P.document =
  let db, b = inputs false in
  let db, b = input db b nq [lnq] in
  C.prove db b [] false_expr >>= (fun (root, b) -> finish b root [disjunction; np; nq])

let lemma_rup_refutation_is_checked ()
  : Lemma (Some? (refutation ()) /\
           P.check_document (Some?.v (refutation ())) == Some 0)
  = assert_norm (Some? (refutation ()) /\
                 P.check_document (Some?.v (refutation ())) == Some 0)

let satisfiable () : bool =
  let db, b = inputs false in
  None? (C.prove db b [] false_expr)

let lemma_satisfiable_clauses_do_not_refute ()
  : Lemma (satisfiable ())
  = assert_norm (satisfiable ())

let deleted_clause () : bool =
  let db, b = inputs false in
  let db, b = input db b nq [lnq] in
  let db = C.delete db [lq; lp] in
  None? (C.prove db b [] false_expr)

let lemma_deleted_clauses_are_not_available ()
  : Lemma (deleted_clause ())
  = assert_norm (deleted_clause ())

let duplicate_clause () : bool =
  let db, b = inputs false in
  let db, b = input db b disjunction [lp; lq] in
  let db, b = input db b nq [lnq] in
  let db = C.delete db [lq; lp] in
  Some? (C.prove db b [] false_expr) &&
  None? (C.prove (C.delete db [lp; lq]) b [] false_expr)

let lemma_deletion_preserves_other_copies ()
  : Lemma (duplicate_clause ())
  = assert_norm (duplicate_clause ())

let fingerprint_collision () : bool =
  let truth : C.literal = { C.atom = 0; C.negative = false; C.formula = true_expr } in
  let left = [lp; lnp] in
  let right = [truth; lnq] in
  let db, b = C.empty { C.entries = []; C.next = 0 } in
  let db, b = input db b (App or_decl [p; np]) left in
  let db, _ = input db b (App or_decl [true_expr; nq]) right in
  C.fingerprint left = C.fingerprint right && db.C.next_clause = 4

let lemma_fingerprints_do_not_identify_clauses ()
  : Lemma (fingerprint_collision ())
  = assert_norm (fingerprint_collision ())

let learned_unit () : option P.document =
  let db, b = inputs false in
  C.prove db b [lq] q >>= (fun (id, b) ->
  let db = C.add db { C.literals = [lq]; C.formula = q; C.proof_id = id } in
  let db, b = input db b nq [lnq] in
  C.prove db b [] false_expr >>= (fun (root, b) -> finish b root [disjunction; np; nq]))

let lemma_rup_hypotheses_are_discharged ()
  : Lemma (Some? (learned_unit ()) /\
           P.check_document (Some?.v (learned_unit ())) == Some 0)
  = assert_norm (Some? (learned_unit ()) /\
                 P.check_document (Some?.v (learned_unit ())) == Some 0)

let disjunction_literal () : option P.document =
  let db, b = C.empty { C.entries = []; C.next = 0 } in
  let literal : C.literal =
    { C.atom = 4; C.negative = false; C.formula = disjunction } in
  let db, b = input db b disjunction [literal] in
  let db, b = input db b disjunction [lp; lq] in
  let db = C.delete db [lp; lq] in
  let negation = mk_not_expr disjunction in
  let db, b = input db b negation [C.opposite literal] in
  C.prove db b [] false_expr >>= (fun (root, b) ->
  finish b root [disjunction; negation])

let lemma_disjunction_literals_are_not_flattened ()
  : Lemma (Some? (disjunction_literal ()) /\
           P.check_document (Some?.v (disjunction_literal ())) == Some 0)
  = assert_norm (Some? (disjunction_literal ()) /\
                 P.check_document (Some?.v (disjunction_literal ())) == Some 0)

let cached_deletion () : bool =
  let db, b = inputs false in
  match C.prove_cached db b [lq] q with
  | None -> false
  | Some (_, b, db) ->
    let db = C.delete db [lp; lq] in
    let db, b = input db b nq [lnq] in
    None? (C.prove db b [] false_expr)

let lemma_deletion_invalidates_cached_propagations ()
  : Lemma (cached_deletion ())
  = assert_norm (cached_deletion ())

let aliased_literals () : bool =
  let db, b = inputs true in
  match C.prove db b [] false_expr with
  | None -> true
  | Some (root, b) ->
    match finish b root [disjunction; np] with
    | None -> true
    | Some doc -> P.check_document doc = None

let lemma_literal_indices_are_not_trusted ()
  : Lemma (aliased_literals ())
  = assert_norm (aliased_literals ())

let missing_assertion () : bool =
  match refutation () with
  | None -> false
  | Some doc -> P.check_document { doc with P.assertions = [disjunction; nq] } = None

let lemma_original_assertions_are_required ()
  : Lemma (missing_assertion ())
  = assert_norm (missing_assertion ())
