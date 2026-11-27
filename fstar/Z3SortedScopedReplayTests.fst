module Z3SortedScopedReplayTests

open Z3AstTheory
module U = Z3UnifiedProof
module P = Z3ProofDocument
module I = Z3ProofIndex
module IT = Z3IdTable
module F = Z3DocumentFactSemantics
module Scoped = Z3SortedScopedReplay
module Cases = Z3SortedRelationalTests
module LemmaCases = Z3SortedLemmaFactsTests
module SC = Z3SortedRelational
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3DefinitionRecognition
module L = FStar.List.Tot
module MPCases = Z3SortedModusPonensTests

let table = IT.put IT.empty 0 LemmaCases.false_fact
let entry : P.entry = { P.rule = U.LemmaRule; P.formula = LemmaCases.disj; P.premise_ids = [0] }

let supported ()
  : Lemma (Scoped.entries_supported Cases.scope false [] [entry]) =
  let at (cache:IT.t U.checked_fact) (e:P.entry) (node:U.proof_node)
    : Lemma (L.mem e [entry] /\ P.prepare_entry_table false [] cache e == Some node ==>
             Scoped.node_supported Cases.scope node) =
    I.lemma_opt_map_tail (IT.find cache) [0];
    match I.opt_map (IT.find cache) [0] with
    | Some _ -> ()
    | None -> () in
  FStar.Classical.forall_intro_3 at

let lemma_replay (#base:sort -> Type0) (s:S.checked_schema)
                 (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                 (other:V.interpretation base (S.signature s))
                 (rho:V.environment base (S.signature s) Cases.scope)
  : Lemma (requires SC.fact_holds s bc eq other Cases.scope rho LemmaCases.false_fact)
          (ensures F.table_holds (Scoped.scoped_fact s bc eq other Cases.scope rho)
                     (IT.put table 1 LemmaCases.result)) =
  let good = Scoped.scoped_fact s bc eq other Cases.scope rho in
  F.lemma_empty good;
  F.lemma_put good IT.empty 0 LemmaCases.false_fact;
  IT.lemma_find_put IT.empty 0 LemmaCases.false_fact 0;
  I.lemma_opt_map_tail (IT.find table) [0];
  supported ();
  assert (P.prepare_entry_table false [] table entry == Some LemmaCases.node);
  assert_norm (U.check_node_with_membership [] true [] (fun _ -> false) LemmaCases.node ==
               Some (LemmaCases.result, 0));
  assert (P.check_entry_table [] true false [] [] (fun _ -> false) table entry ==
          Some (LemmaCases.result, 0));
  assert (P.checker_using D.linear_expander [] true false [] [] (fun _ -> false) table entry ==
          Some (LemmaCases.result, 0));
  assert (P.diagnose_entries_using (P.checker_using D.linear_expander)
            [] false [] [] (fun _ -> false) table 1 0 [] [entry] ==
          P.EntriesChecked (IT.put table 1 LemmaCases.result) 0 []);
  Scoped.lemma_entries s bc eq other Cases.scope rho [] false [] [] (fun _ -> false)
    table 1 [] [entry] (IT.put table 1 LemmaCases.result) []

let mp_table = IT.put (IT.put IT.empty 0 MPCases.premise) 1 MPCases.observation
let mp_entry : P.entry = { P.rule = U.ObservationalMP; P.formula = Cases.q; P.premise_ids = [0; 1] }

let mp_supported ()
  : Lemma (Scoped.entries_supported Cases.scope false [] [mp_entry]) =
  let at (cache:IT.t U.checked_fact) (e:P.entry) (node:U.proof_node)
    : Lemma (L.mem e [mp_entry] /\ P.prepare_entry_table false [] cache e == Some node ==>
             Scoped.node_supported Cases.scope node) =
    I.lemma_opt_map_tail (IT.find cache) [0; 1];
    match I.opt_map (IT.find cache) [0; 1] with
    | Some _ -> ()
    | None -> () in
  FStar.Classical.forall_intro_3 at

let observational_mp_replay (#base:sort -> Type0) (s:S.checked_schema)
                            (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                            (other:V.interpretation base (S.signature s))
                            (rho:V.environment base (S.signature s) Cases.scope)
  : Lemma (requires SC.fact_holds s bc eq other Cases.scope rho MPCases.premise /\
                    SC.fact_holds s bc eq other Cases.scope rho MPCases.observation)
          (ensures F.table_holds (Scoped.scoped_fact s bc eq other Cases.scope rho)
                     (IT.put mp_table 2 MPCases.result)) =
  let good = Scoped.scoped_fact s bc eq other Cases.scope rho in
  F.lemma_empty good;
  F.lemma_put good IT.empty 0 MPCases.premise;
  F.lemma_put good (IT.put IT.empty 0 MPCases.premise) 1 MPCases.observation;
  IT.lemma_find_put (IT.put IT.empty 0 MPCases.premise) 1 MPCases.observation 0;
  IT.lemma_find_put (IT.put IT.empty 0 MPCases.premise) 1 MPCases.observation 1;
  IT.lemma_find_put IT.empty 0 MPCases.premise 0;
  I.lemma_opt_map_tail (IT.find mp_table) [0; 1];
  mp_supported ();
  assert (P.prepare_entry_table false [] mp_table mp_entry == Some MPCases.obs_node);
  assert_norm (U.check_node_with_membership [] true [] (fun _ -> false) MPCases.obs_node ==
               Some (MPCases.result, 0));
  assert (P.check_entry_table [] true false [] [] (fun _ -> false) mp_table mp_entry ==
          Some (MPCases.result, 0));
  assert (P.checker_using D.linear_expander [] true false [] [] (fun _ -> false) mp_table mp_entry ==
          Some (MPCases.result, 0));
  assert (P.diagnose_entries_using (P.checker_using D.linear_expander)
            [] false [] [] (fun _ -> false) mp_table 2 0 [] [mp_entry] ==
          P.EntriesChecked (IT.put mp_table 2 MPCases.result) 0 []);
  Scoped.lemma_entries s bc eq other Cases.scope rho [] false [] [] (fun _ -> false)
    mp_table 2 [] [mp_entry] (IT.put mp_table 2 MPCases.result) []
