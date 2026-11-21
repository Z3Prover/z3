module Z3IndependentBinderReplay

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module U = Z3UnifiedProofSyntax
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module RL = Z3SortedReal
module NR = Z3NnfReplay
module BG = Z3BinderScopeSyntax
module BS = Z3BinderScopeIndependent
module I = Z3ProofIndex
module L = FStar.List.Tot

let replay (real:bool) (assertions:list expr) (c:U.binder_certificate)
           (concl:U.judgment) : NR.verdict =
  if not (NR.consumed_root c) then NR.Unreplayed
  else if not (NR.well_indexed c.U.binder_entries 0) then NR.Malformed
  else
    let n = BG.count_cells 0 c.U.binder_entries in
    let root = c.U.binder_root in
    match NR.judgments_of c.U.binder_entries I.Empty 0 with
    | None -> NR.Unreplayed
    | Some cache ->
      if not (0 <= root && root < n && I.index_find cache root = Some concl) then NR.Unreplayed
      else match BG.binder_scopes (BG.binder_demand_limit n) (8 * BG.binder_work_limit n) c with
      | None -> NR.Unreplayed
      | Some (t, w) ->
        if L.mem [] (BG.scope_demanded t root) &&
           Some? (BG.scope_entries_checked t cache 0 c.U.binder_entries w) &&
           NR.steps_ok real (NR.quant_intro_root c) assertions (BG.count_cells 0 assertions)
             t cache I.Empty 0 c.U.binder_entries (BG.binder_work_limit n)
        then NR.Replayed else NR.Unreplayed

let lemma_replay (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (real:bool) (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (real ==> RL.real_model s bc eq other) /\
                    T.truths s bc eq other assertions /\ replay real assertions c concl == NR.Replayed)
          (ensures BS.binder_judgment_scoped [] concl /\
                   NR.holds_at s bc eq other [] (T.empty_environment (S.signature s)) concl) =
  let entries = c.U.binder_entries in
  let n = BG.count_cells 0 entries in
  let root = c.U.binder_root in
  match NR.judgments_of entries I.Empty 0 with
  | None -> ()
  | Some cache ->
    (match BG.binder_scopes (BG.binder_demand_limit n) (8 * BG.binder_work_limit n) c with
     | None -> ()
     | Some (t, w) ->
       assert (BG.binder_scoped_within (BG.binder_demand_limit n) (8 * BG.binder_work_limit n) c cache);
       BS.lemma_guard (BG.binder_demand_limit n) (8 * BG.binder_work_limit n) c cache;
       BS.lemma_count_cells 0 entries;
       NR.lemma_steps s bc eq other real (NR.quant_intro_root c) assertions (BG.count_cells 0 assertions)
         t cache I.Empty 0 entries (BG.binder_work_limit n);
       let key : nat = root in
       assert (NR.entry_valid s bc eq other t cache key);
       NR.lemma_entry_valid_def s bc eq other t cache key;
       BS.lemma_scoped_at t cache entries key [])
