(*
   Z3DagGuardKernel.fst

   Kernel soundness of quantifier introduction under the opt-in DAG guard
   (`verified-dag-v1`): the fragment theorem of
   `Z3BinderKernel.lemma_certificate_sound`, for a prepared certificate
   checked by `Z3DagDocument.verify_binder_dag`, proved from the same typed
   quantifier contract (`Z3TypedQuantifier.quantifier_model`) and the same
   per-entry invariant, with the scope facts of
   `Z3DagDocument.lemma_verify_binder_dag`. No semantic fact is assumed and
   none is cached: the memo of the guard records structural scope facts
   only, and the invariant is the kernel's own, over the checker's cache.
*)
module Z3DagGuardKernel

open Z3AstTheory
open Z3ValueTheory
open Z3UnifiedProof
module CO = Z3CoreModel
module TQ = Z3TypedQuantifier
module BK = Z3BinderKernel
module G = Z3CheckedGuard
module DD = Z3DagDocument
module I = Z3ProofIndex
module SK = Z3Skolemization
module BS = Z3BinderScope
module L = FStar.List.Tot

let lemma_scoped_certificate_sound (skolems:list SK.definition) (i:interpretation value) (dom:CO.domains)
                                   (rho0:env value) (assertions:list judgment)
                                   (c:binder_certificate) (concl:judgment) (rho:env value)
                                   (final:I.index_tree judgment) (t:scope_demands)
  : Lemma (requires TQ.quantifier_model i dom /\ judgments_hold i rho0 assertions /\
                    BK.introduction_fragment skolems assertions c /\
                    check_binder_entries skolems assertions c.binder_entries I.Empty 0 == Some final /\
                    I.index_find final c.binder_root == Some concl /\
                    0 <= c.binder_root /\ c.binder_root < L.length c.binder_entries /\
                    L.memP [] (scope_demanded t c.binder_root) /\ BS.entries_scoped t final 0 c.binder_entries)
          (ensures judgment_holds i rho concl)
  = BK.lemma_entries_typed skolems i dom rho0 assertions t final c.binder_entries I.Empty 0;
    let root : nat = c.binder_root in
    assert (BK.entry_holds i dom t final root);
    BK.lemma_entry_holds i dom t final root;
    assert (CO.env_typed dom [] rho)

(* The prepared certificate's conclusion holds under every environment. *)
let lemma_dag_certificate_sound (skolems:list SK.definition) (i:interpretation value) (dom:CO.domains)
                                (rho0:env value) (assertions:list judgment)
                                (p:DD.prepared) (concl:judgment) (rho:env value)
  : Lemma (requires TQ.quantifier_model i dom /\ judgments_hold i rho0 assertions /\
                    G.BinderGuardChecked? (DD.verify_binder_dag skolems assertions p concl) /\
                    BK.introduction_fragment skolems assertions p.DD.pcert)
          (ensures judgment_holds i rho concl)
  = DD.lemma_verify_binder_dag skolems assertions p concl;
    let c = p.DD.pcert in
    let final = Some?.v (check_binder_entries skolems assertions c.binder_entries I.Empty 0) in
    let aux (t:scope_demands)
      : Lemma (requires 0 <= c.binder_root /\ c.binder_root < L.length c.binder_entries /\
                        L.memP [] (scope_demanded t c.binder_root) /\ BS.entries_scoped t final 0 c.binder_entries)
              (ensures judgment_holds i rho concl)
      = lemma_scoped_certificate_sound skolems i dom rho0 assertions c concl rho final t in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
