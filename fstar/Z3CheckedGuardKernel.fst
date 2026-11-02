(*
   Z3CheckedGuardKernel.fst

   Kernel soundness of quantifier introduction under the opt-in guard: the
   fragment theorem of `Z3BinderKernel.lemma_certificate_sound`, proved from
   the same typed quantifier contract (`Z3TypedQuantifier.quantifier_model`)
   and the same per-entry invariant, with the scope facts taken from
   `Z3CheckedGuardProof.lemma_verified_guard` instead of the old guard. No
   semantic fact is assumed and no truth is cached: the invariant is the
   kernel's own, over the checker's cache and the demand table the checked
   ids denote.
*)
module Z3CheckedGuardKernel

open Z3AstTheory
open Z3ValueTheory
open Z3UnifiedProof
module CO = Z3CoreModel
module TQ = Z3TypedQuantifier
module BK = Z3BinderKernel
module G = Z3CheckedGuard
module GP = Z3CheckedGuardProof
module I = Z3ProofIndex
module SK = Z3Skolemization
module L = FStar.List.Tot

(* The certificate's conclusion holds under every environment. *)
let lemma_verified_certificate_sound (skolems:list SK.definition) (i:interpretation value) (dom:CO.domains)
                                     (rho0:env value) (assertions:list judgment)
                                     (c:binder_certificate) (concl:judgment) (rho:env value)
  : Lemma (requires TQ.quantifier_model i dom /\ judgments_hold i rho0 assertions /\
                    G.check_binder_verified skolems assertions c concl /\
                    BK.introduction_fragment skolems assertions c)
          (ensures judgment_holds i rho concl)
  = GP.lemma_verified_checked_guard skolems assertions c concl;
    let final = Some?.v (check_binder_entries skolems assertions c.binder_entries I.Empty 0) in
    let n = L.length c.binder_entries in
    GP.lemma_verified_guard (G.verified_budget n) c final;
    let t = GP.checked_demands (G.Checked?.state (G.verified_guard (G.verified_budget n) c final)) in
    BK.lemma_entries_typed skolems i dom rho0 assertions t final c.binder_entries I.Empty 0;
    let root : nat = c.binder_root in
    assert (L.memP [] (scope_demanded t root));
    assert (BK.entry_holds i dom t final root);
    BK.lemma_entry_holds i dom t final root;
    assert (CO.env_typed dom [] rho)
