(*
   Z3BinderScope.fst

   Structural theorems about the scope guard of binder certificates
   (`Z3UnifiedProof.binder_scoped`), with no semantic model.

   A certificate's entries are judgments at different binder depths. The
   guard assigns every entry the scopes at which the root uses it, starting
   from the root at the closed top-level scope `[]`, and checks every entry's
   judgment at each of its scopes, within explicit resource bounds.

   * Specification. `entries_scoped` states the forward check without work
     accounting: every assigned scope of every entry scopes its judgment
     (`binder_judgment_scoped`, i.e. `Z3Definitions.scoped` of each side),
     and every premise is an earlier entry assigned the premise scope
     (`premise_scope_of`: `L.rev bs @ s` under binder sorts `bs`, else `s`).
     `lemma_entries_checked` proves that the bounded executable check implies
     it: the work-counted primitives compute exactly the list length, scope
     membership and `Z3Definitions.scoped` whenever they finish. The guard
     builds the scope under binders with the loop `scope_under`, which is
     `L.rev_acc` and `L.rev bs @ s` (`lemma_scope_under`), and walks
     expressions and compares sorts over explicit worklists. The recursive
     definitions of 0ebb92579 are kept for the proof only (`*_rec`,
     `binder_premise_scope_append`), and the loops change no result and no
     remaining work (`lemma_sort_same`, `lemma_sort_list_same`,
     `lemma_scoped_same`, `lemma_scoped_args_same`,
     `lemma_premise_scope_same`).
   * Theorem 1, `lemma_root_scoped` / `lemma_checked_root_scoped`: the root is
     an entry, it is assigned `[]`, and its judgment (the node conclusion) is
     scoped at `[]` (closed and well sorted).
   * Theorem 2, `lemma_edge_scoped`: for every entry `k`, every scope `s`
     assigned to it and every premise `p` of it, `k`'s judgment is scoped at
     `s`, `p` is an earlier entry (`0 <= p < k`), `p` was assigned the scope
     `premise_scope_of k s`, and `p`'s judgment is scoped there. A shared entry
     is checked at every scope it is assigned.
   * `lemma_checked_guard`: `check_binder_with_context` accepts only when
     `check_binder_entries` builds a cache holding the conclusion at the root
     and the guard holds on that cache with the checker's bounds; the
     theorems then apply to the checker's own cache.

   These are facts about the guard's decision only. They do not make any
   rule's step semantically sound; `Z3BinderKernel` proves that for a
   fragment of entry kinds.
*)
module Z3BinderScope

open Z3AstTheory
open Z3UnifiedProof
module I = Z3ProofIndex
module D = Z3Definitions
module DV = Z3DatatypeValue
module SK = Z3Skolemization
module L = FStar.List.Tot

include Z3BinderScopeIndependent

let lemma_checked_guard (skolems:list SK.definition) (assertions:list judgment)
                        (c:binder_certificate) (concl:judgment)
  : Lemma (requires check_binder_with_context skolems assertions c concl)
          (ensures Some? (check_binder_entries skolems assertions c.binder_entries I.Empty 0) /\
                   (let cache = Some?.v (check_binder_entries skolems assertions c.binder_entries I.Empty 0) in
                    let n = L.length c.binder_entries in
                    I.index_find cache c.binder_root == Some concl /\
                    binder_scoped_within (binder_demand_limit n) (binder_work_limit n) c cache))
  = lemma_count_cells 0 c.binder_entries

let lemma_checked_root_scoped (skolems:list SK.definition) (assertions:list judgment)
                              (c:binder_certificate) (concl:judgment)
  : Lemma (requires check_binder_with_context skolems assertions c concl)
          (ensures binder_judgment_scoped [] concl)
  = lemma_checked_guard skolems assertions c concl;
    let cache = Some?.v (check_binder_entries skolems assertions c.binder_entries I.Empty 0) in
    let n = L.length c.binder_entries in
    lemma_root_scoped (binder_demand_limit n) (binder_work_limit n) c cache
