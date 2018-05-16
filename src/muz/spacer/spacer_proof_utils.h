/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_proof_utils.cpp

Abstract:
    Utilities to traverse and manipulate proofs

Author:
    Bernhard Gleiss
    Arie Gurfinkel

Revision History:

--*/

#ifndef _SPACER_PROOF_UTILS_H_
#define _SPACER_PROOF_UTILS_H_
#include "ast/ast.h"

namespace spacer {

bool is_arith_lemma(ast_manager& m, proof* pr);
bool is_farkas_lemma(ast_manager& m, proof* pr);

/// rewrites theory axioms into theory lemmas
class theory_axiom_reducer {
public:
    theory_axiom_reducer(ast_manager& m) : m(m), m_pinned(m) {}

    // reduce theory axioms and return transformed proof
    proof_ref reduce(proof* pr);

private:
    ast_manager &m;

    // tracking all created expressions
    expr_ref_vector m_pinned;

    // maps each proof of a clause to the transformed subproof of
    // that clause
    obj_map<proof, proof*> m_cache;

    void reset();
};

class hypothesis_reducer
{
public:
    hypothesis_reducer(ast_manager &m) : m(m), m_pinned(m) {}

    // reduce hypothesis and return transformed proof
    proof_ref reduce(proof* pf);

private:
    typedef obj_hashtable<expr> expr_set;
    typedef obj_hashtable<proof> proof_set;

    ast_manager &m;

    // created expressions
    expr_ref_vector m_pinned;

    // created sets of active hypothesis
    ptr_vector<proof_set> m_pinned_active_hyps;
    // created sets of parent hypothesis
    ptr_vector<expr_set> m_pinned_parent_hyps;

    // maps a proof to the transformed proof
    obj_map<proof, proof*> m_cache;

    // maps a unit literal to its derivation
    obj_map<expr, proof*> m_units;

    // maps a proof to the set of proofs of active hypotheses
    obj_map<proof, proof_set*> m_active_hyps;
    // maps a proof to the hypothesis-fact that are transitive
    // parents of that proof.  Used for cycle detection and avoidance.
    obj_map<proof, expr_set*> m_parent_hyps;

    void reset();

    // compute active_hyps and parent_hyps for pr
    void compute_hypsets(proof* pr);
    // compute m_units
    void collect_units(proof* pr);
    proof* compute_transformed_proof(proof* pf);

    proof* mk_lemma_core(proof *pf, expr *fact);
    proof* mk_unit_resolution_core(ptr_buffer<proof>& args);
    proof* mk_step_core(proof* old_step, ptr_buffer<proof>& args);
};
}
#endif
