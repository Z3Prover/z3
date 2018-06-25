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

/// reduces the number of hypotheses in a proof
class hypothesis_reducer
{
public:
    hypothesis_reducer(ast_manager &m) : m(m), m_pinned(m) {}
    ~hypothesis_reducer() {reset();}

    // reduce hypothesis and return transformed proof
    proof_ref reduce(proof* pf);

private:
    typedef ptr_vector<proof> proof_ptr_vector;

    ast_manager &m;

    proof_ptr_vector m_empty_vector;

    // created expressions
    expr_ref_vector m_pinned;

    // created sets of active hypothesis
    ptr_vector<proof_ptr_vector> m_pinned_active_hyps;

    // maps a proof to the transformed proof
    obj_map<proof, proof*> m_cache;

    // maps a unit literal to its derivation
    obj_map<expr, proof*> m_units;

    // maps a proof node to the set of its  active (i.e., in scope) hypotheses
    obj_map<proof, proof_ptr_vector*> m_active_hyps;

    /// marks if an expression is ever used as a hypothesis in a proof
    expr_mark m_hyp_mark;
    /// marks a proof as open, i.e., has a non-discharged hypothesis as ancestor
    expr_mark m_open_mark;
    expr_mark m_visited;

    void reset();

    /// true if p is an ancestor of q
    bool is_ancestor(proof *p, proof *q);
    // compute active_hyps and parent_hyps for a given proof node and
    // all its ancestors
    void compute_hypsets(proof* pr);
    // compute m_units
    void collect_units(proof* pr);

    // -- rewrite proof to reduce number of hypotheses used
    proof* reduce_core(proof* pf);

    proof* mk_lemma_core(proof *pf, expr *fact);
    proof* mk_unit_resolution_core(proof* ures, ptr_buffer<proof>& args);
    proof* mk_proof_core(proof* old, ptr_buffer<proof>& args);
};
}
#endif
