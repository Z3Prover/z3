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
/*
 * iterator, which traverses the proof in depth-first post-order.
 */
class ProofIteratorPostOrder {
public:
    ProofIteratorPostOrder(proof* refutation, ast_manager& manager);
    bool hasNext();
    proof* next();

private:
    ptr_vector<proof> m_todo;
    ast_mark m_visited; // the proof nodes we have already visited

    ast_manager& m;
};

    /*
     * prints the proof pr in dot representation to the file proof.dot
     * if iuc_pr is not nullptr, then it is queried for coloring partitions
     */
    class iuc_proof;
    void pp_proof_dot(ast_manager& m, proof* pr, iuc_proof* iuc_pr = nullptr);
    
    class theory_axiom_reducer
    {
    public:
        theory_axiom_reducer(ast_manager& m) : m(m), m_pinned(m) {}

        // reduce theory axioms and return transformed proof
        proof_ref reduce(proof* pr);
        
    private:
        ast_manager &m;
        
        // tracking all created expressions
        expr_ref_vector m_pinned;
        
        // maps each proof of a clause to the transformed subproof of that clause
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
        
        expr_ref_vector m_pinned; // tracking all created expressions
        ptr_vector<proof_set> m_pinned_active_hyps; // tracking all created sets of active hypothesis
        ptr_vector<expr_set> m_pinned_parent_hyps; // tracking all created sets of parent hypothesis

        obj_map<proof, proof*> m_cache; // maps each proof of a clause to the transformed subproof of that clause
        obj_map<expr, proof*> m_units; // maps each unit literal to the subproof of that unit
        obj_map<proof, proof_set*> m_active_hyps; // maps each proof of a clause to the set of proofs of active hypothesis' of the clause
        obj_map<proof, expr_set*> m_parent_hyps; // maps each proof of a clause to the hypothesis-fact, which are transitive parents of that clause, needed to avoid creating cycles in the proof.
        
        void reset();
        void compute_hypsets(proof* pr); // compute active_hyps and parent_hyps for pr
        void collect_units(proof* pr); // compute m_units
        proof* compute_transformed_proof(proof* pf);
        
        proof* mk_lemma_core(proof *pf, expr *fact);
        proof* mk_unit_resolution_core(ptr_buffer<proof>& args);
        proof* mk_step_core(proof* old_step, ptr_buffer<proof>& args);
    };
}
#endif
