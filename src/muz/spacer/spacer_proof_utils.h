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
        
        ast_manager &m;
        // tracking all created expressions
        expr_ref_vector m_pinned;
        
        // maps each proof of a clause to the transformed subproof of that clause
        obj_map<proof, proof*> m_cache;
        
        // maps each unit literals to the transformed subproof of that unit
        obj_map<expr, proof*> m_units;
        
        // -- all hypotheses in the the proof
        obj_hashtable<expr> m_hyps;
        
        // marks hypothetical proofs
        ast_mark m_hypmark;
        
        std::vector<expr_set> m_pinned_hyp_sets; // tracking all created sets of hypothesis
        obj_map<expr, expr_set*> m_hyp_anchestor; // maps each proof to the set of hypothesis it contains, needed to avoid creating cycles in the proof.
        
        // stack
        ptr_vector<proof> m_todo;
        
        void reset();
        proof* compute_transformed_proof(proof* pf);

        void compute_hypmarks_and_hyps(proof* pr);
        bool compute_hypmark_from_parents(proof *pr);
        void collect_units(proof* pr);
        
        // returns true if (hypothesis (not a)) would be reduced
        bool is_reduced(expr *a);
        
        proof* mk_lemma_core(proof *pf, expr *fact);
        proof* mk_unit_resolution_core(unsigned num_args, proof* const *args);
    };
}
#endif
