/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    proof_utils.h

Abstract:
    Utilities to traverse and manipulate proofs

Author:
    Bernhard Gleiss
    Arie Gurfinkel

Revision History:

--*/

#ifndef PROOF_UTILS_H_
#define PROOF_UTILS_H_
#include "ast/ast.h"

/*
 * iterator, which traverses the proof in depth-first post-order.
 */

class proof_post_order {
public:
    proof_post_order(proof* refutation, ast_manager& manager);
    bool hasNext();
    proof* next();

private:
    ptr_vector<proof> m_todo;
    ast_mark          m_visited; // the proof nodes we have already visited
    ast_manager&      m;
};

void reduce_hypotheses(proof_ref &pr);


class proof_utils {
public:
    /**
       \brief reduce the set of hypotheses used in the proof.
     */
    static void reduce_hypotheses(proof_ref& pr);

    /**
       \brief Check that a proof does not contain open hypotheses.
    */
    static bool is_closed(ast_manager& m, proof* p);

    /**
       \brief Permute unit resolution rule with th-lemma
    */
    static void permute_unit_resolution(proof_ref& pr);

    /**
       \brief Push instantiations created in hyper-resolutions up to leaves.
       This produces a "ground" proof where leaves are annotated by instantiations.
    */
    static void push_instantiations_up(proof_ref& pr);


};


#endif
