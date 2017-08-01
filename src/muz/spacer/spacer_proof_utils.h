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


void reduce_hypotheses(proof_ref &pr);
}
#endif
