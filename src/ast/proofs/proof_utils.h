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

#ifndef _PROOF_UTILS_H_
#define _PROOF_UTILS_H_
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


#endif
