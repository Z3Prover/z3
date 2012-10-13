/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    proof_utils.h

Abstract:

    Utilities for proofs.

Author:

    Nikolaj Bjorner (nbjorner) 2012-10-12.

Revision History:

--*/
#ifndef _PROOF_UTILS_H_
#define _PROOF_UTILS_H_

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

};

#endif _PROOF_UTILS_H_
