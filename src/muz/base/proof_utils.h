/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    proof_utils.h

Abstract:

    Utilities for transforming proofs.

Author:

    Nikolaj Bjorner (nbjorner) 2012-10-12.

Revision History:

--*/
#ifndef PROOF_UTILS_H_
#define PROOF_UTILS_H_

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
