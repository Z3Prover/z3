/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    proof_converter.h

Abstract:

    Abstract interface for converting proofs, and basic combinators.

Author:

    Leonardo (leonardo) 2011-04-26

Notes:

--*/
#ifndef _PROOF_CONVERTER_H_
#define _PROOF_CONVERTER_H_

#include"ast.h"
#include"converter.h"
#include"ref.h"

class proof_converter : public converter {
public:
    virtual ~proof_converter() { }
    virtual void operator()(ast_manager & m, unsigned num_source, proof * const * source, proof_ref & result) = 0;
    virtual proof_converter * translate(ast_translation & translator) = 0;
};

typedef ref<proof_converter> proof_converter_ref;

proof_converter * concat(proof_converter * pc1, proof_converter * pc2);

/**
   \brief \c pc1 is the proof converter for a sequence of subgoals of size \c num.
   Given an i in [0, num), pc2s[i] is the proof converter for subgoal i,
   and num_subgoals[i] is the number of subgoals of subgoals[i].
*/
proof_converter * concat(proof_converter * pc1, unsigned num, proof_converter * const * pc2s, unsigned * num_subgoals);

proof_converter * proof2proof_converter(ast_manager & m, proof * pr);

typedef sref_vector<proof_converter> proof_converter_ref_vector;
typedef sref_buffer<proof_converter> proof_converter_ref_buffer;

void apply(ast_manager & m, proof_converter_ref & pc1, proof_converter_ref_buffer & pc2s, proof_ref & result);
void apply(ast_manager & m, proof_converter * pc, proof_ref & pr);

#endif
