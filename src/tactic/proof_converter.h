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
#ifndef PROOF_CONVERTER_H_
#define PROOF_CONVERTER_H_

#include "ast/ast.h"
#include "util/ref.h"
#include "tactic/converter.h"
class goal;

class proof_converter : public converter {
public:
    ~proof_converter() override { }
    virtual proof_ref operator()(ast_manager & m, unsigned num_source, proof * const * source) = 0;
    virtual proof_converter * translate(ast_translation & translator) = 0;
};

typedef ref<proof_converter> proof_converter_ref;
typedef sref_vector<proof_converter> proof_converter_ref_vector;
typedef sref_buffer<proof_converter> proof_converter_ref_buffer;


proof_converter * concat(proof_converter * pc1, proof_converter * pc2);

/**
   \brief create a proof converter that takes a set of subgoals and converts their proofs to a proof of 
   the goal they were derived from.
 */
proof_converter * concat(proof_converter *pc1, unsigned n, goal* const* goals);

proof_converter * proof2proof_converter(ast_manager & m, proof * pr);

void apply(ast_manager & m, proof_converter * pc, proof_ref & pr);

proof_ref apply(ast_manager & m, proof_converter_ref & pc1, proof_converter_ref_buffer & pc2s);

#endif
