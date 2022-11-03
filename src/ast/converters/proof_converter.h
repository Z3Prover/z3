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
#pragma once

#include "ast/ast.h"
#include "util/ref.h"
#include "ast/converters/converter.h"

class proof_converter : public converter {
public:
    virtual proof_ref operator()(ast_manager & m, unsigned num_source, proof * const * source) = 0;
    virtual proof_converter * translate(ast_translation & translator) = 0;
};

typedef ref<proof_converter> proof_converter_ref;
typedef sref_vector<proof_converter> proof_converter_ref_vector;
typedef sref_buffer<proof_converter> proof_converter_ref_buffer;


proof_converter * concat(proof_converter * pc1, proof_converter * pc2);

proof_converter * proof2proof_converter(ast_manager & m, proof * pr);

void apply(ast_manager & m, proof_converter * pc, proof_ref & pr);

proof_ref apply(ast_manager & m, proof_converter_ref & pc1, proof_converter_ref_buffer & pc2s);

