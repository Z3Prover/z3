/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    replace_proof_converter.h

Abstract:

    Proof converter to replace asserted leaves by proofs.

    Given a proof P with occurrences of [asserted fml] 
    Replace [asserted fml] by proofs whose conclusions are fml. 

Author:

    Nikolaj Bjorner (nbjorner) 2012-9-16

Revision History:  

--*/

#pragma once

#include "tactic/proof_converter.h"

class replace_proof_converter : public proof_converter {
    ast_manager&    m;
    proof_ref_vector m_proofs;
public:

    replace_proof_converter(ast_manager& _m): m(_m), m_proofs(m) {}

    ~replace_proof_converter() override {}

    proof_ref operator()(ast_manager & _m, unsigned num_source, proof * const * source) override;

    proof_converter * translate(ast_translation & translator) override;

    void insert(proof* p) { m_proofs.push_back(p); }

    ast_manager& get_manager() { return m; }

    // run the replacements the inverse direction.
    void invert() { m_proofs.reverse(); }

    void display(std::ostream & out) override {}

};

