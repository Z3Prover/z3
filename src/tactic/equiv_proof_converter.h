/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    equiv_proof_converter.h

Abstract:

    Proof converter that applies equivalence rule to leaves.

    Given a proof P with occurrences of [asserted fml] 
    replace [asserted fml] by a proof of the form
    [mp [asserted fml'] [~ fml fml']]

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-23

Revision History:  

--*/

#pragma once

#include "tactic/replace_proof_converter.h"

class equiv_proof_converter : public proof_converter {
    ast_manager&            m;
    replace_proof_converter m_replace;
public:

    equiv_proof_converter(ast_manager& m): m(m), m_replace(m) {}

    ~equiv_proof_converter() override {}

    proof_ref operator()(ast_manager & m, unsigned num_source, proof * const * source) override {
        return m_replace(m, num_source, source);
    }

    proof_converter * translate(ast_translation & translator) override {
        return m_replace.translate(translator);
    }

    void insert(expr* fml1, expr* fml2);

    ast_manager& get_manager() { return m; }

    void display(std::ostream & out) override {}
};

