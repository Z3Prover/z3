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

#ifndef _EQUIV_PROOF_CONVERTER_H_
#define _EQUIV_PROOF_CONVERTER_H_

#include "replace_proof_converter.h"

class equiv_proof_converter : public proof_converter {
    ast_manager&            m;
    replace_proof_converter m_replace;
public:

    equiv_proof_converter(ast_manager& m): m(m), m_replace(m) {}

    virtual ~equiv_proof_converter() {}

    virtual void operator()(ast_manager & m, unsigned num_source, proof * const * source, proof_ref & result) {
        m_replace(m, num_source, source, result);
    }

    virtual proof_converter * translate(ast_translation & translator) {
        return m_replace.translate(translator);
    }

    void insert(expr* fml1, expr* fml2);

    ast_manager& get_manager() { return m; }

};

#endif
