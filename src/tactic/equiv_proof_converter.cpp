/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    equiv_proof_converter.cpp

Abstract:

    Proof converter that applies equivalence rule to leaves.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-23

Revision History:  

--*/

#include "tactic/equiv_proof_converter.h"
#include "ast/ast_pp.h"
#include "ast/scoped_proof.h"

void equiv_proof_converter::insert(expr* fml1, expr* fml2) {
    if (fml1 != fml2) {
        scoped_proof _sp(m);
        proof_ref p1(m), p2(m), p3(m);
        p1 = m.mk_asserted(fml1);
        p2 = m.mk_rewrite(fml1, fml2);
        p3 = m.mk_modus_ponens(p1, p2);
        TRACE("proof_converter", tout << mk_pp(p3.get(), m) << "\n";);
        SASSERT(m.has_fact(p3));
        m_replace.insert(p3);
    }
}
