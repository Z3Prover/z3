/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bv_elim.h

Abstract:

    Eliminate bit-vectors variables from clauses, by
    replacing them by bound Boolean variables.

Author:

    Nikolaj Bjorner (nbjorner) 2008-12-16.

Revision History:

--*/
#ifndef _BV_ELIM_H_
#define _BV_ELIM_H_

#include "ast.h"
#include "simplifier.h"

class bv_elim {
    ast_manager& m_manager;
public:
    bv_elim(ast_manager& m) : m_manager(m) {};

    void elim(quantifier* q, quantifier_ref& r);
};

class bv_elim_star : public simplifier {
protected:
    bv_elim m_bv_elim;
    virtual bool visit_quantifier(quantifier* q);
    virtual void reduce1_quantifier(quantifier* q);
public:
    bv_elim_star(ast_manager& m) : simplifier(m), m_bv_elim(m) { enable_ac_support(false); }
    virtual ~bv_elim_star() {}
};

#endif /* _BV_ELIM_H_ */

