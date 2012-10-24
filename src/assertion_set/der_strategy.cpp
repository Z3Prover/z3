/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    der_strategy.cpp

Abstract:

    DER strategy

Author:

    Leonardo de Moura (leonardo) 2012-10-20

--*/
#include"der_strategy.h"

struct der_strategy::imp {
    ast_manager &   m_manager;
    der_rewriter    m_r;

    imp(ast_manager & m):
        m_manager(m),
        m_r(m) {
    }

    ast_manager & m() const { return m_manager; }

    void set_cancel(bool f) {
        m_r.set_cancel(f);
    }

    void reset() {
        m_r.reset();
    }

    void operator()(assertion_set & s) {
        SASSERT(is_well_sorted(s));
        as_st_report report("der", s);
        TRACE("before_der", s.display(tout););
        if (s.inconsistent())
            return;
        expr_ref   new_curr(m());
        proof_ref  new_pr(m());
        unsigned size = s.size();
        for (unsigned idx = 0; idx < size; idx++) {
            if (s.inconsistent())
                break;
            expr * curr = s.form(idx);
            m_r(curr, new_curr, new_pr);
            if (m().proofs_enabled()) {
                proof * pr = s.pr(idx);
                new_pr     = m().mk_modus_ponens(pr, new_pr);
            }
            s.update(idx, new_curr, new_pr);
        }
        s.elim_redundancies();
        TRACE("after_der", s.display(tout););
        SASSERT(is_well_sorted(s));
    }
};

der_strategy::der_strategy(ast_manager & m) {
    m_imp = alloc(imp, m);
}

der_strategy::~der_strategy() {
    dealloc(m_imp);
}

void der_strategy::operator()(assertion_set & s) {
    m_imp->operator()(s);
}

void der_strategy::set_cancel(bool f) {
    if (m_imp)
        m_imp->set_cancel(f);
}

void der_strategy::cleanup() {
    ast_manager & m = m_imp->m();
    imp * d = m_imp;
    #pragma omp critical (as_st_cancel)
    {
        m_imp = 0;
    }
    dealloc(d);
    d = alloc(imp, m);
    #pragma omp critical (as_st_cancel)
    {
        m_imp = d;
    }
}
