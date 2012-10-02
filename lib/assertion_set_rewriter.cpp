/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    assertion_set_rewriter.cpp

Abstract:

    Apply rewriting rules in an assertion set.

Author:

    Leonardo (leonardo) 2011-04-27

Notes:

--*/
#include"assertion_set_rewriter.h"
#include"th_rewriter.h"
#include"ast_smt2_pp.h"
#include"assertion_set_util.h"

struct assertion_set_rewriter::imp {
    ast_manager &   m_manager;
    th_rewriter     m_r;
    unsigned        m_num_steps;

    imp(ast_manager & m, params_ref const & p):
        m_manager(m),
        m_r(m, p),
        m_num_steps(0) {
    }

    ast_manager & m() const { return m_manager; }

    void set_cancel(bool f) {
        m_r.set_cancel(f);
    }

    void reset() {
        m_r.reset();
        m_num_steps = 0;
    }

    void operator()(assertion_set & s) {
        SASSERT(is_well_sorted(s));
        as_st_report report("simplifier", s);
        TRACE("before_simplifier", s.display(tout););
        m_num_steps = 0;
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
            m_num_steps += m_r.get_num_steps();
            if (m().proofs_enabled()) {
                proof * pr = s.pr(idx);
                new_pr     = m().mk_modus_ponens(pr, new_pr);
            }
            s.update(idx, new_curr, new_pr);
        }
        TRACE("after_simplifier_bug", s.display(tout););
        s.elim_redundancies();
        TRACE("after_simplifier", s.display(tout););
        SASSERT(is_well_sorted(s));
    }

    unsigned get_num_steps() const { return m_num_steps; }
};

assertion_set_rewriter::assertion_set_rewriter(ast_manager & m, params_ref const & p):
    m_params(p) {
    m_imp = alloc(imp, m, p);
}

assertion_set_rewriter::~assertion_set_rewriter() {
    dealloc(m_imp);
}

void assertion_set_rewriter::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->m_r.updt_params(p);
}

void assertion_set_rewriter::get_param_descrs(param_descrs & r) {
    th_rewriter::get_param_descrs(r);
}

void assertion_set_rewriter::operator()(assertion_set & s) {
    m_imp->operator()(s);
}

void assertion_set_rewriter::set_cancel(bool f) {
    if (m_imp)
        m_imp->set_cancel(f);
}

void assertion_set_rewriter::cleanup() {
    ast_manager & m = m_imp->m();
    imp * d = m_imp;
    #pragma omp critical (as_st_cancel)
    {
        m_imp = 0;
    }
    dealloc(d);
    d = alloc(imp, m, m_params);
    #pragma omp critical (as_st_cancel)
    {
        m_imp = d;
    }
}

unsigned assertion_set_rewriter::get_num_steps() const {
    return m_imp->get_num_steps();
}

