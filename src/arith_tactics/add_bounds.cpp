/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    add_bounds.h

Abstract:

    Strategy for bounding unbounded variables.

Author:

    Leonardo de Moura (leonardo) 2011-06-30.

Revision History:

--*/
#include"add_bounds.h"
#include"arith_decl_plugin.h"
#include"ast_smt2_pp.h"
#include"bound_manager.h"
#include"for_each_expr.h"
#include"assertion_set_util.h"

struct is_unbounded_proc {
    struct found {};
    arith_util      m_util;
    bound_manager & m_bm;
    
    is_unbounded_proc(bound_manager & bm):m_util(bm.m()), m_bm(bm) {}

    void operator()(app * t) {
        if (is_uninterp_const(t) &&  (m_util.is_int(t) || m_util.is_real(t)) && (!m_bm.has_lower(t) || !m_bm.has_upper(t)))
            throw found();
    }
    
    void operator()(var *) {}
    
    void operator()(quantifier*) {}
};

bool is_unbounded(assertion_set const & s) {
    ast_manager & m = s.m();
    bound_manager bm(m);
    bm(s);
    is_unbounded_proc proc(bm);
    return test(s, proc);
}

struct add_bounds::imp {
    ast_manager & m;
    rational      m_lower;
    rational      m_upper;
    volatile bool m_cancel;
    
    imp(ast_manager & _m, params_ref const & p):
        m(_m) {
        updt_params(p);
    }
        
    void updt_params(params_ref const & p) {
        m_lower  = p.get_rat(":add-bound-lower", rational(-2));
        m_upper  = p.get_rat(":add-bound-upper", rational(2));
    }

    void set_cancel(bool f) {
        m_cancel = f;
    }

    struct add_bound_proc {
        arith_util       m_util;
        bound_manager &  m_bm;
        assertion_set &  m_set;
        rational const & m_lower;
        rational const & m_upper;
        unsigned         m_num_bounds;
 
       add_bound_proc(bound_manager & bm, assertion_set & s, rational const & l, rational const & u):
            m_util(bm.m()), 
            m_bm(bm), 
            m_set(s),
            m_lower(l),
            m_upper(u) {
            m_num_bounds = 0;
        }

        void operator()(app * t) {
            if (is_uninterp_const(t) &&  (m_util.is_int(t) || m_util.is_real(t))) {
                if (!m_bm.has_lower(t)) {
                    m_set.assert_expr(m_util.mk_le(t, m_util.mk_numeral(m_upper, m_util.is_int(t))));
                    m_num_bounds++;
                }
                if (!m_bm.has_upper(t)) {
                    m_set.assert_expr(m_util.mk_ge(t, m_util.mk_numeral(m_lower, m_util.is_int(t))));
                    m_num_bounds++;
                }
            }
        }
        
        void operator()(var *) {}
        
        void operator()(quantifier*) {}
    };

    void operator()(assertion_set & s, model_converter_ref & mc) {
        mc = 0;
        if (s.inconsistent())
            return;
        as_st_report report("add-bounds", s);
        bound_manager bm(m);
        expr_fast_mark1 visited;
        add_bound_proc proc(bm, s, m_lower, m_upper);
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++)
            quick_for_each_expr(proc, visited, s.form(i));
        visited.reset();
        report_st_progress(":added-bounds", proc.m_num_bounds);
        TRACE("add_bounds", s.display(tout););
    }
};

add_bounds::add_bounds(ast_manager & m, params_ref const & p):
    m_params(p) {
    m_imp = alloc(imp, m, p);
}

add_bounds::~add_bounds() {
    dealloc(m_imp);
}

void add_bounds::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->updt_params(p);
}

void add_bounds::get_param_descrs(param_descrs & r) {
    r.insert(":add-bound-lower", CPK_NUMERAL, "(default: -2) lower bound to be added to unbounded variables.");
    r.insert(":add-bound-upper", CPK_NUMERAL, "(default: 2) upper bound to be added to unbounded variables.");
}

void add_bounds::operator()(assertion_set & s, model_converter_ref & mc) {
    m_imp->operator()(s, mc);
}

void add_bounds::set_cancel(bool f) {
    if (m_imp)
        m_imp->set_cancel(f);
}
 
void add_bounds::cleanup() {
    ast_manager & m = m_imp->m;
    imp * d = m_imp;
    #pragma omp critical (as_st_cancel)
    {
        d = m_imp;
    }
    dealloc(d);
    d = alloc(imp, m, m_params);
    #pragma omp critical (as_st_cancel) 
    {
        m_imp = d;
    }
}
