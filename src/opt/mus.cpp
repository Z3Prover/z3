/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    mus.cpp

Abstract:
   
    MUS extraction.

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:


--*/

#include "solver.h"
#include "smt_literal.h"
#include "mus.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"

using namespace opt;

// 

struct mus::imp {
    ref<solver>&                m_s;
    ast_manager&                m;
    expr_ref_vector             m_cls2expr;
    obj_map<expr, unsigned>     m_expr2cls;
    volatile bool               m_cancel;

    imp(ref<solver>& s, ast_manager& m): 
        m_s(s), m(m), m_cls2expr(m),  m_cancel(false)
    {}

    void reset() {
        m_cls2expr.reset();
        m_expr2cls.reset();
    }
        
    void set_cancel(bool f) {
        m_cancel = f;
    }
    
    
    unsigned add_soft(expr* cls) {
        SASSERT(is_uninterp_const(cls) || m.is_not(cls) && is_uninterp_const(to_app(cls)->get_arg(0)));
        unsigned idx = m_cls2expr.size();
        m_expr2cls.insert(cls, idx);
        m_cls2expr.push_back(cls);
        TRACE("opt", tout << idx << ": " << mk_pp(cls, m) << "\n";);
        return idx;
    }

    expr* mk_not(expr* e) {
        if (m.is_not(e, e)) {
            return e;
        }
        return m.mk_not(e);
    }
    
    lbool get_mus(unsigned_vector& mus) {
        // SASSERT: mus does not have duplicates.
        unsigned_vector core;
        for (unsigned i = 0; i < m_cls2expr.size(); ++i) {
            core.push_back(i);
        }
        if (core.size() == 1) {
            mus.push_back(core.back());
            return l_true;
        }
        mus.reset();
        expr_ref_vector assumptions(m);
        ptr_vector<expr> core_exprs;
        while (!core.empty()) { 
            IF_VERBOSE(1, verbose_stream() << "(opt.mus reducing core: " << core.size() << " new core: " << mus.size() << ")\n";);
            unsigned cls_id = core.back();
            TRACE("opt", 
                  display_vec(tout << "core:  ", core);
                  display_vec(tout << "mus:   ", mus);
                  );
            core.pop_back();
            expr* cls = m_cls2expr[cls_id].get();
            expr_ref not_cls(m);
            not_cls = mk_not(cls);
            unsigned sz = assumptions.size();
            assumptions.push_back(not_cls);
            add_core(core, assumptions);
            lbool is_sat = m_s->check_sat(assumptions.size(), assumptions.c_ptr());
            assumptions.resize(sz);
            switch (is_sat) {
            case l_undef: 
                return is_sat;
            case l_true:
                assumptions.push_back(cls);
                mus.push_back(cls_id);
                break;
            default:
                core_exprs.reset();
                m_s->get_unsat_core(core_exprs);
                if (!core_exprs.contains(not_cls)) {
                    // core := core_exprs \ mus
                    core.reset();
                    for (unsigned i = 0; i < core_exprs.size(); ++i) {
                        cls = core_exprs[i];
                        cls_id = m_expr2cls.find(cls);
                        if (!mus.contains(cls_id)) {
                            core.push_back(cls_id);
                        }
                    }
                }
                break;
            }
        }
#if 0
        DEBUG_CODE(
            assumptions.reset();
            for (unsigned i = 0; i < mus.size(); ++i) {
                assumptions.push_back(m_cls2expr[mus[i]].get());
            }
            lbool is_sat = m_s->check_sat(assumptions.size(), assumptions.c_ptr());
            SASSERT(is_sat == l_false);
                   );
#endif
        return l_true;
    }

    void add_core(unsigned_vector const& core, expr_ref_vector& assumptions) {
        for (unsigned i = 0; i < core.size(); ++i) {
            assumptions.push_back(m_cls2expr[core[i]].get());
        }
    }

    template<class T>
    void display_vec(std::ostream& out, T const& v) const {
        for (unsigned i = 0; i < v.size(); ++i) {
            out << v[i] << " ";
        }
        out << "\n";
    }

};

mus::mus(ref<solver>& s, ast_manager& m) {
    m_imp = alloc(imp, s, m);
}

mus::~mus() {
    dealloc(m_imp);
}

unsigned mus::add_soft(expr* cls) {
    return m_imp->add_soft(cls);
}

lbool mus::get_mus(unsigned_vector& mus) {
    return m_imp->get_mus(mus);
}

void mus::set_cancel(bool f) {
    m_imp->set_cancel(f);
}

void mus::reset() {
    m_imp->reset();
}
