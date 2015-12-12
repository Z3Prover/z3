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
#include "ast_util.h"

using namespace opt;

// 

struct mus::imp {
    solver&                  m_s;
    ast_manager&             m;
    expr_ref_vector          m_cls2expr;
    obj_map<expr, unsigned>  m_expr2cls;
    model_ref                m_model;
    expr_ref_vector          m_soft;
    vector<rational>         m_weights;
    rational                 m_weight;

    imp(solver& s, ast_manager& m): 
        m_s(s), m(m), m_cls2expr(m),  m_soft(m)
    {}

    void reset() {
        m_cls2expr.reset();
        m_expr2cls.reset();
    }
            
    
    unsigned add_soft(expr* cls) {
        SASSERT(is_uninterp_const(cls) || 
                (m.is_not(cls) && is_uninterp_const(to_app(cls)->get_arg(0))));
        unsigned idx = m_cls2expr.size();
        m_expr2cls.insert(cls, idx);
        m_cls2expr.push_back(cls);
        TRACE("opt", tout << idx << ": " << mk_pp(cls, m) << "\n";
        display_vec(tout, m_cls2expr););
        return idx;
    }
    
    lbool get_mus(unsigned_vector& mus) {
        // SASSERT: mus does not have duplicates.
        m_model.reset();
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
            IF_VERBOSE(2, verbose_stream() << "(opt.mus reducing core: " << core.size() << " new core: " << mus.size() << ")\n";);
            unsigned cls_id = core.back();
            TRACE("opt", 
                  display_vec(tout << "core:  ", core);
                  display_vec(tout << "mus:   ", mus);
                  );
            core.pop_back();
            expr* cls = m_cls2expr[cls_id].get();
            expr_ref not_cls(m);
            not_cls = mk_not(m, cls);
            unsigned sz = assumptions.size();
            assumptions.push_back(not_cls);
            add_core(core, assumptions);
            lbool is_sat = m_s.check_sat(assumptions.size(), assumptions.c_ptr());
            assumptions.resize(sz);
            switch (is_sat) {
            case l_undef: 
                return is_sat;
            case l_true:
                assumptions.push_back(cls);
                mus.push_back(cls_id);
                update_model();
                break;
            default:
                core_exprs.reset();
                m_s.get_unsat_core(core_exprs);
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
                    TRACE("opt", display_vec(tout << "core exprs:", core_exprs);
                        display_vec(tout << "core:", core);
                        display_vec(tout << "mus:", mus);
                    );

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
            lbool is_sat = m_s.check_sat(assumptions.size(), assumptions.c_ptr());
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

    void display_vec(std::ostream& out, expr_ref_vector const& v) const {
        for (unsigned i = 0; i < v.size(); ++i)
            out << mk_pp(v[i], m) << " ";
        out << "\n";
    }


    void display_vec(std::ostream& out, ptr_vector<expr> const& v) const {
        for (unsigned i = 0; i < v.size(); ++i)
            out << mk_pp(v[i], m) << " ";
        out << "\n";
    }

    void set_soft(unsigned sz, expr* const* soft, rational const* weights) {
        m_model.reset();
        m_weight.reset();
        m_soft.append(sz, soft);
        m_weights.append(sz, weights);
        for (unsigned i = 0; i < sz; ++i) {
            m_weight += weights[i];
        }
    }

    void update_model() {
        if (m_soft.empty()) return;
        model_ref mdl;
        expr_ref tmp(m);
        m_s.get_model(mdl);
        rational w;
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            mdl->eval(m_soft[i].get(), tmp);
            if (!m.is_true(tmp)) {
                w += m_weights[i];
            }
        }
        if (w < m_weight || !m_model.get()) {
            m_model = mdl;
            m_weight = w;
        }
    }

    rational get_best_model(model_ref& mdl) {
        mdl = m_model;
        return m_weight;
    }


};

mus::mus(solver& s, ast_manager& m) {
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


void mus::reset() {
    m_imp->reset();
}

void mus::set_soft(unsigned sz, expr* const* soft, rational const* weights) {
    m_imp->set_soft(sz, soft, weights);
}

rational mus::get_best_model(model_ref& mdl) {
    return m_imp->get_best_model(mdl);
}
