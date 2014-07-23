/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    mus.cpp

Abstract:
   
    Faster MUS extraction based on Belov et.al. HYB (Algorithm 3, 4)

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:

   Model rotation needs fixes to ensure that hard constraints are satisfied
   under pertubed model. Model rotation also has o be consistent with theories.

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
    vector<smt::literal_vector> m_cls2lits;
    expr_ref_vector             m_vars;
    obj_map<expr, unsigned>     m_var2idx;
    volatile bool               m_cancel;

    imp(ref<solver>& s, ast_manager& m): m_s(s), m(m), m_cls2expr(m), m_vars(m), m_cancel(false) {}

    void reset() {
        m_cls2expr.reset();
        m_expr2cls.reset();
        m_cls2lits.reset();
        m_vars.reset();
        m_var2idx.reset();
        m_vars.push_back(m.mk_true());
    }
        
    void set_cancel(bool f) {
        m_cancel = f;
    }
    
    unsigned add_var(expr* v) {
        unsigned idx = m_vars.size();
        if (!m_var2idx.find(v, idx)) {
            m_var2idx.insert(v, idx);
            m_vars.push_back(v);
        }
        return idx;
    }
    
    unsigned add_soft(expr* cls, unsigned sz, expr* const* args) {
        SASSERT(is_uninterp_const(cls) || m.is_not(cls) && is_uninterp_const(to_app(cls)->get_arg(0)));
        smt::literal_vector lits;
        expr* arg;
        for (unsigned i = 0; i < sz; ++i) {
            if (m.is_not(args[i], arg)) {
                lits.push_back(smt::literal(add_var(arg), true));
            }
            else {
                lits.push_back(smt::literal(add_var(args[i]), false));
            }
        }
        unsigned idx = m_cls2lits.size();
        m_expr2cls.insert(cls, idx);
        m_cls2expr.push_back(cls);
        m_cls2lits.push_back(lits);
        TRACE("opt", 
              tout << idx << ": " << mk_pp(cls, m) << "\n";
              display_vec(tout, lits);
              );
        return idx;
    }

    expr* mk_not(expr* e) {
        if (m.is_not(e, e)) {
            return e;
        }
        return m.mk_not(e);
    }
    
    lbool get_mus(unsigned_vector& mus) {
        TRACE("opt", 
              for (unsigned i = 0; i < m_cls2lits.size(); ++i) {
                  display_vec(tout, m_cls2lits[i]);
              }
              );
        unsigned_vector core;
        for (unsigned i = 0; i < m_cls2expr.size(); ++i) {
            core.push_back(i);
        }
        mus.reset();
        expr_ref_vector assumptions(m);
        svector<bool> model;
        ptr_vector<expr> core_exprs;
        model.resize(m_vars.size());
        while (!core.empty()) {
            IF_VERBOSE(1, verbose_stream() << "(opt.mus reducing core: " << core.size() << " new core: " << mus.size() << ")\n";);
            unsigned cls_id = core.back();
            TRACE("opt", 
                  display_vec(tout << "core:  ", core);
                  display_vec(tout << "mus:   ", mus);
                  display_vec(tout << "model: ", model);
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
            switch(is_sat) {
            case l_undef: 
                return is_sat;
            case l_true:
                assumptions.push_back(cls);
                mus.push_back(cls_id);
                extract_model(model);
                sz = core.size();
                core.append(mus);
                rmr(core, mus, model);
                core.resize(sz);
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

    void extract_model(svector<bool>& model) {
        model_ref mdl;
        m_s->get_model(mdl);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            expr_ref tmp(m);
            mdl->eval(m_vars[i].get(), tmp);
            model[i] = m.is_true(tmp);
        }
        TRACE("opt", 
              display_vec(tout << "model: ", model);
              model_smt2_pp(tout, m, *mdl, 0);              
              );

    }

    /**
       Recursive model rotation.       
    */
    void rmr(unsigned_vector& M, unsigned_vector& mus, svector<bool>& model) {
        TRACE("opt", 
              display_vec(tout << "core:  ", M);
              display_vec(tout << "mus:   ", mus);
              display_vec(tout << "model: ", model););

        unsigned cls_id = mus.back();
        smt::literal_vector const& cls = m_cls2lits[cls_id];
        for (unsigned i = 0; i < cls.size(); ++i) {
            smt::literal lit = cls[i];
            SASSERT(model[lit.var()] == lit.sign()); // literal evaluates to false.
            model[lit.var()] = !model[lit.var()];    // swap assignment
            if (has_single_unsat(model, cls_id) && 
                !mus.contains(cls_id) && 
                model_check(model, cls_id)) {
                mus.push_back(cls_id);
                rmr(M, mus, model);
            }
            model[lit.var()] = !model[lit.var()];    // swap assignment back            
        }
    }

    bool model_check(svector<bool> const& model, unsigned cls_id) {
        // model has to work for hard constraints.
        return false;
    }

    bool has_single_unsat(svector<bool> const& model, unsigned& cls_id) const {
        cls_id = UINT_MAX;
        for (unsigned i = 0; i < m_cls2lits.size(); ++i) {
            if (!eval(model, m_cls2lits[i])) {
                if (cls_id == UINT_MAX) {
                    cls_id = i;
                }
                else {
                    return false;
                }
            }
        }
        TRACE("opt", display_vec(tout << "clause: " << cls_id << " model: ", model););
        return cls_id != UINT_MAX;
    }

    bool eval(svector<bool> const& model, smt::literal_vector const& cls) const {
        bool result = false;
        for (unsigned i = 0; !result && i < cls.size(); ++i) {
            result = (model[cls[i].var()] != cls[i].sign());
        }
        TRACE("opt", display_vec(tout << "model: ", model);
              display_vec(tout << "clause: ", cls);
              tout << "result: " << result << "\n";);
        return result;
    }

};

mus::mus(ref<solver>& s, ast_manager& m) {
    m_imp = alloc(imp, s, m);
}

mus::~mus() {
    dealloc(m_imp);
}

unsigned mus::add_soft(expr* cls, unsigned sz, expr* const* args) {
    return m_imp->add_soft(cls, sz, args);
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
