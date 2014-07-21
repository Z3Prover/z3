#include "solver.h"
#include "smt_literal.h"
#include "mus.h"
#include "ast_pp.h"

using namespace opt;

// Faster MUS extraction based on Belov et.al. HYB (Algorithm 3, 4)


struct mus::imp {
    solver&                     s;
    ast_manager&                m;
    expr_ref_vector             m_cls2expr;
    obj_map<expr, unsigned>     m_expr2cls;
    vector<smt::literal_vector> m_cls2lits;
    expr_ref_vector             m_vars;
    obj_map<expr, unsigned>     m_var2idx;

public:
    imp(solver& s, ast_manager& m): s(s), m(m), m_cls2expr(m), m_vars(m) {}
    
    unsigned add_var(expr* v) {
        unsigned idx = m_vars.size();
        if (!m_var2idx.find(v, idx)) {
            m_var2idx.insert(v, idx);
            m_vars.push_back(v);
        }
        return idx;
    }
    
    unsigned add_soft(expr* cls, unsigned sz, expr* const* args) {
        TRACE("opt", tout << sz << ": " << mk_pp(cls, m) << "\n";);
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
        return idx;
    }
    
    lbool get_mus(unsigned_vector& mus) {
        TRACE("opt", tout << "\n";);
        solver::scoped_push _sc(s);
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
            IF_VERBOSE(0, display_vec(tout << "core: ", core););
            unsigned cls_id = core.back();
            core.pop_back();
            expr* cls = m_cls2expr[cls_id].get();
            expr_ref not_cls(m);
            not_cls = m.mk_not(cls);
            unsigned sz = assumptions.size();
            assumptions.push_back(not_cls);
            add_core(core, assumptions);
            lbool is_sat = s.check_sat(assumptions.size(), assumptions.c_ptr());
            assumptions.resize(sz);
            switch(is_sat) {
            case l_undef: 
                return is_sat;
            case l_true:
                assumptions.push_back(cls);
                mus.push_back(cls_id);
                extract_model(s, model);
                sz = core.size();
                core.append(mus);
                rmr(core, mus, model);
                core.resize(sz);
                break;
            default:
                core_exprs.reset();
                s.get_unsat_core(core_exprs);
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
            out << mk_pp(v[i], m) << " ";
        }
        out << "\n";
    }

    void extract_model(solver& s, svector<bool>& model) {
        model_ref mdl;
        s.get_model(mdl);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            expr_ref tmp(m);
            mdl->eval(m_vars[i].get(), tmp);
            model[i] = m.is_true(tmp);
        }
    }

    /**
       Recursive model rotation.       
    */
    void rmr(unsigned_vector& M, unsigned_vector& mus, svector<bool>& model) {
        TRACE("opt", 
              display_vec(tout << "M:", M);
              display_vec(tout << "mus:", mus);
              display_vec(tout << "model:", model););

        unsigned cls_id = mus.back();
        smt::literal_vector const& cls = m_cls2lits[cls_id];
        unsigned cls_id_new;
        for (unsigned i = 0; i < cls.size(); ++i) {
            smt::literal lit = cls[i];
            SASSERT(model[lit.var()] == lit.sign()); // literal evaluates to false.
            model[lit.var()] = !model[lit.var()];    // swap assignment
            if (has_single_unsat(model, cls_id_new)) {
                mus.push_back(cls_id_new);
                rmr(M, mus, model);
            }
            model[lit.var()] = !model[lit.var()];    // swap assignment back            
        }
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
        return cls_id != UINT_MAX;
    }

    bool eval(svector<bool> const& model, smt::literal_vector const& cls) const {
        for (unsigned i = 0; i < cls.size(); ++i) {
            if (model[cls[i].var()] != cls[i].sign()) {
                return true;
            }
        }
        return false;
    }

    template<class T>
    void display_vec(std::ostream& out, T const& v) {
        for (unsigned i = 0; i < v.size(); ++i) {
            out << v[i] << " ";
        }
        out << "\n";
    }
};

mus::mus(solver& s, ast_manager& m) {
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

