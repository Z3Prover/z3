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

#include "solver/solver.h"
#include "solver/mus.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "model/model_evaluator.h"


struct mus::imp {

    typedef obj_hashtable<expr> expr_set;

    solver&                  m_solver;
    ast_manager&             m;
    expr_ref_vector          m_lit2expr;
    expr_ref_vector          m_assumptions;
    obj_map<expr, unsigned>  m_expr2lit;
    model_ref                m_model;
    expr_ref_vector          m_soft;
    vector<rational>         m_weights;
    rational                 m_weight;

    imp(solver& s): 
        m_solver(s), m(s.get_manager()), m_lit2expr(m),  m_assumptions(m), m_soft(m)
    {}

    void reset() {
        m_lit2expr.reset();
        m_expr2lit.reset();
        m_assumptions.reset();
    }

    bool is_literal(expr* lit) const {
        expr* l;
        return is_uninterp_const(lit) || (m.is_not(lit, l) && is_uninterp_const(l));
    }
    
    unsigned add_soft(expr* lit) {
        SASSERT(is_literal(lit));
        unsigned idx = m_lit2expr.size();
        m_expr2lit.insert(lit, idx);
        m_lit2expr.push_back(lit);
        TRACE("mus", tout << idx << ": " << mk_pp(lit, m) << "\n" << m_lit2expr << "\n";);
        return idx;
    }

    void add_assumption(expr* lit) {
        SASSERT(is_literal(lit));
        m_assumptions.push_back(lit);
    }

    lbool get_mus(expr_ref_vector& mus) {
        m_model.reset();
        mus.reset();
        if (m_lit2expr.size() == 1) {
            mus.push_back(m_lit2expr.back());
            return l_true;
        }
        return get_mus1(mus);
    }

    lbool get_mus(ptr_vector<expr>& mus) {
        mus.reset();
        expr_ref_vector result(m);
        lbool r = get_mus(result);
        mus.append(result.size(), result.c_ptr());
        return r;
    }    

    lbool get_mus1(expr_ref_vector& mus) {
        ptr_vector<expr> unknown(m_lit2expr.size(), m_lit2expr.c_ptr());
        ptr_vector<expr> core_exprs;
        TRACE("mus", m_solver.display(tout););
        while (!unknown.empty()) { 
            IF_VERBOSE(12, verbose_stream() << "(mus reducing core: " << unknown.size() << " new core: " << mus.size() << ")\n";);
            TRACE("mus", display_vec(tout << "core:  ", unknown); display_vec(tout << "mus:   ", mus););
            expr* lit = unknown.back();
            unknown.pop_back();
            expr_ref not_lit(mk_not(m, lit), m);
            lbool is_sat = l_undef;
            {
                scoped_append _sa1(*this, mus, unknown);
                scoped_append _sa2(*this, mus, m_assumptions);
                mus.push_back(not_lit);
                is_sat = m_solver.check_sat(mus);
            }
            switch (is_sat) {
            case l_undef: 
                return is_sat;
            case l_true:
                mus.push_back(lit);
                update_model();
                break;
            default:
                core_exprs.reset();
                m_solver.get_unsat_core(core_exprs);
                if (!core_exprs.contains(not_lit)) {
                    // unknown := core_exprs \ mus
                    unknown.reset();
                    for (unsigned i = 0; i < core_exprs.size(); ++i) {
                        if (!mus.contains(core_exprs[i])) {
                            unknown.push_back(core_exprs[i]);
                        }
                    }
                    TRACE("mus", display_vec(tout << "core exprs:", core_exprs);
                        display_vec(tout << "core:", unknown);
                        display_vec(tout << "mus:", mus);
                    );

                }
                break;
            }
        }
        // SASSERT(is_core(mus));
        return l_true;
    }

    // use correction sets
    lbool get_mus2(expr_ref_vector& mus) {
        expr* lit = nullptr;
        lbool is_sat;
        ptr_vector<expr> unknown(m_lit2expr.size(), m_lit2expr.c_ptr());
        while (!unknown.empty()) { 
            IF_VERBOSE(12, verbose_stream() << "(mus reducing core: " << unknown.size() << " new core: " << mus.size() << ")\n";);
            {
                scoped_append _sa1(*this, mus, m_assumptions);
                is_sat = get_next_mcs(mus, unknown, lit);
            }
            if (l_false == is_sat) {
                mus.push_back(lit);
            }
            else {
                return is_sat;
            }
        }        
        
        //SASSERT(is_core(mus));
        return l_true;
    }

    // find the next literal to be a member of a core.
    lbool get_next_mcs(expr_ref_vector& mus, ptr_vector<expr>& unknown, expr*& core_literal) {
        ptr_vector<expr> mss;
        expr_ref_vector  nmcs(m);
        expr_set core, min_core, nmcs_set;
        bool min_core_valid = false;
        expr* min_lit = nullptr;
        while (!unknown.empty()) {
            expr* lit = unknown.back();
            unknown.pop_back();
            model_ref mdl;
            scoped_append assume_mss(*this,  mus, mss);      // current satisfied literals
            scoped_append assume_nmcs(*this, mus, nmcs);     // current non-satisfied literals
            scoped_append assume_lit(*this,  mus, lit);      // current unknown literal
            switch (m_solver.check_sat(mus)) {
            case l_true: {
                TRACE("mus", tout << "literal can be satisfied: " << mk_pp(lit, m) << "\n";);
                mss.push_back(lit);
                m_solver.get_model(mdl);
                model_evaluator eval(*mdl.get());
                for (unsigned i = 0; i < unknown.size(); ) {
                    expr_ref tmp(m);
                    eval(unknown[i], tmp);
                    if (m.is_true(tmp)) {
                        mss.push_back(unknown[i]);
                        unknown[i] = unknown.back();
                        unknown.pop_back();
                    }
                    else {
                        ++i;
                    }
                }
                break;
            }
            case l_false:
                TRACE("mus", tout << "literal is in a core: " << mk_pp(lit, m) << "\n";);
                nmcs.push_back(mk_not(m, lit));
                nmcs_set.insert(nmcs.back());
                get_core(core);
                if (!core.contains(lit)) {
                    // The current mus is already a core.
                    unknown.reset();
                    return l_true;
                }
                if (have_intersection(nmcs_set, core)) {
                    // can't use this core directly. Hypothetically, we 
                    // could try to combine min_core with core and
                    // see if the combination produces a better minimal core.
                    SASSERT(min_core_valid);
                    break;
                }
                if (!min_core_valid || core.size() < min_core.size()) {
                    // The current core is smallest so far, so we get fewer unknowns from it.
                    min_core = core;
                    min_core_valid = true;
                    min_lit = lit;
                }
                break;
            case l_undef:
                return l_undef;
            }
        }
        SASSERT(min_core_valid);
        if (!min_core_valid) {
            // all unknown soft constraints were satisfiable
            return l_true;
        }

        expr_set mss_set;
        for (unsigned i = 0; i < mss.size(); ++i) {
            mss_set.insert(mss[i]);
        }
        expr_set::iterator it = min_core.begin(), end = min_core.end();
        for (; it != end; ++it) {
            if (mss_set.contains(*it) && min_lit != *it) {
                unknown.push_back(*it);
            }
        }
        core_literal = min_lit;
        
        return l_false;
    }

    void get_core(expr_set& core) {
        core.reset();
        ptr_vector<expr> core_exprs;
        m_solver.get_unsat_core(core_exprs);
        for (unsigned i = 0; i < core_exprs.size(); ++i) {
            if (m_expr2lit.contains(core_exprs[i])) {
                core.insert(core_exprs[i]);
            }
        }
    }

    bool have_intersection(expr_set const& A, expr_set const& B) {
        if (A.size() < B.size()) {
            expr_set::iterator it = A.begin(), end = A.end();
            for (; it != end; ++it) {
                if (B.contains(*it)) return true;
            }
        }
        else {
            expr_set::iterator it = B.begin(), end = B.end();
            for (; it != end; ++it) {
                if (A.contains(*it)) return true;
            }
        }
        return false;
    }

    bool is_core(expr_ref_vector const& mus) {
        return l_false == m_solver.check_sat(mus); 
    }

    class scoped_append {
        expr_ref_vector& m_fmls;
        unsigned         m_size;
    public:
        scoped_append(imp& imp, expr_ref_vector& fmls1, expr_set const& fmls2):
            m_fmls(fmls1),
            m_size(fmls1.size()) {
            expr_set::iterator it = fmls2.begin(), end = fmls2.end();
            for (; it != end; ++it) {
                fmls1.push_back(*it);
            }            
        }
        scoped_append(imp& imp, expr_ref_vector& fmls1, expr_ref_vector const& fmls2):
            m_fmls(fmls1),
            m_size(fmls1.size()) {
            fmls1.append(fmls2);
        }
        scoped_append(imp& imp, expr_ref_vector& fmls1, ptr_vector<expr> const& fmls2):
            m_fmls(fmls1),
            m_size(fmls1.size()) {
            fmls1.append(fmls2.size(), fmls2.c_ptr());
        }
        scoped_append(imp& imp, expr_ref_vector& fmls1, expr* fml):
            m_fmls(fmls1),
            m_size(fmls1.size()) {
            fmls1.push_back(fml);
        }
        ~scoped_append() {
            m_fmls.shrink(m_size);
        }
    };

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
        m_solver.get_model(mdl);
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

mus::mus(solver& s) {
    m_imp = alloc(imp, s);
}

mus::~mus() {
    dealloc(m_imp);
}

unsigned mus::add_soft(expr* lit) {
    return m_imp->add_soft(lit);
}

void mus::add_assumption(expr* lit) {
    return m_imp->add_assumption(lit);
}

lbool mus::get_mus(ptr_vector<expr>& mus) {
    return m_imp->get_mus(mus);
}

lbool mus::get_mus(expr_ref_vector& mus) {
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
