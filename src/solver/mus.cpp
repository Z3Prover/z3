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
#include "mus.h"
#include "ast_pp.h"
#include "ast_util.h"
#include "uint_set.h"


struct mus::imp {
    solver&                  m_s;
    ast_manager&             m;
    expr_ref_vector          m_cls2expr;
    obj_map<expr, unsigned>  m_expr2cls;
    model_ref                m_model;
    expr_ref_vector          m_soft;
    vector<rational>         m_weights;
    rational                 m_weight;

    imp(solver& s): 
        m_s(s), m(s.get_manager()), m_cls2expr(m),  m_soft(m)
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
        if (core.size() > 64) {
            return qx(mus);
        }

        expr_ref_vector assumptions(m);
        ptr_vector<expr> core_exprs;
        while (!core.empty()) { 
            IF_VERBOSE(12, verbose_stream() << "(opt.mus reducing core: " << core.size() << " new core: " << mus.size() << ")\n";);
            unsigned cls_id = core.back();
            TRACE("opt", 
                  display_vec(tout << "core:  ", core);
                  display_vec(tout << "mus:   ", mus);
                  );
            core.pop_back();
            expr* cls = m_cls2expr[cls_id].get();
            expr_ref not_cls(m);
            not_cls = mk_not(m, cls);
            lbool is_sat = l_undef;
            {
                scoped_append _sa(*this, assumptions, core);
                assumptions.push_back(not_cls);
                is_sat = m_s.check_sat(assumptions);
            }
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

    class scoped_append {
        expr_ref_vector& m_fmls;
        unsigned         m_size;
    public:
        scoped_append(imp& imp, expr_ref_vector& fmls1, unsigned_vector const& fmls2):
            m_fmls(fmls1),
            m_size(fmls1.size()) {
            for (unsigned i = 0; i < fmls2.size(); ++i) {
                fmls1.push_back(imp.m_cls2expr[fmls2[i]].get());
            }            
        }
        scoped_append(imp& imp, expr_ref_vector& fmls1, uint_set const& fmls2):
            m_fmls(fmls1),
            m_size(fmls1.size()) {
            uint_set::iterator it = fmls2.begin(), end = fmls2.end();
            for (; it != end; ++it) {
                fmls1.push_back(imp.m_cls2expr[*it].get());
            }            
        }
        ~scoped_append() {
            m_fmls.shrink(m_size);
        }
    };

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


    lbool qx(unsigned_vector& mus) {
        uint_set core, support;
        for (unsigned i = 0; i < m_cls2expr.size(); ++i) {
            core.insert(i);
        }
        lbool is_sat = qx(core, support, false);
        if (is_sat == l_true) {
            uint_set::iterator it = core.begin(), end = core.end();
            mus.reset();
            for (; it != end; ++it) {
                mus.push_back(*it);
            }
        }
        return is_sat;
    }

    lbool qx(uint_set& assignment, uint_set& support, bool has_support) {
        lbool is_sat = l_true;
#if 0
        if (s.m_config.m_minimize_core_partial && s.m_stats.m_restart - m_restart > m_max_restarts) {
            IF_VERBOSE(1, verbose_stream() << "(sat restart budget exceeded)\n";);
            return l_true;
        }
#endif
        if (has_support) {
            expr_ref_vector asms(m);
            scoped_append _sa(*this, asms, support);
            is_sat = m_s.check_sat(asms);
            switch (is_sat) {
            case l_false: {
                uint_set core; 
                get_core(core);
                support &= core;
                assignment.reset();
                return l_true;
            }
            case l_undef:
                return l_undef;
            case l_true:
                update_model();
                break;
            default:
                break;
            }
        }
        if (assignment.num_elems() == 1) {
            return l_true;
        }
        uint_set assign2;
        split(assignment, assign2);
        support |= assignment;
        is_sat = qx(assign2, support, !assignment.empty());        
        unsplit(support, assignment);
        if (is_sat != l_true) return is_sat;
        support |= assign2;
        is_sat = qx(assignment, support, !assign2.empty());
        assignment |= assign2;
        unsplit(support, assign2);
        return is_sat;
    }

    void get_core(uint_set& core) {
        ptr_vector<expr> core_exprs;
        m_s.get_unsat_core(core_exprs);
        for (unsigned i = 0; i < core_exprs.size(); ++i) {
            expr* cls = core_exprs[i];
            core.insert(m_expr2cls.find(cls));
        }
    }

    void unsplit(uint_set& A, uint_set& B) {
        uint_set A1, B1;
        uint_set::iterator it = A.begin(), end = A.end();
        for (; it != end; ++it) {
            if (B.contains(*it)) {
                B1.insert(*it);
            }
            else {
                A1.insert(*it);
            }
        }
        A = A1;
        B = B1;
    }

    void split(uint_set& lits1, uint_set& lits2) {
        unsigned half = lits1.num_elems()/2;
        uint_set lits3;
        uint_set::iterator it = lits1.begin(), end = lits1.end();
        for (unsigned i = 0; it != end; ++it, ++i) {
            if (i < half) {
                lits3.insert(*it);
            }
            else {
                lits2.insert(*it);
            }
        }
        lits1 = lits3;
    }

};

mus::mus(solver& s) {
    m_imp = alloc(imp, s);
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
