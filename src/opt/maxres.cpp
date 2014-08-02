/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    maxsres.cpp

Abstract:
   
    MaxRes (weighted) max-sat algorithm by Nina and Bacchus, AAAI 2014.

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:

--*/

#include "solver.h"
#include "maxsmt.h"
#include "maxres.h"
#include "ast_pp.h"
#include "mus.h"

using namespace opt;


class maxres : public maxsmt_solver_base {
    expr_ref_vector  m_B;
    expr_ref_vector  m_asms;    
    obj_map<expr, rational> m_asm2weight;
    ptr_vector<expr> m_new_core;
    mus              m_mus;
    expr_ref_vector  m_trail;

public:
    maxres(ast_manager& m, opt_solver* s, params_ref& p, 
           vector<rational> const& ws, expr_ref_vector const& soft):
        maxsmt_solver_base(s, m, p, ws, soft),
        m_B(m), m_asms(m),
        m_mus(m_s, m),
        m_trail(m)
    {
    }

    virtual ~maxres() {}

    bool is_literal(expr* l) {
        return 
            is_uninterp_const(l) ||
            (m.is_not(l, l) && is_uninterp_const(l));
    }

    void add_soft(expr* e, rational const& w) {
        TRACE("opt", tout << mk_pp(e, m) << "\n";);
        expr_ref asum(m), fml(m);
        app_ref cls(m);
        rational weight(0);
        if (m_asm2weight.find(e, weight)) {
            weight += w;
            m_asm2weight.insert(e, weight);
            return;
        }
        if (is_literal(e)) {
            asum = e;
        }
        else {
            asum = mk_fresh_bool("soft");
            fml = m.mk_iff(asum, e);
            m_s->assert_expr(fml);
        }
        new_assumption(asum, w);
        m_upper += w;
    }

    void new_assumption(expr* e, rational const& w) {
        TRACE("opt", tout << "insert: " << mk_pp(e, m) << " : " << w << "\n";);
        m_asm2weight.insert(e, w);
        m_asms.push_back(e);
        m_trail.push_back(e);        
    }

    lbool operator()() {
        solver::scoped_push _sc(*m_s.get());
        init();
        init_local();
        enable_bvsat();
        while (true) {
            TRACE("opt", 
                  display_vec(tout, m_asms.size(), m_asms.c_ptr());
                  m_s->display(tout);
                  tout << "\n";
                  display(tout);
                  );
            lbool is_sat = m_s->check_sat(m_asms.size(), m_asms.c_ptr());
            if (m_cancel) {
                return l_undef;
            }
            switch (is_sat) {
            case l_true: {
                m_s->get_model(m_model);
                expr_ref tmp(m);
                DEBUG_CODE(
                    for (unsigned i = 0; i < m_asms.size(); ++i) {
                        VERIFY(m_model->eval(m_asms[i].get(), tmp));                        
                        SASSERT(m.is_true(tmp));
                    });
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    VERIFY(m_model->eval(m_soft[i].get(), tmp));
                    m_assignment[i] = m.is_true(tmp);
                }
                m_upper = m_lower;
                return l_true;
            }
            case l_false:
                is_sat = process_unsat();
                if (is_sat != l_true) return is_sat;
                break;
            case l_undef:
                return l_undef;
            default:
                break;
            }
            IF_VERBOSE(1, verbose_stream() << "(opt.max_res [" << m_lower << ":" << m_upper << "])\n";);
        }
        return l_true;
    }

    lbool get_cores(vector<ptr_vector<expr> >& cores) {
        // assume m_s is unsat.
        lbool is_sat = l_false;
        expr_ref_vector asms(m_asms);
        cores.reset();
        ptr_vector<expr> core;
        while (is_sat == l_false) {
            core.reset();
            m_s->get_unsat_core(core);
            is_sat = minimize_core(core);
            if (is_sat != l_true) {
                break;
            }
            cores.push_back(core);
            // TBD: ad hoc to avoid searching for large cores..
            if (core.size() >= 3) {
                break;
            }
            remove_soft(core, asms);
            TRACE("opt",
                  display_vec(tout << "core: ", core.size(), core.c_ptr());
                  display_vec(tout << "assumptions: ", asms.size(), asms.c_ptr()););
            is_sat = m_s->check_sat(asms.size(), asms.c_ptr());            
        }
        TRACE("opt", 
              tout << "num cores: " << cores.size() << "\n";
              for (unsigned i = 0; i < cores.size(); ++i) {
                  for (unsigned j = 0; j < cores[i].size(); ++j) {
                      tout << mk_pp(cores[i][j], m) << " ";
                  }
                  tout << "\n";
              }
              tout << "num satisfying: " << asms.size() << "\n";);
        
        return is_sat;
    }


    lbool process_unsat() {
        vector<ptr_vector<expr> > cores;
        lbool is_sat = get_cores(cores);
        if (is_sat != l_true) {
            return is_sat;
        }
        if (cores.empty()) {
            return l_false;
        }
        for (unsigned i = 0; is_sat == l_true && i < cores.size(); ++i) {
            is_sat = process_unsat(cores[i]);
        }
        return is_sat;
    }
    
    lbool process_unsat(ptr_vector<expr>& core) {
        expr_ref fml(m);
        remove_core(core);
        rational w = split_core(core);
        TRACE("opt", display_vec(tout << "minimized core: ", core.size(), core.c_ptr()););
        max_resolve(core, w);
        fml = m.mk_not(m.mk_and(m_B.size(), m_B.c_ptr()));
        m_s->assert_expr(fml);
        m_lower += w;
        return l_true;
    }

    lbool minimize_core(ptr_vector<expr>& core) {
        if (m_sat_enabled) {
            return l_true;
        }
        m_mus.reset();
        for (unsigned i = 0; i < core.size(); ++i) {
            m_mus.add_soft(core[i]);
        }
        unsigned_vector mus_idx;
        lbool is_sat = m_mus.get_mus(mus_idx);
        if (is_sat != l_true) {
            return is_sat;
        }
        m_new_core.reset();
        for (unsigned i = 0; i < mus_idx.size(); ++i) {
            m_new_core.push_back(core[mus_idx[i]]);
        }
        core.reset();
        core.append(m_new_core);
        return l_true;
    }

    rational get_weight(expr* e) {
        return m_asm2weight.find(e);
    }

    rational split_core(ptr_vector<expr> const& core) {

        // find the minimal weight:
        SASSERT(!core.empty());
        rational w = get_weight(core[0]);
        for (unsigned i = 1; i < core.size(); ++i) {
            rational w2 = get_weight(core[i]);
            if (w2 < w) {
                w = w2;
            }
        }
        // add fresh soft clauses for weights that are above w.
        for (unsigned i = 0; i < core.size(); ++i) {
            rational w2 = get_weight(core[i]);
            if (w2 > w) {
                rational w3 = w2 - w;
                new_assumption(core[i], w3);
            }
        }
        return w;
    }

    void display_vec(std::ostream& out, unsigned sz, expr* const* args) {
        for (unsigned i = 0; i < sz; ++i) {
            out << mk_pp(args[i], m) << " : " << get_weight(args[i]) << " ";
        }
        out << "\n";
    }

    void display(std::ostream& out) {
        for (unsigned i = 0; i < m_asms.size(); ++i) {
            expr* a = m_asms[i].get();
            out << mk_pp(a, m) << " : " << get_weight(a) << "\n";
        }
    }

    void max_resolve(ptr_vector<expr>& core, rational const& w) {
        SASSERT(!core.empty());
        expr_ref fml(m), asum(m);
        app_ref cls(m), d(m);
        m_B.reset();
        m_B.append(core.size(), core.c_ptr());
        d = m.mk_true();
        //
        // d_0 := true
        // d_i := b_{i-1} and d_{i-1}    for i = 1...sz-1
        // soft (b_i or !d_i) 
        //   == (b_i or !(!b_{i-1} or d_{i-1}))
        //   == (b_i or b_0 & b_1 & ... & b_{i-1})
        // 
        // Soft constraint is satisfied if previous soft constraint
        // holds or if it is the first soft constraint to fail.
        // 
        // Soundness of this rule can be established using MaxRes
        // 
        for (unsigned i = 1; i < core.size(); ++i) {
            expr* b_i = m_B[i-1].get();
            expr* b_i1 = m_B[i].get();
            d = m.mk_and(b_i, d);
            asum = mk_fresh_bool("a");
            cls = m.mk_or(b_i1, d);
            fml = m.mk_iff(asum, cls);
            new_assumption(asum, w);
            m_s->assert_expr(fml);
        }
    }

    void remove_soft(ptr_vector<expr> const& core, expr_ref_vector& asms) {
        for (unsigned i = 0; i < asms.size(); ++i) {
            if (core.contains(asms[i].get())) {
                asms[i] = asms.back();
                asms.pop_back();
                --i;
            }
        }
    }

    void remove_core(ptr_vector<expr> const& core) {
        remove_soft(core, m_asms);
    }

    virtual void set_cancel(bool f) {
        maxsmt_solver_base::set_cancel(f);
        m_mus.set_cancel(f);
    }

    void init_local() {
        m_upper.reset();
        m_lower.reset();
        m_trail.reset();
        for (unsigned i = 0; i < m_soft.size(); ++i) {
            add_soft(m_soft[i].get(), m_weights[i]);
        }
    }

};

opt::maxsmt_solver_base* opt::mk_maxres(ast_manager& m, opt_solver* s, params_ref& p, 
                                        vector<rational> const& ws, expr_ref_vector const& soft) {
    return alloc(maxres, m, s, p, ws, soft);
}

