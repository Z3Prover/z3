/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mip_tactic.cpp

Abstract:

    Tactic for solvig MIP (mixed integer) problem.
    This is a temporary tactic. It should be deleted
    after theory_arith is upgraded.

Author:

    Leonardo (leonardo) 2012-02-26

Notes:

--*/
#include"tactical.h"
#include"smt_solver_exp.h"

class mip_tactic : public tactic {
    struct imp;
    ast_manager &               m;
    params_ref                  m_params;
    statistics                  m_stats;
    scoped_ptr<smt::solver_exp> m_solver;

    void init_solver() {
        smt::solver_exp * new_solver = alloc(smt::solver_exp, m, m_params);
        #pragma omp critical (tactic_cancel)
        {
            m_solver = new_solver;
        }
    }

public:
    mip_tactic(ast_manager & _m, params_ref const & p):
        m(_m),
        m_params(p) {
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(mip_tactic, m, m_params);
    }

    virtual ~mip_tactic() {}

    virtual void updt_params(params_ref const & p) {
        m_params = p;
    }
    virtual void collect_param_descrs(param_descrs & r) {
    }
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        bool produce_models = g->models_enabled();
        mc = 0; pc = 0; core = 0; result.reset();
        tactic_report report("mip", *g);
        fail_if_proof_generation("mip", g);
        fail_if_unsat_core_generation("mip", g);

        g->elim_redundancies();
        if (g->inconsistent()) {
            result.push_back(g.get());
            return;
        }

        init_solver();
        m_solver->assert_goal(*g);
        
        lbool r;
        try {
            r = m_solver->check();
        }
        catch (strategy_exception & ex) {
            // solver_exp uses assertion_sets and strategy_exception's
            throw tactic_exception(ex.msg());
        }

        m_solver->collect_statistics(m_stats);

        if (r == l_false) {
            g->reset();
            g->assert_expr(m.mk_false());
        }
        else if (r == l_true) {
            g->reset();
            if (produce_models) {
                model_ref md;
                m_solver->get_model(md);
                mc = model2model_converter(md.get());
            }
        }
        else {
            // failed
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("mip", g->display(tout););
        SASSERT(g->is_well_sorted());
    }

    virtual void cleanup() {
        if (m_solver)
            m_solver->collect_statistics(m_stats);
        #pragma omp critical (tactic_cancel)
        {
            m_solver = 0;
        }
    }
    
    virtual void collect_statistics(statistics & st) const {
        st.copy(m_stats);
    }

    virtual void reset_statistics() {
        m_stats.reset();
    }

    virtual void set_cancel(bool f) {
        if (m_solver)
            m_solver->set_cancel(f);
    }
};

tactic * mk_mip_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(mip_tactic, m, p));
}
