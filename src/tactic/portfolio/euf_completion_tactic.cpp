/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    euf_completion_tactic.cpp

Abstract:

    Tactic for simplifying with equations.

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/

#include "tactic/tactic.h"
#include "tactic/portfolio/euf_completion_tactic.h"
#include "solver/solver.h"

class euf_side_condition_solver : public euf::side_condition_solver {
    ast_manager& m;
    params_ref m_params;
    scoped_ptr<solver> m_solver;
    expr_ref_vector m_deps;
    obj_map<expr, expr_dependency*> m_e2d;
    void init_solver() {
        if (m_solver.get())
            return;
        m_params.set_uint("smt.max_conflicts", 100);
        scoped_ptr<solver_factory> f = mk_smt_strategic_solver_factory();
        m_solver = (*f)(m, m_params, false, false, true, symbol::null);
    }
public:
    euf_side_condition_solver(ast_manager& m, params_ref const& p) : m(m), m_params(p), m_deps(m) {}

    void add_constraint(expr* f, expr_dependency* d) override {
        if (!is_ground(f))
            return;
        init_solver();
        expr* e_dep = nullptr;
        if (d) {
            e_dep = m.mk_fresh_const("dep", m.mk_bool_sort());
            m_deps.push_back(e_dep);
            m_e2d.insert(e_dep, d);
        }
        m_solver->assert_expr(f, e_dep);
    }

    bool is_true(expr* f, expr_dependency*& d) override {
        d = nullptr;
        m_solver->push();
        expr_ref_vector fmls(m);
        fmls.push_back(m.mk_not(f));
        expr_ref nf(m.mk_not(f), m);
        lbool r = m_solver->check_sat(fmls);
        if (r == l_false) {
            expr_ref_vector core(m);
            m_solver->get_unsat_core(core);
            for (auto c : core)
                d = m.mk_join(d, m_e2d[c]);
        }
        m_solver->pop(1);
        return r == l_false;
    }
};

static euf::completion* mk_completion(ast_manager& m, dependent_expr_state& s, params_ref const& p) {
    auto r = alloc(euf::completion, m, s);
    auto scs = alloc(euf_side_condition_solver, m, p);
    r->set_solver(scs);
    return r;
}

tactic * mk_euf_completion_tactic(ast_manager& m, params_ref const& p) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return mk_completion(m, s, p); });
}
