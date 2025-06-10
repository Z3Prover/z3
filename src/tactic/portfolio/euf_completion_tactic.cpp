/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    euf_completion_tactic.cpp

Abstract:

    Tactic for simplifying with equations.

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/

#include "ast/rewriter/expr_safe_replace.h"
#include "tactic/tactic.h"
#include "tactic/portfolio/euf_completion_tactic.h"
#include "solver/solver.h"
#include "smt/smt_solver.h"

class euf_side_condition_solver : public euf::side_condition_solver {
    ast_manager& m;
    params_ref m_params;
    scoped_ptr<solver> m_solver;
    expr_ref_vector m_deps;
    obj_map<expr, std::pair<proof*, expr_dependency*>> m_e2d;
    expr_ref_vector m_fmls;
    obj_hashtable<expr> m_seen;
    trail_stack m_trail;

    void init_solver() {
        if (m_solver.get())
            return;
        m_params.set_uint("smt.max_conflicts", 100);
        scoped_ptr<solver_factory> f = mk_smt_solver_factory();
        m_solver = (*f)(m, m_params, false, false, true, symbol::null);
    }

public:

    euf_side_condition_solver(ast_manager& m, params_ref const& p) : 
        m(m), m_params(p), m_deps(m), m_fmls(m) {}

    void push() override {
        init_solver();
        m_solver->push();
        m_trail.pop_scope(1);
    }

    void pop(unsigned n) override {
        m_trail.push_scope();
        SASSERT(m_solver.get());
        m_solver->pop(n);
    }

    void add_constraint(expr* f, proof* pr, expr_dependency* d) override {
        if (m_seen.contains(f))
            return;
        m_seen.insert(f);
        m_trail.push(insert_obj_trail(m_seen, f));
        if (!is_ground(f))
            return;
        if (m.is_implies(f))
            return;
        init_solver();
        if (d) {
            expr* e_dep = m.mk_fresh_const("dep", m.mk_bool_sort());
            m_deps.push_back(e_dep);
            m_e2d.insert(e_dep, { pr, d });
            m_trail.push(insert_obj_map(m_e2d, e_dep));
            m_solver->assert_expr(f, e_dep);
        }
        else
            m_solver->assert_expr(f);        
    }

    bool is_true(expr* f, proof_ref& pr, expr_dependency*& d) override {
        d = nullptr;
        solver::scoped_push _sp(*m_solver);
        m_fmls.reset();
        m_fmls.push_back(m.mk_not(f));
        expr_ref nf(m.mk_not(f), m);
        lbool r = m_solver->check_sat(m_fmls);
        if (r == l_false) {
            expr_ref_vector core(m);
            m_solver->get_unsat_core(core);
            for (auto c : core) {
                auto [pr, dep] = m_e2d[c];
                d = m.mk_join(d, dep);
            }
            if (m.proofs_enabled()) {
                pr = m_solver->get_proof();
                SASSERT(pr);
                expr_safe_replace rep(m);
                for (auto c : core) {
                    auto [p, dep] = m_e2d[c];
                    rep.insert(m.mk_asserted(c), p);
                }
                expr_ref ppr(pr, m);
                rep(ppr);
                pr = to_app(ppr.get());
            }
        }

        return r == l_false;
    }

    void solve_for(vector<solution>& sol) override {
        vector<solver::solution> ss;
        for (auto [v, t, g] : sol)
            ss.push_back({ v, t, g });
        sol.reset();
        m_solver->solve_for(ss);
        for (auto [v, t, g] : ss)
            sol.push_back({ v, t, g });
    }
};

dependent_expr_simplifier* mk_euf_completion_simplifier(ast_manager& m, dependent_expr_state& s, params_ref const& p) {
    auto r = alloc(euf::completion, m, s);
    auto scs = alloc(euf_side_condition_solver, m, p);
    r->set_solver(scs);
    return r;
}

tactic * mk_euf_completion_tactic(ast_manager& m, params_ref const& p) {
    return alloc(dependent_expr_state_tactic, m, p,
                 [](auto& m, auto& p, auto &s) -> dependent_expr_simplifier* { return mk_euf_completion_simplifier(m, s, p); });
}
