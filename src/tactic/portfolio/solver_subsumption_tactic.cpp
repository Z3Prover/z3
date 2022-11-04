/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    solver_subsumption_tactic.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2021-7-23

--*/
#include "ast/ast_util.h"
#include "tactic/tactical.h"
#include "tactic/portfolio/solver_subsumption_tactic.h"
#include "solver/solver.h"

class solver_subsumption_tactic : public tactic {
    ast_manager& m;
    params_ref    m_params;
    solver_ref    m_solver;

    void push() {
        m_solver->push();
    }

    void pop() {
        m_solver->pop(1);
    }

    void assert_expr(expr* f) {
        m_solver->assert_expr(f);
    }

    bool subsumed(expr* f) {
        expr_ref_vector fmls(m);
        fmls.push_back(m.mk_not(f));
        lbool is_sat = m_solver->check_sat(fmls);
        return (is_sat == l_false);
    }

    /**
    * Check subsumption (a \/ b \/ c)
    *
    * If 
    *   F |= (a \/ ~b \/ c)
    * Then replace (a \/ b \/ c) by (a \/ c)
    * 
    * If
    *   F |= (a \/ b \/ c)
    * Then replace (a \/ b \/ c) by true
    * 
    */

    bool simplify(expr_ref& f) {
        expr_ref_vector fmls(m), ors(m), nors(m), prefix(m);
        expr_ref nf(m.mk_not(f), m);
        fmls.push_back(nf);
        lbool is_sat = m_solver->check_sat(fmls);
        if (is_sat == l_false) {
            f = m.mk_true();
            return true;
        }
        if (!m.is_or(f))
            return false;
        ors.append(to_app(f)->get_num_args(), to_app(f)->get_args());
        for (expr* arg : ors)
            nors.push_back(mk_not(m, arg));
        for (unsigned i = 0; i < ors.size(); ++i) {
            expr* arg = ors.get(i);
            expr_ref save(nors.get(i), m);
            nors[i] = arg;
            is_sat = m_solver->check_sat(nors);
            nors[i] = save;
            if (is_sat == l_false) 
                nors[i] = m.mk_true();
            else 
                prefix.push_back(arg);            
        }
        if (ors.size() != prefix.size()) {
            ors.reset();
            ors.append(prefix.size(), prefix.data());
            f = mk_or(ors);
            return true;
        }
        return false;
    }

    void simplify(vector<std::pair<unsigned, expr_ref>>& fmls, unsigned_vector& change) {

        if (fmls.size() == 0)
            return;

        if (fmls.size() == 1) {
            if (subsumed(fmls[0].second)) {                
                change.push_back(fmls[0].first);
                fmls[0].second = m.mk_true();                
            }
            else if (simplify(fmls[0].second)) 
                change.push_back(fmls[0].first);            
            return;
        }
        unsigned mid = fmls.size() / 2;

        vector<std::pair<unsigned, expr_ref>> pre(mid, fmls.data());
        vector<std::pair<unsigned, expr_ref>> post(fmls.size() - mid, fmls.data() + mid);
        push();
        for (auto const& [p, f] : post)
            assert_expr(f);
        simplify(pre, change);
        pop();
        push();
        for (auto const& [p, f] : pre)
            assert_expr(f);
        simplify(post, change);
        pop();
        if (!change.empty()) {
            fmls.reset();
            fmls.append(pre);
            fmls.append(post);
        }
    }

public:
    solver_subsumption_tactic(ast_manager& m, params_ref const& p) :
        m(m),
        m_params(p) {
    }

    tactic* translate(ast_manager& other_m) override {
        return alloc(solver_subsumption_tactic, other_m, m_params);
    }

    char const* name() const override { return "solver_subsumption"; }

    void updt_params(params_ref const& p) override { 
        m_params.append(p);
        unsigned max_conflicts = m_params.get_uint("max_conflicts", 2);
        m_params.set_uint("sat.max_conflicts", max_conflicts);
        m_params.set_uint("smt.max_conflicts", max_conflicts);
    }

    void collect_param_descrs(param_descrs& r) override { 
        r.insert("max_conflicts", CPK_UINT, "(default: 2) maximal number of conflicts allowed per solver call.");
    }

    void operator()(goal_ref const& g, goal_ref_buffer& result) override {
        TRACE("tactic", tout << "params: " << m_params << "\n"; g->display(tout););
        tactic_report report("subsumption", *g);

        vector<std::pair<unsigned, expr_ref>> fmls;
        unsigned_vector change;
        unsigned sz = g->size();
        if (sz == 1) {
            result.push_back(g.get());
            return;
        }
        for (unsigned i = 0; i < sz; i++)
            fmls.push_back(std::make_pair(i, expr_ref(g->form(i), m)));
        if (!m_solver) {
            scoped_ptr<solver_factory> f = mk_smt_strategic_solver_factory();
            m_solver = (*f)(m, m_params, false, false, true, symbol::null);
        }
        simplify(fmls, change);
        if (change.empty()) {
            result.push_back(g.get());
            return;
        }
        g->inc_depth();
        for (unsigned idx : change)
            g->update(idx, fmls[idx].second);
        g->elim_true();
        result.push_back(g.get());
    }

    void cleanup() override {}
};

tactic* mk_solver_subsumption_tactic(ast_manager& m, params_ref const& p) {
    return alloc(solver_subsumption_tactic, m, p);
}

