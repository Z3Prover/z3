/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    solver2tactic.cpp

Abstract:

    Convert solver to a tactic.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-17

Notes:
   
--*/

#include "solver/solver.h"
#include "tactic/tactic.h"
#include "tactic/generic_model_converter.h"
#include "solver/solver2tactic.h"
#include "ast/ast_util.h"

typedef obj_map<expr, expr *> expr2expr_map;

void extract_clauses_and_dependencies(goal_ref const& g, expr_ref_vector& clauses, ptr_vector<expr>& assumptions, expr2expr_map& bool2dep, ref<generic_model_converter>& fmc) {
    expr2expr_map dep2bool;
    ptr_vector<expr> deps;
    ast_manager& m = g->m();
    expr_ref_vector clause(m);
    unsigned sz = g->size();
    for (unsigned i = 0; i < sz; i++) {
        expr * f            = g->form(i);
        expr_dependency * d = g->dep(i);
        if (d == nullptr || !g->unsat_core_enabled()) {
            clauses.push_back(f);
        }
        else {
            // create clause (not d1 \/ ... \/ not dn \/ f) when the d's are the assumptions/dependencies of f.
            clause.reset();
            clause.push_back(f);
            deps.reset();
            m.linearize(d, deps);
            SASSERT(!deps.empty()); // d != 0, then deps must not be empty
            ptr_vector<expr>::iterator it  = deps.begin();
            ptr_vector<expr>::iterator end = deps.end();
            for (; it != end; ++it) {
                expr * d = *it;
                if (is_uninterp_const(d) && m.is_bool(d)) {
                    // no need to create a fresh boolean variable for d
                    if (!bool2dep.contains(d)) {
                        assumptions.push_back(d);
                        bool2dep.insert(d, d);
                    }
                    clause.push_back(m.mk_not(d));
                }
                else {
                    // must normalize assumption
                    expr * b = nullptr;
                    if (!dep2bool.find(d, b)) {
                        b = m.mk_fresh_const(nullptr, m.mk_bool_sort());
                        dep2bool.insert(d, b);
                        bool2dep.insert(b, d);
                        assumptions.push_back(b);
                        if (!fmc) {
                            fmc = alloc(generic_model_converter, m, "solver2tactic");
                        }
                        fmc->hide(to_app(b)->get_decl());
                    }
                    clause.push_back(m.mk_not(b));
                }
            }
            SASSERT(clause.size() > 1);
            expr_ref cls(m);
            cls = mk_or(m, clause.size(), clause.c_ptr());
            clauses.push_back(cls);
        }
    }
}

class solver2tactic : public tactic {
    ast_manager& m;
    ref<solver> m_solver;
    params_ref m_params;
    statistics m_st;

public:
    solver2tactic(solver* s):
        m(s->get_manager()),
        m_solver(s)
    {}
    
    void updt_params(params_ref const & p) override {
        m_params.append(p);
        m_solver->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        m_solver->collect_param_descrs(r);
    }

    void operator()(/* in */  goal_ref const & in, 
                    /* out */ goal_ref_buffer & result) override {
        expr_ref_vector clauses(m);
        expr2expr_map               bool2dep;
        ptr_vector<expr>            assumptions;
        ref<generic_model_converter> fmc;
        extract_clauses_and_dependencies(in, clauses, assumptions, bool2dep, fmc);
        ref<solver> local_solver = m_solver->translate(m, m_params);
        local_solver->assert_expr(clauses);
        TRACE("solver2tactic", tout << "clauses asserted\n";);
        lbool r = local_solver->check_sat(assumptions.size(), assumptions.c_ptr()); 
        TRACE("solver2tactic", tout << "check sat result " << r << "\n";);
        proof* pr = local_solver->get_proof();
        if (pr) in->set(proof2proof_converter(m, pr));
        switch (r) {
        case l_true: 
            if (in->models_enabled()) {
                model_ref mdl;
                local_solver->get_model(mdl);
                model_converter_ref mc;
                mc = model2model_converter(mdl.get());
                mc = concat(fmc.get(), mc.get());
                mc = concat(local_solver->mc0(), mc.get());
                in->add(mc.get());
            }
            in->reset();
            result.push_back(in.get());
            break;
        case l_false: {
            in->reset();
            expr_dependency_ref lcore(m);
            if (in->unsat_core_enabled()) {
                expr_ref_vector core(m);
                local_solver->get_unsat_core(core);
                for (expr* c : core) {
                    lcore = m.mk_join(lcore, m.mk_leaf(bool2dep.find(c)));
                }
            }
            in->assert_expr(m.mk_false(), pr, lcore);
            result.push_back(in.get());
            in->set(dependency_converter::unit(lcore));
            break;
        }
        case l_undef:
            if (m.canceled()) {
                throw tactic_exception(Z3_CANCELED_MSG);
            }
            model_converter_ref mc;
            mc = local_solver->get_model_converter();                
            mc = concat(fmc.get(), mc.get());            
            in->reset();
            in->add(mc.get());
            unsigned sz = local_solver->get_num_assertions();
            for (unsigned i = 0; i < sz; ++i) {
                in->assert_expr(local_solver->get_assertion(i));
            }
            result.push_back(in.get());
            break;
        }
        local_solver->collect_statistics(m_st);
    }

    void collect_statistics(statistics & st) const override {
        st.copy(m_st);
    }
    void reset_statistics() override { m_st.reset(); }

    void cleanup() override { }
    void reset() override { cleanup(); }

    void set_logic(symbol const & l) override {}

    void set_progress_callback(progress_callback * callback) override {
        m_solver->set_progress_callback(callback);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(solver2tactic, m_solver->translate(m, m_params));
    }    
};

tactic* mk_solver2tactic(solver* s) { return alloc(solver2tactic, s); }
