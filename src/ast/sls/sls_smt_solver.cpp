/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_smt_solver.cpp

Abstract:

    A Stochastic Local Search (SLS) Solver.

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-10
    
--*/

#include "ast/sls/sls_context.h"
#include "ast/sls/sat_ddfw.h"
#include "ast/sls/sls_smt_solver.h"
#include "ast/ast_ll_pp.h"


namespace sls {

    class smt_solver::solver_ctx : public sat::local_search_plugin, public sls::sat_solver_context {
        ast_manager& m;
        sat::ddfw& m_ddfw;
        context m_context;
        bool m_dirty = false;
        bool m_new_constraint = false;
        model_ref m_model;
        obj_map<expr, sat::literal> m_expr2lit;
    public:
        solver_ctx(ast_manager& m, sat::ddfw& d) :
            m(m), m_ddfw(d), m_context(m, *this) {
            m_ddfw.set_plugin(this);
            m.limit().push_child(&m_ddfw.rlimit());
        }

        ~solver_ctx() override {
            m.limit().pop_child(&m_ddfw.rlimit());
        }

        void on_rescale() override {}

        void on_restart() override {
            m_context.on_restart();
        }

        bool m_on_save_model = false;
        lbool on_save_model() override {
            lbool r = l_true;
            if (m_on_save_model)
                return r;
            flet<bool> _on_save_model(m_on_save_model, true);
            CTRACE("sls", unsat().empty(), display(tout));
            while (unsat().empty()) {
                r = m_context.check();
                if (!m_new_constraint)
                    break;
                TRACE("sls", display(tout));
                //m_ddfw.simplify();
                m_ddfw.reinit();
                m_new_constraint = false;
            }
            return r;
        }

        void on_model(model_ref& mdl) override {
            m_model = mdl;
        }

        bool is_external(sat::bool_var v) override {
            return m_context.is_external(v);
        }

        void register_atom(sat::bool_var v, expr* e) {
            m_context.register_atom(v, e);
        }

        std::ostream& display(std::ostream& out) override {
            m_ddfw.display(out);
            m_context.display(out);
            return out;
        }

        vector<sat::clause_info> const& clauses() const override { return m_ddfw.clauses(); }
        sat::clause_info const& get_clause(unsigned idx) const override { return m_ddfw.get_clause_info(idx); }
        ptr_iterator<unsigned> get_use_list(sat::literal lit) override { return m_ddfw.use_list(lit); }
        void flip(sat::bool_var v) override { if (m_dirty) m_ddfw.reinit(), m_dirty = false;  m_ddfw.external_flip(v); }
        sat::bool_var external_flip() override { if (m_dirty) m_ddfw.reinit(), m_dirty = false; return m_ddfw.external_flip(); }
        bool try_rotate(sat::bool_var v, sat::bool_var_set& rotated, unsigned& budget) override { if (m_dirty) m_ddfw.reinit(), m_dirty = false; return m_ddfw.try_rotate(v, rotated, budget); }
        double reward(sat::bool_var v) override { return m_ddfw.reward(v); }
        double get_weigth(unsigned clause_idx) override { return m_ddfw.get_clause_info(clause_idx).m_weight; }
        bool is_true(sat::literal lit) override { return m_ddfw.get_value(lit.var()) != lit.sign(); }
        unsigned num_vars() const override { return m_ddfw.num_vars(); }
        indexed_uint_set const& unsat() const override { return m_ddfw.unsat_set(); }
        indexed_uint_set const& unsat_vars() const override { return m_ddfw.unsat_vars(); }
        unsigned num_external_in_unsat_vars() const override { return m_ddfw.num_external_in_unsat_vars(); }
        sat::bool_var add_var() override { m_dirty = true;  return m_ddfw.add_var(); }  
        void add_input_assertion(expr* f) { m_context.add_input_assertion(f); }
        reslimit& rlimit() override { return m_ddfw.rlimit(); }
        void shift_weights() override { m_ddfw.shift_weights(); }

        void force_restart() override { m_ddfw.force_restart(); }

        void add_clause(unsigned n, sat::literal const* lits) override {
            m_ddfw.add(n, lits);
            m_new_constraint = true;
        }

        sat::literal mk_literal() {
            sat::bool_var v = add_var();
            return sat::literal(v, false);
        }

        model_ref get_model() { return m_model; }

        void collect_statistics(statistics& st) {
            m_ddfw.collect_statistics(st);
            m_context.collect_statistics(st);
        }

        void reset_statistics() {
            m_ddfw.reset_statistics();
            m_context.reset_statistics();
        }

        void updt_params(params_ref const& p) {
            m_ddfw.updt_params(p);
            m_context.updt_params(p);
        }
    };

    smt_solver::smt_solver(ast_manager& m, params_ref const& p):
        m(m),
        m_solver_ctx(alloc(solver_ctx, m, m_ddfw)),
        m_assertions(m) {

        m_solver_ctx->updt_params(p);
    }
    
    smt_solver::~smt_solver() {        
    }
    
    void smt_solver::assert_expr(expr* e) {
        if (m.is_and(e)) {
            for (expr* arg : *to_app(e))
                assert_expr(arg);
        }
        else 
            m_assertions.push_back(e);
    }
    
    lbool smt_solver::check() {        
        for (auto f : m_assertions) 
            m_solver_ctx->add_input_assertion(f);        
        IF_VERBOSE(10, m_solver_ctx->display(verbose_stream()));
        return m_ddfw.check(0, nullptr);
    }
    
    model_ref smt_solver::get_model() {
        return m_solver_ctx->get_model();
    }

    std::ostream& smt_solver::display(std::ostream& out) {
        return m_solver_ctx->display(out);
    }

    void smt_solver::collect_statistics(statistics& st) {
        m_solver_ctx->collect_statistics(st);
    }

    void smt_solver::reset_statistics() {
        m_solver_ctx->reset_statistics();
    }
}
