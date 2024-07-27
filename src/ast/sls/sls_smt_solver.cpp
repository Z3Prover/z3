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
        bool m_new_clause_added = false;
        model_ref m_model;
    public:
        solver_ctx(ast_manager& m, sat::ddfw& d) :
            m(m), m_ddfw(d), m_context(m, *this) {
            m_ddfw.set_plugin(this);
        }

        ~solver_ctx() override {
        }

        void init_search() override {}

        void finish_search() override {}

        void on_rescale() override {}

        void on_restart() override {}

        void on_save_model() override {
            TRACE("sls", display(tout));
            while (unsat().empty()) {
                m_context.check();
                if (!m_new_clause_added)
                    break;
                TRACE("sls", display(tout));
                m_ddfw.reinit();
                m_new_clause_added = false;
            }
        }

        void on_model(model_ref& mdl) override {
            IF_VERBOSE(1, verbose_stream() << "on-model " << "\n");
            m_model = mdl;
        }

        void register_atom(sat::bool_var v, expr* e) {
            m_context.register_atom(v, e);
        }

        std::ostream& display(std::ostream& out) {
            m_ddfw.display(out);
            m_context.display(out);
            return out;
        }

        vector<sat::clause_info> const& clauses() const override { return m_ddfw.clauses(); }
        sat::clause_info const& get_clause(unsigned idx) const override { return m_ddfw.get_clause_info(idx); }
        ptr_iterator<unsigned> get_use_list(sat::literal lit) override { return m_ddfw.use_list(lit); }
        void flip(sat::bool_var v) override { m_ddfw.flip(v); }
        double reward(sat::bool_var v) override { return m_ddfw.get_reward(v); }
        double get_weigth(unsigned clause_idx) override { return m_ddfw.get_clause_info(clause_idx).m_weight; }
        bool is_true(sat::literal lit) override { return m_ddfw.get_value(lit.var()) != lit.sign(); }
        unsigned num_vars() const override { return m_ddfw.num_vars(); }
        indexed_uint_set const& unsat() const override { return m_ddfw.unsat_set(); }
        sat::bool_var add_var() override { return m_ddfw.add_var(); }
        void add_clause(unsigned n, sat::literal const* lits) override { 
            m_ddfw.add(n, lits);
            m_new_clause_added = true;
        }
        model_ref get_model() { return m_model; }
    };

    smt_solver::smt_solver(ast_manager& m, params_ref const& p):
        m(m),
        m_solver_ctx(alloc(solver_ctx, m, m_ddfw)),
        m_assertions(m) {
        m_ddfw.updt_params(p);
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
        // send clauses to ddfw
        // send expression mapping to m_solver_ctx
        
        for (auto f : m_assertions) 
            add_clause(f);
        
        IF_VERBOSE(10, m_solver_ctx->display(verbose_stream()));
        return m_ddfw.check(0, nullptr);
    }

    void smt_solver::add_clause(expr* f) {
        expr* g, * h;
        sat::literal_vector clause;
        if (m.is_not(f, g) && m.is_not(g, g)) {
            add_clause(g);
        }
        if (m.is_or(f)) {
            clause.reset();
            for (auto arg : *to_app(f))
                clause.push_back(mk_literal(arg));
            m_solver_ctx->add_clause(clause.size(), clause.data());
        }
        else if (m.is_and(f)) {
            for (auto arg : *to_app(f))
                add_clause(arg);
        }
        else if (m.is_not(f, g) && m.is_or(g)) {
            for (auto arg : *to_app(g)) {
                expr_ref fml(m.mk_not(arg), m);;
                add_clause(fml);
            }
        }
        else if (m.is_not(f, g) && m.is_and(g)) {
            clause.reset();
            for (auto arg : *to_app(g))
                clause.push_back(~mk_literal(arg));
            m_solver_ctx->add_clause(clause.size(), clause.data());
        }
        else if (m.is_eq(f, g, h) && m.is_bool(g)) {
            auto lit1 = mk_literal(g);
            auto lit2 = mk_literal(h);
            clause.reset();
            clause.push_back(~lit1);
            clause.push_back(lit2);
            m_solver_ctx->add_clause(clause.size(), clause.data());
            clause.reset();
            clause.push_back(lit1);
            clause.push_back(~lit2);
            m_solver_ctx->add_clause(clause.size(), clause.data());
        }
        else {
            sat::literal lit = mk_literal(f);
            m_solver_ctx->add_clause(1, &lit);
        }
    }

    sat::literal smt_solver::mk_literal(expr* e) {
        sat::literal lit;
        bool neg = false;
        while (m.is_not(e,e))
            neg = !neg;
        if (m_expr2lit.find(e, lit))
            return neg ? ~lit : lit;
        sat::literal_vector clause;
        if (m.is_and(e)) {
            lit = mk_literal();
            for (expr* arg : *to_app(e)) {
                auto lit2 = mk_literal(arg);
                clause.push_back(~lit2);
                sat::literal lits[2] = { ~lit, lit2 };
                m_solver_ctx->add_clause(2, lits);
            }
            clause.push_back(lit);
            m_solver_ctx->add_clause(clause.size(), clause.data());
        }
        else if (m.is_or(e)) {
            lit = mk_literal();
            for (expr* arg : *to_app(e)) {
                auto lit2 = mk_literal(arg);
                clause.push_back(lit2);
                sat::literal lits[2] = { lit, ~lit2 };
                m_solver_ctx->add_clause(2, lits);                
            }
            clause.push_back(~lit);
            m_solver_ctx->add_clause(clause.size(), clause.data());
        }
        else {
            sat::bool_var v = m_num_vars++;
            lit = sat::literal(v, false);
            m_solver_ctx->register_atom(lit.var(), e);
        }
        m_expr2lit.insert(e, lit);
        return neg ? ~lit : lit;
    }

    sat::literal smt_solver::mk_literal() {
        sat::bool_var v = m_num_vars++;
        return sat::literal(v, false);
    }
    
    model_ref smt_solver::get_model() {
        return m_solver_ctx->get_model();
    }

    std::ostream& smt_solver::display(std::ostream& out) {
        return m_solver_ctx->display(out);
    }
}
