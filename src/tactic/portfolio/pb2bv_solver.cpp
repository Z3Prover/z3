/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    pb2bv_solver.cpp

Abstract:


Author:

    Nikolaj Bjorner (nbjorner) 2016-10-23

Notes:
   
--*/

#include "tactic/portfolio/pb2bv_solver.h"
#include "solver/solver_na2as.h"
#include "tactic/tactic.h"
#include "ast/rewriter/pb2bv_rewriter.h"
#include "tactic/filter_model_converter.h"
#include "ast/ast_pp.h"
#include "model/model_smt2_pp.h"

class pb2bv_solver : public solver_na2as {
    ast_manager&     m;
    mutable expr_ref_vector  m_assertions;
    mutable ref<solver>      m_solver;
    mutable pb2bv_rewriter   m_rewriter;

public:

    pb2bv_solver(ast_manager& m, params_ref const& p, solver* s):
        solver_na2as(m),
        m(m),
        m_assertions(m),
        m_solver(s),
        m_rewriter(m, p)
    {
        solver::updt_params(p);
    }

    ~pb2bv_solver() override {}

    solver* translate(ast_manager& m, params_ref const& p) override {
        return alloc(pb2bv_solver, m, p, m_solver->translate(m, p));
    }
    
    void assert_expr(expr * t) override {
        m_assertions.push_back(t);
    }

    void push_core() override {
        flush_assertions();
        m_rewriter.push();
        m_solver->push();
    }

    void pop_core(unsigned n) override {
        m_assertions.reset();
        m_solver->pop(n);
        m_rewriter.pop(n);
    }

    lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) override {
        flush_assertions();
        return m_solver->check_sat(num_assumptions, assumptions);
    }

    void updt_params(params_ref const & p) override { solver::updt_params(p); m_solver->updt_params(p);  }
    void collect_param_descrs(param_descrs & r) override { m_solver->collect_param_descrs(r); }    
    void set_produce_models(bool f) override { m_solver->set_produce_models(f); }
    void set_progress_callback(progress_callback * callback) override { m_solver->set_progress_callback(callback);  }
    void collect_statistics(statistics & st) const override {
        m_rewriter.collect_statistics(st);
        m_solver->collect_statistics(st); 
    }
    void get_unsat_core(ptr_vector<expr> & r) override { m_solver->get_unsat_core(r); }
    void get_model(model_ref & mdl) override {
        m_solver->get_model(mdl);
        if (mdl) {
            filter_model(mdl);            
        }
    } 
    proof * get_proof() override { return m_solver->get_proof(); }
    std::string reason_unknown() const override { return m_solver->reason_unknown(); }
    void set_reason_unknown(char const* msg) override { m_solver->set_reason_unknown(msg); }
    void get_labels(svector<symbol> & r) override { m_solver->get_labels(r); }
    ast_manager& get_manager() const override { return m;  }
    lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) override { return m_solver->find_mutexes(vars, mutexes); }    
    lbool get_consequences_core(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences) override {
        flush_assertions(); 
        return m_solver->get_consequences(asms, vars, consequences); }

    void filter_model(model_ref& mdl) {
        if (m_rewriter.fresh_constants().empty()) {
            return;
        }
        filter_model_converter filter(m);
        func_decl_ref_vector const& fns = m_rewriter.fresh_constants();
        for (unsigned i = 0; i < fns.size(); ++i) {
            filter.insert(fns[i]);
        }
        filter(mdl, 0);
    }

    unsigned get_num_assertions() const override {
        flush_assertions();
        return m_solver->get_num_assertions();
    }

    expr * get_assertion(unsigned idx) const override {
        flush_assertions();
        return m_solver->get_assertion(idx);
    }


private:
    void flush_assertions() const {
        proof_ref proof(m);
        expr_ref fml(m);
        expr_ref_vector fmls(m);
        for (unsigned i = 0; i < m_assertions.size(); ++i) {
            m_rewriter(m_assertions[i].get(), fml, proof);
            m_solver->assert_expr(fml);
        }
        m_rewriter.flush_side_constraints(fmls);
        m_solver->assert_expr(fmls);
        m_assertions.reset();
    }
};

solver * mk_pb2bv_solver(ast_manager & m, params_ref const & p, solver* s) {
    return alloc(pb2bv_solver, m, p, s);
}
