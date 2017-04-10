/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    pb2bv_solver.cpp

Abstract:


Author:

    Nikolaj Bjorner (nbjorner) 2016-10-23

Notes:
   
--*/

#include "pb2bv_solver.h"
#include "solver_na2as.h"
#include "tactic.h"
#include "pb2bv_rewriter.h"
#include "filter_model_converter.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"

class pb2bv_solver : public solver_na2as {
    ast_manager&     m;
    params_ref       m_params;
    mutable expr_ref_vector  m_assertions;
    mutable ref<solver>      m_solver;
    mutable pb2bv_rewriter   m_rewriter;

public:

    pb2bv_solver(ast_manager& m, params_ref const& p, solver* s):
        solver_na2as(m),
        m(m),
        m_params(p),
        m_assertions(m),
        m_solver(s),
        m_rewriter(m, p)
    {
    }

    virtual ~pb2bv_solver() {}

    virtual solver* translate(ast_manager& m, params_ref const& p) {
        return alloc(pb2bv_solver, m, p, m_solver->translate(m, p));
    }
    
    virtual void assert_expr(expr * t) {
        m_assertions.push_back(t);
    }

    virtual void push_core() {
        flush_assertions();
        m_rewriter.push();
        m_solver->push();
    }

    virtual void pop_core(unsigned n) {
        m_assertions.reset();
        m_solver->pop(n);
        m_rewriter.pop(n);
    }

    virtual lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) {
        flush_assertions();
        return m_solver->check_sat(num_assumptions, assumptions);
    }

    virtual void updt_params(params_ref const & p) { m_solver->updt_params(p);  }
    virtual void collect_param_descrs(param_descrs & r) { m_solver->collect_param_descrs(r); }    
    virtual void set_produce_models(bool f) { m_solver->set_produce_models(f); }
    virtual void set_progress_callback(progress_callback * callback) { m_solver->set_progress_callback(callback);  }
    virtual void collect_statistics(statistics & st) const { 
        m_rewriter.collect_statistics(st);
        m_solver->collect_statistics(st); 
    }
    virtual void get_unsat_core(ptr_vector<expr> & r) { m_solver->get_unsat_core(r); }
    virtual void get_model(model_ref & mdl) { 
        m_solver->get_model(mdl);
        if (mdl) {
            filter_model(mdl);            
        }
    } 
    virtual proof * get_proof() { return m_solver->get_proof(); }
    virtual std::string reason_unknown() const { return m_solver->reason_unknown(); }
    virtual void set_reason_unknown(char const* msg) { m_solver->set_reason_unknown(msg); }
    virtual void get_labels(svector<symbol> & r) { m_solver->get_labels(r); }
    virtual ast_manager& get_manager() const { return m;  }
    virtual lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) { return m_solver->find_mutexes(vars, mutexes); }    
    virtual lbool get_consequences_core(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences) {
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

    virtual unsigned get_num_assertions() const {
        flush_assertions();
        return m_solver->get_num_assertions();
    }

    virtual expr * get_assertion(unsigned idx) const {
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
