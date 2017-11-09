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
#include "ast/rewriter/th_rewriter.h"
#include "tactic/filter_model_converter.h"
#include "ast/ast_pp.h"
#include "model/model_smt2_pp.h"

class pb2bv_solver : public solver_na2as {
    ast_manager&     m;
    mutable expr_ref_vector  m_assertions;
    mutable ref<solver>      m_solver;
    mutable th_rewriter      m_th_rewriter;
    mutable pb2bv_rewriter   m_rewriter;

public:

    pb2bv_solver(ast_manager& m, params_ref const& p, solver* s):
        solver_na2as(m),
        m(m),
        m_assertions(m),
        m_solver(s),
        m_th_rewriter(m, p),
        m_rewriter(m, p)
    {
        solver::updt_params(p);
    }

    virtual ~pb2bv_solver() {}

    virtual solver* translate(ast_manager& dst_m, params_ref const& p) {
        flush_assertions();
        solver* result = alloc(pb2bv_solver, dst_m, p, m_solver->translate(dst_m, p));
        if (mc0()) {
            ast_translation tr(m, dst_m);
            result->set_model_converter(mc0()->translate(tr));
        }
        return result;
    }
    
    virtual void assert_expr(expr * t) {
        m_assertions.push_back(t);
    }

    virtual void assert_lemma(expr * t) {
        m_solver->assert_lemma(t);
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

    virtual void updt_params(params_ref const & p) { solver::updt_params(p); m_rewriter.updt_params(p); m_solver->updt_params(p);  }
    virtual void collect_param_descrs(param_descrs & r) { m_solver->collect_param_descrs(r); m_rewriter.collect_param_descrs(r);}    
    virtual void set_produce_models(bool f) { m_solver->set_produce_models(f); }
    virtual void set_progress_callback(progress_callback * callback) { m_solver->set_progress_callback(callback);  }
    virtual void collect_statistics(statistics & st) const { 
        m_rewriter.collect_statistics(st);
        m_solver->collect_statistics(st); 
    }
    virtual void get_unsat_core(ptr_vector<expr> & r) { m_solver->get_unsat_core(r); }
    virtual void get_model_core(model_ref & mdl) { 
        m_solver->get_model(mdl);
        if (mdl) {
            filter_model(mdl);            
        }
    } 
    virtual model_converter_ref get_model_converter() const { return m_solver->get_model_converter(); }
    virtual proof * get_proof() { return m_solver->get_proof(); }
    virtual std::string reason_unknown() const { return m_solver->reason_unknown(); }
    virtual void set_reason_unknown(char const* msg) { m_solver->set_reason_unknown(msg); }
    virtual void get_labels(svector<symbol> & r) { m_solver->get_labels(r); }
    virtual ast_manager& get_manager() const { return m;  }
    virtual expr_ref cube() { flush_assertions(); return m_solver->cube(); }
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
        m_rewriter.updt_params(get_params());
        proof_ref proof(m);
        expr_ref fml1(m), fml(m);
        expr_ref_vector fmls(m);
        for (unsigned i = 0; i < m_assertions.size(); ++i) {
            m_th_rewriter(m_assertions[i].get(), fml1, proof);
            m_rewriter(fml1, fml, proof);
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
