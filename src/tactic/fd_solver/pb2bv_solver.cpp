/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    pb2bv_solver.cpp

Abstract:


Author:

    Nikolaj Bjorner (nbjorner) 2016-10-23

Notes:
   
--*/

#include "util/statistics.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/pb2bv_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "model/model_smt2_pp.h"
#include "tactic/tactic.h"
#include "tactic/generic_model_converter.h"
#include "solver/solver_na2as.h"
#include "tactic/fd_solver/pb2bv_solver.h"

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

    ~pb2bv_solver() override {}

    solver* translate(ast_manager& dst_m, params_ref const& p) override {
        flush_assertions();
        solver* result = alloc(pb2bv_solver, dst_m, p, m_solver->translate(dst_m, p));
        model_converter_ref mc = external_model_converter();
        if (mc.get()) {
            ast_translation tr(m, dst_m);
            result->set_model_converter(mc->translate(tr));
        }
        return result;
    }
    
    void assert_expr_core(expr * t) override {
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

    void updt_params(params_ref const & p) override { solver::updt_params(p); m_rewriter.updt_params(p); m_solver->updt_params(p);  }
    void collect_param_descrs(param_descrs & r) override { m_solver->collect_param_descrs(r); m_rewriter.collect_param_descrs(r);}    
    void set_produce_models(bool f) override { m_solver->set_produce_models(f); }
    void set_progress_callback(progress_callback * callback) override { m_solver->set_progress_callback(callback);  }
    void collect_statistics(statistics & st) const override { 
        m_rewriter.collect_statistics(st);
        m_solver->collect_statistics(st); 
    }
    void get_unsat_core(expr_ref_vector & r) override { m_solver->get_unsat_core(r); }
    void get_model_core(model_ref & mdl) override { 
        m_solver->get_model(mdl);
        if (mdl) {
            model_converter_ref mc = local_model_converter();
            if (mc) (*mc)(mdl);
        }
    } 

    model_converter* external_model_converter() const{
        return concat(mc0(), local_model_converter());
    }
    model_converter_ref get_model_converter() const override { 
        model_converter_ref mc = external_model_converter();
        mc = concat(mc.get(), m_solver->get_model_converter().get());
        return mc;
    }
    proof * get_proof() override { return m_solver->get_proof(); }
    std::string reason_unknown() const override { return m_solver->reason_unknown(); }
    void set_reason_unknown(char const* msg) override { m_solver->set_reason_unknown(msg); }
    void get_labels(svector<symbol> & r) override { m_solver->get_labels(r); }
    ast_manager& get_manager() const override { return m;  }
    expr_ref_vector cube(expr_ref_vector& vars, unsigned backtrack_level) override { flush_assertions(); return m_solver->cube(vars, backtrack_level); }
    lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) override { return m_solver->find_mutexes(vars, mutexes); }    
    lbool get_consequences_core(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences) override {
        flush_assertions(); 
        return m_solver->get_consequences(asms, vars, consequences); }

    model_converter* local_model_converter() const {
        if (m_rewriter.fresh_constants().empty()) {
            return nullptr;
        }
        generic_model_converter* filter = alloc(generic_model_converter, m, "pb2bv");
        func_decl_ref_vector const& fns = m_rewriter.fresh_constants();
        for (func_decl* f : fns) {
            filter->hide(f);
        }
        return filter;
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
        if (m_assertions.empty()) return;
        m_rewriter.updt_params(get_params());
        proof_ref proof(m);
        expr_ref fml1(m), fml(m);
        expr_ref_vector fmls(m);
        for (expr* a : m_assertions) {
            m_th_rewriter(a, fml1, proof);
            m_rewriter(false, fml1, fml, proof);
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
