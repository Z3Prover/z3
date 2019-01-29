/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    enum2bv_solver.cpp

Abstract:

    Finite domain solver.

    Enumeration data-types are translated into bit-vectors, and then 
    the incremental sat-solver is applied to the resulting assertions.    

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-17

Notes:
   
--*/

#include "ast/bv_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/ast_pp.h"
#include "model/model_smt2_pp.h"
#include "tactic/tactic.h"
#include "tactic/generic_model_converter.h"
#include "solver/solver_na2as.h"
#include "ast/rewriter/enum2bv_rewriter.h"
#include "tactic/fd_solver/enum2bv_solver.h"

class enum2bv_solver : public solver_na2as {
    ast_manager&     m;
    ref<solver>      m_solver;
    enum2bv_rewriter m_rewriter;

public:

    enum2bv_solver(ast_manager& m, params_ref const& p, solver* s):
        solver_na2as(m),
        m(m),
        m_solver(s),
        m_rewriter(m, p)
    {
        solver::updt_params(p);
    }

    ~enum2bv_solver() override {}

    solver* translate(ast_manager& dst_m, params_ref const& p) override {   
        solver* result = alloc(enum2bv_solver, dst_m, p, m_solver->translate(dst_m, p));
        model_converter_ref mc = external_model_converter();
        if (mc) {
            ast_translation tr(m, dst_m);
            result->set_model_converter(mc->translate(tr));
        }
        return result;
    }
    
    void assert_expr_core(expr * t) override {
        expr_ref tmp(t, m);
        expr_ref_vector bounds(m);
        proof_ref tmp_proof(m);
        m_rewriter(t, tmp, tmp_proof);
        m_solver->assert_expr(tmp);
        m_rewriter.flush_side_constraints(bounds);
        m_solver->assert_expr(bounds);
    }

    void push_core() override {
        m_rewriter.push();
        m_solver->push();
    }

    void pop_core(unsigned n) override {
        m_solver->pop(n);
        m_rewriter.pop(n);
    }

    lbool check_sat_core2(unsigned num_assumptions, expr * const * assumptions) override {
        m_solver->updt_params(get_params());
        return m_solver->check_sat_core(num_assumptions, assumptions);
    }

    void updt_params(params_ref const & p) override { solver::updt_params(p); m_solver->updt_params(p);  }
    void collect_param_descrs(param_descrs & r) override { m_solver->collect_param_descrs(r); }    
    void set_produce_models(bool f) override { m_solver->set_produce_models(f); }
    void set_progress_callback(progress_callback * callback) override { m_solver->set_progress_callback(callback);  }
    void collect_statistics(statistics & st) const override { m_solver->collect_statistics(st); }
    void get_unsat_core(expr_ref_vector & r) override { m_solver->get_unsat_core(r); }
    void get_model_core(model_ref & mdl) override { 
        m_solver->get_model(mdl);
        if (mdl) {
            model_converter_ref mc = local_model_converter();
            if (mc) (*mc)(mdl);
        }
    } 
    model_converter* local_model_converter() const {
        if (m_rewriter.enum2def().empty() && 
            m_rewriter.enum2bv().empty()) {
            return nullptr;
        }
        generic_model_converter* mc = alloc(generic_model_converter, m, "enum2bv");
        for (auto const& kv : m_rewriter.enum2bv()) 
            mc->hide(kv.m_value);
        for (auto const& kv : m_rewriter.enum2def()) 
            mc->add(kv.m_key, kv.m_value);            
        return mc;
    }

    model_converter* external_model_converter() const {
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
    lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) override { 
        return m_solver->find_mutexes(vars, mutexes); 
    }
    expr_ref_vector cube(expr_ref_vector& vars, unsigned backtrack_level) override { 
        return m_solver->cube(vars, backtrack_level); 
    }
    
    lbool get_consequences_core(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences) override {
        datatype_util dt(m);
        bv_util bv(m);
        expr_ref_vector bvars(m), conseq(m), bounds(m);

        // ensure that enumeration variables that 
        // don't occur in the constraints
        // are also internalized.
        for (expr* v : vars) {
            expr_ref tmp(m.mk_eq(v, v), m);
            proof_ref proof(m);
            m_rewriter(tmp, tmp, proof);            
        }
        m_rewriter.flush_side_constraints(bounds);
        m_solver->assert_expr(bounds);

        // translate enumeration constants to bit-vectors.
        for (expr* v : vars) {
            func_decl* f = nullptr;
            if (is_app(v) && is_uninterp_const(v) && m_rewriter.enum2bv().find(to_app(v)->get_decl(), f)) {
                bvars.push_back(m.mk_const(f));
            }
            else {
                bvars.push_back(v);
            }
        }
        lbool r = m_solver->get_consequences(asms, bvars, consequences);

        // translate bit-vector consequences back to enumeration types
        for (unsigned i = 0; i < consequences.size(); ++i) {
            expr* a = nullptr, *b = nullptr, *u = nullptr, *v = nullptr;
            func_decl* f;
            rational num;
            unsigned bvsize;
            VERIFY(m.is_implies(consequences[i].get(), a, b));
            if (m.is_eq(b, u, v) && is_uninterp_const(u) && m_rewriter.bv2enum().find(to_app(u)->get_decl(), f) && bv.is_numeral(v, num, bvsize)) {
                SASSERT(num.is_unsigned());
                expr_ref head(m);
                ptr_vector<func_decl> const& enums = *dt.get_datatype_constructors(f->get_range());
                if (enums.size() > num.get_unsigned()) {
                    head = m.mk_eq(m.mk_const(f), m.mk_const(enums[num.get_unsigned()]));
                    consequences[i] = m.mk_implies(a, head);
                }
            }
        }
        return r;
    }

    void get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) override {
        m_solver->get_levels(vars, depth);
    }

    expr_ref_vector get_trail() override {
        return m_solver->get_trail();
    }

    unsigned get_num_assertions() const override {
        return m_solver->get_num_assertions();
    }

    expr * get_assertion(unsigned idx) const override {
        return m_solver->get_assertion(idx);
    }

};

solver * mk_enum2bv_solver(ast_manager & m, params_ref const & p, solver* s) {
    return alloc(enum2bv_solver, m, p, s);
}
