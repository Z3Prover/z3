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

#include "solver/solver_na2as.h"
#include "tactic/tactic.h"
#include "ast/bv_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/rewriter/enum2bv_rewriter.h"
#include "tactic/extension_model_converter.h"
#include "tactic/filter_model_converter.h"
#include "ast/ast_pp.h"
#include "model/model_smt2_pp.h"
#include "tactic/portfolio/enum2bv_solver.h"

class enum2bv_solver : public solver_na2as {
    ast_manager&   m;
    ref<solver>    m_solver;
    enum2bv_rewriter    m_rewriter;

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

    solver* translate(ast_manager& m, params_ref const& p) override {
        return alloc(enum2bv_solver, m, p, m_solver->translate(m, p));
    }
    
    void assert_expr(expr * t) override {
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

    lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) override {
        return m_solver->check_sat(num_assumptions, assumptions);
    }

    void updt_params(params_ref const & p) override { solver::updt_params(p); m_solver->updt_params(p);  }
    void collect_param_descrs(param_descrs & r) override { m_solver->collect_param_descrs(r); }    
    void set_produce_models(bool f) override { m_solver->set_produce_models(f); }
    void set_progress_callback(progress_callback * callback) override { m_solver->set_progress_callback(callback);  }
    void collect_statistics(statistics & st) const override { m_solver->collect_statistics(st); }
    void get_unsat_core(ptr_vector<expr> & r) override { m_solver->get_unsat_core(r); }
    void get_model(model_ref & mdl) override {
        m_solver->get_model(mdl);
        if (mdl) {
            extend_model(mdl);
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
        datatype_util dt(m);
        bv_util bv(m);
        expr_ref_vector bvars(m), conseq(m), bounds(m);

        // ensure that enumeration variables that 
        // don't occur in the constraints
        // are also internalized.
        for (unsigned i = 0; i < vars.size(); ++i) {
            expr_ref tmp(m.mk_eq(vars[i], vars[i]), m);
            proof_ref proof(m);
            m_rewriter(tmp, tmp, proof);            
        }
        m_rewriter.flush_side_constraints(bounds);
        m_solver->assert_expr(bounds);

        // translate enumeration constants to bit-vectors.
        for (unsigned i = 0; i < vars.size(); ++i) {
            func_decl* f = nullptr;
            if (is_app(vars[i]) && is_uninterp_const(vars[i]) && m_rewriter.enum2bv().find(to_app(vars[i])->get_decl(), f)) {
                bvars.push_back(m.mk_const(f));
            }
            else {
                bvars.push_back(vars[i]);
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

    void filter_model(model_ref& mdl) {
        filter_model_converter filter(m);
        obj_map<func_decl, func_decl*>::iterator it = m_rewriter.enum2bv().begin(), end = m_rewriter.enum2bv().end();
        for (; it != end; ++it) {
            filter.insert(it->m_value);
        }
        filter(mdl, 0);
    }

    void extend_model(model_ref& mdl) {
        extension_model_converter ext(m);
        obj_map<func_decl, expr*>::iterator it = m_rewriter.enum2def().begin(), end = m_rewriter.enum2def().end();
        for (; it != end; ++it) {
            ext.insert(it->m_key, it->m_value);
            
        }
        ext(mdl, 0);
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
