/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    combined_solver.cpp

Abstract:

    Implements the solver API by combining two solvers.

    This is a replacement for the strategic_solver class.

Author:

    Leonardo (leonardo) 2012-12-11

Notes:

--*/
#include"solver.h"
#include"scoped_timer.h"
#include"combined_solver_params.hpp"
#define PS_VB_LVL 15

/**
   \brief Implementation of the solver API that combines two given solvers.

   The combined solver has two modes:
       - non-incremental
       - incremental
   In non-incremental mode, the first solver is used.
   In incremental mode, the second one is used.
   
   A timeout for the second solver can be specified.
   If the timeout is reached, then the first solver is executed.

   The object switches to incremental when:
       - push is used
       - assertions are peformed after a check_sat
       - parameter ignore_solver1==false
*/
class combined_solver : public solver {
public:
    // Behavior when the incremental solver returns unknown.
    enum inc_unknown_behavior {
        IUB_RETURN_UNDEF,      // just return unknown
        IUB_USE_TACTIC_IF_QF,  // invoke tactic if problem is quantifier free
        IUB_USE_TACTIC         // invoke tactic
    };

private:
    bool                 m_inc_mode;
    bool                 m_check_sat_executed;
    bool                 m_use_solver1_results;
    ref<solver>          m_solver1;
    ref<solver>          m_solver2;
    // We delay sending assertions to solver 2
    // This is relevant for big benchmarks that are meant to be solved
    // by a non-incremental solver. 
    bool                 m_solver2_initialized;

    bool                 m_ignore_solver1;
    inc_unknown_behavior m_inc_unknown_behavior;
    unsigned             m_inc_timeout;
    
    void init_solver2_assertions() {
        if (m_solver2_initialized)
            return;
        unsigned sz = m_solver1->get_num_assertions();
        for (unsigned i = 0; i < sz; i++) {
            m_solver2->assert_expr(m_solver1->get_assertion(i));
        }
        m_solver2_initialized = true;
    }

    void switch_inc_mode() {
        m_inc_mode = true;
        init_solver2_assertions();
    }

    struct aux_timeout_eh : public event_handler {
        solver *        m_solver;
        volatile bool   m_canceled;
        aux_timeout_eh(solver * s):m_solver(s), m_canceled(false) {}
        virtual void operator()() {
            m_solver->cancel();
            m_canceled = true;
        }
    };

    void updt_local_params(params_ref const & _p) {
        combined_solver_params p(_p);
        m_inc_timeout    = p.solver2_timeout();
        m_ignore_solver1 = p.ignore_solver1();
        m_inc_unknown_behavior = static_cast<inc_unknown_behavior>(p.solver2_unknown());
    }

    bool has_quantifiers() const {
        unsigned sz = get_num_assertions();
        for (unsigned i = 0; i < sz; i++) {
            if (::has_quantifiers(get_assertion(i)))
                return true;
        }
        return false;
    }

    bool use_solver1_when_undef() const {
        switch (m_inc_unknown_behavior) {
        case IUB_RETURN_UNDEF: return false;
        case IUB_USE_TACTIC_IF_QF: return !has_quantifiers();
        case IUB_USE_TACTIC: return true;
        default:
            UNREACHABLE();
            return false;
        }
    }

public:
    combined_solver(solver * s1, solver * s2, params_ref const & p) {
        m_solver1 = s1;
        m_solver2 = s2;
        updt_local_params(p);
        m_solver2_initialized = false;
        m_inc_mode            = false;
        m_check_sat_executed  = false;
        m_use_solver1_results = true;
    }

    solver* translate(ast_manager& m, params_ref const& p) {
        solver* s1 = m_solver1->translate(m, p);
        solver* s2 = m_solver2->translate(m, p);
        combined_solver* r = alloc(combined_solver, s1, s2, p);
        r->m_solver2_initialized = m_solver2_initialized;
        r->m_inc_mode = m_inc_mode;
        r->m_check_sat_executed = m_check_sat_executed;
        r->m_use_solver1_results = m_use_solver1_results;
        return r;
    }

    virtual void updt_params(params_ref const & p) {
        m_solver1->updt_params(p);
        m_solver2->updt_params(p);
        updt_local_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        m_solver1->collect_param_descrs(r);
        m_solver2->collect_param_descrs(r);
        combined_solver_params::collect_param_descrs(r);
    }
    
    virtual void set_produce_models(bool f) {
        m_solver1->set_produce_models(f);
        m_solver2->set_produce_models(f);
    }
    
    virtual void assert_expr(expr * t) {
        if (m_check_sat_executed)
            switch_inc_mode();
        m_solver1->assert_expr(t);
        if (m_solver2_initialized)
            m_solver2->assert_expr(t);
    }

    virtual void assert_expr(expr * t, expr * a) {
        if (m_check_sat_executed)
            switch_inc_mode();
        m_solver1->assert_expr(t, a);
        init_solver2_assertions();
        m_solver2->assert_expr(t, a);
    }

    virtual void push() {
        switch_inc_mode();
        m_solver1->push();
        m_solver2->push();
    }
    
    virtual void pop(unsigned n) {
        switch_inc_mode();
        m_solver1->pop(n);
        m_solver2->pop(n);
    }

    virtual unsigned get_scope_level() const {
        return m_solver1->get_scope_level();
    }

    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
        m_check_sat_executed  = true;
        
        if (get_num_assumptions() != 0 ||            
            num_assumptions > 0 || // assumptions were provided
            m_ignore_solver1)  {
            // must use incremental solver
            switch_inc_mode();
            m_use_solver1_results = false;
            return m_solver2->check_sat(num_assumptions, assumptions);
        }
        
        if (m_inc_mode) {
            if (m_inc_timeout == UINT_MAX) {
                IF_VERBOSE(PS_VB_LVL, verbose_stream() << "(combined-solver \"using solver 2 (without a timeout)\")\n";);            
                lbool r = m_solver2->check_sat(0, 0);
                if (r != l_undef || !use_solver1_when_undef()) {
                    m_use_solver1_results = false;
                    return r;
                }
            }
            else {
                IF_VERBOSE(PS_VB_LVL, verbose_stream() << "(combined-solver \"using solver 2 (with timeout)\")\n";);            
                aux_timeout_eh eh(m_solver2.get());
                lbool r;
                {
                    scoped_timer timer(m_inc_timeout, &eh);
                    r = m_solver2->check_sat(0, 0);
                }
                if ((r != l_undef || !use_solver1_when_undef()) && !eh.m_canceled) {
                    m_use_solver1_results = false;
                    return r;
                }
            }
            IF_VERBOSE(PS_VB_LVL, verbose_stream() << "(combined-solver \"solver 2 failed, trying solver1\")\n";);                        
        }
        
        IF_VERBOSE(PS_VB_LVL, verbose_stream() << "(combined-solver \"using solver 1\")\n";);
        m_use_solver1_results = true;
        return m_solver1->check_sat(0, 0);
    }

    virtual void set_cancel(bool f) {
        if (f) {
            m_solver1->cancel();
            m_solver2->cancel();
        }
        else {
            m_solver1->reset_cancel();
            m_solver2->reset_cancel();
        }
    }
    
    virtual void set_progress_callback(progress_callback * callback) {
        m_solver1->set_progress_callback(callback);
        m_solver2->set_progress_callback(callback);
    }
    
    virtual unsigned get_num_assertions() const {
        return m_solver1->get_num_assertions();
    }

    virtual expr * get_assertion(unsigned idx) const {
        return m_solver1->get_assertion(idx);
    }

    virtual unsigned get_num_assumptions() const {
        return m_solver1->get_num_assumptions() + m_solver2->get_num_assumptions();
    }

    virtual expr * get_assumption(unsigned idx) const {
        unsigned c1 = m_solver1->get_num_assumptions();
        if (idx < c1) return m_solver1->get_assumption(idx);
        return m_solver2->get_assumption(idx - c1);
    }

    virtual void display(std::ostream & out) const {
        m_solver1->display(out);
    }

    virtual void collect_statistics(statistics & st) const {
        if (m_use_solver1_results)
            m_solver1->collect_statistics(st);
        else
            m_solver2->collect_statistics(st);
    }

    virtual void get_unsat_core(ptr_vector<expr> & r) {
        if (m_use_solver1_results)
            m_solver1->get_unsat_core(r);
        else
            m_solver2->get_unsat_core(r);
    }

    virtual void get_model(model_ref & m) {
        if (m_use_solver1_results)
            m_solver1->get_model(m);
        else
            m_solver2->get_model(m);
    }

    virtual proof * get_proof() {
        if (m_use_solver1_results)
            return m_solver1->get_proof();
        else
            return m_solver2->get_proof();
    }

    virtual std::string reason_unknown() const {
        if (m_use_solver1_results)
            return m_solver1->reason_unknown();
        else
            return m_solver2->reason_unknown();
    }

    virtual void get_labels(svector<symbol> & r) {
        if (m_use_solver1_results)
            return m_solver1->get_labels(r);
        else
            return m_solver2->get_labels(r);
    }

};


solver * mk_combined_solver(solver * s1, solver * s2, params_ref const & p) {
    return alloc(combined_solver, s1, s2, p);
}

class combined_solver_factory : public solver_factory {
    scoped_ptr<solver_factory> m_f1;
    scoped_ptr<solver_factory> m_f2;
public:
    combined_solver_factory(solver_factory * f1, solver_factory * f2):m_f1(f1), m_f2(f2) {}
    virtual ~combined_solver_factory() {}

    virtual solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) {
        return mk_combined_solver((*m_f1)(m, p, proofs_enabled, models_enabled, unsat_core_enabled, logic),
                                  (*m_f2)(m, p, proofs_enabled, models_enabled, unsat_core_enabled, logic),
                                  p);
    }
};

solver_factory * mk_combined_solver_factory(solver_factory * f1, solver_factory * f2) {
    return alloc(combined_solver_factory, f1, f2);
}
