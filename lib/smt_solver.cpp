/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_solver.h

Abstract:

    New frontend for the incremental solver.
    
Author:

    Leonardo de Moura (leonardo) 2012-02-09.

Revision History:

--*/
#include"smt_solver.h"
#include"smt_context.h" 
#include"ast_smt2_pp.h"
#include"params2front_end_params.h"

namespace smt {

    struct solver::imp {
        smt::context m_kernel;
        params_ref   m_params;
        
        imp(ast_manager & m, front_end_params & fp, params_ref const & p):
            m_kernel(m, fp, p),
            m_params(p) {
        }

        front_end_params & fparams() {
            return m_kernel.get_fparams();
        }

        params_ref const & params() {
            return m_params;
        }
     
        ast_manager & m() const {
            return m_kernel.get_manager();
        }

        bool set_logic(symbol logic) {
            return m_kernel.set_logic(logic);
        }
        
        void set_progress_callback(progress_callback * callback) {
            return m_kernel.set_progress_callback(callback);
        }
        
        void assert_expr(expr * e) {
            TRACE("smt_solver", tout << "assert:\n" << mk_ismt2_pp(e, m()) << "\n";);
            m_kernel.assert_expr(e);
        }
        
        void assert_expr(expr * e, proof * pr) {
            m_kernel.assert_expr(e, pr);
        }

        unsigned size() const {
            return m_kernel.get_num_asserted_formulas();
        }
        
        expr * const * get_formulas() const {
            return m_kernel.get_asserted_formulas();
        }
        
        bool reduce() {
            return m_kernel.reduce_assertions();
        }
        
        void push() {
            TRACE("smt_solver", tout << "push()\n";);
            m_kernel.push();
        }

        void pop(unsigned num_scopes) {
            TRACE("smt_solver", tout << "pop()\n";);
            m_kernel.pop(num_scopes);
        }
        
        unsigned get_scope_level() const {
            return m_kernel.get_scope_level();
        }

        lbool setup_and_check() {
            return m_kernel.setup_and_check();
        }

        bool inconsistent() {
            return m_kernel.inconsistent();
        }
        
        lbool check(unsigned num_assumptions, expr * const * assumptions) {
            return m_kernel.check(num_assumptions, assumptions);
        }
        
        void get_model(model_ref & m) const {
            m_kernel.get_model(m);
        }

        proof * get_proof() {
            return m_kernel.get_proof();
        }

        unsigned get_unsat_core_size() const {
            return m_kernel.get_unsat_core_size();
        }
        
        expr * get_unsat_core_expr(unsigned idx) const {
            return m_kernel.get_unsat_core_expr(idx);
        }
        
        failure last_failure() const {
            return m_kernel.get_last_search_failure();
        }
        
        std::string last_failure_as_string() const {
            return m_kernel.last_failure_as_string();
        }

        void get_assignments(expr_ref_vector & result) {
            m_kernel.get_assignments(result);
        }
        
        void get_relevant_labels(expr * cnstr, buffer<symbol> & result) {
            m_kernel.get_relevant_labels(cnstr, result);
        }
        
        void get_relevant_labeled_literals(bool at_lbls, expr_ref_vector & result) {
            m_kernel.get_relevant_labeled_literals(at_lbls, result);
        }

        void get_relevant_literals(expr_ref_vector & result) {
            m_kernel.get_relevant_literals(result);
        }
        
        void get_guessed_literals(expr_ref_vector & result) {
            m_kernel.get_guessed_literals(result);
        }

        void display(std::ostream & out) const {
            // m_kernel.display(out); <<< for external users it is just junk
            // TODO: it will be replaced with assertion_stack.display
            unsigned num = m_kernel.get_num_asserted_formulas();
            expr * const * fms = m_kernel.get_asserted_formulas();
            out << "(solver";
            for (unsigned i = 0; i < num; i++) {
                out << "\n  " << mk_ismt2_pp(fms[i], m(), 2);
            }
            out << ")";
        }
        
        void collect_statistics(::statistics & st) const {
            m_kernel.collect_statistics(st);
        }
        
        void reset_statistics() {
        }

        void display_statistics(std::ostream & out) const {
            m_kernel.display_statistics(out);
        }
        
        void display_istatistics(std::ostream & out) const {
            m_kernel.display_istatistics(out);
        }

        void set_cancel(bool f) {
            m_kernel.set_cancel_flag(f);
        }
        
        bool canceled() {
            return m_kernel.get_cancel_flag();
        }

        void updt_params(params_ref const & p) {
            params2front_end_params(p, fparams());
        }

        void collect_param_descrs(param_descrs & d) {
            solver_front_end_params_descrs(d);
        }
    };

    solver::solver(ast_manager & m, front_end_params & fp, params_ref const & p) {
        m_imp = alloc(imp, m, fp, p);
    }

    solver::~solver() {
        dealloc(m_imp);
    }

    ast_manager & solver::m() const {
        return m_imp->m();
    }

    bool solver::set_logic(symbol logic) {
        return m_imp->set_logic(logic);
    }

    void solver::set_progress_callback(progress_callback * callback) {
        m_imp->set_progress_callback(callback);
    }

    void solver::assert_expr(expr * e) {
        m_imp->assert_expr(e);
    }

    void solver::assert_expr(expr * e, proof * pr) {
        m_imp->assert_expr(e, pr);
    }

    unsigned solver::size() const {
        return m_imp->size();
    }
    
    expr * const * solver::get_formulas() const {
        return m_imp->get_formulas();
    }

    bool solver::reduce() {
        return m_imp->reduce();
    }

    void solver::push() {
        m_imp->push();
    }

    void solver::pop(unsigned num_scopes) {
        m_imp->pop(num_scopes);
    }

    unsigned solver::get_scope_level() const {
        return m_imp->get_scope_level();
    }

    void solver::reset() {
        ast_manager & _m       = m();
        front_end_params & fps = m_imp->fparams();
        params_ref ps          = m_imp->params();
        #pragma omp critical (smt_solver)
        {
            dealloc(m_imp);
            m_imp = alloc(imp, _m, fps, ps);
        }
    }

    bool solver::inconsistent() {
        return m_imp->inconsistent();
    }

    lbool solver::setup_and_check() {
        set_cancel(false);
        return m_imp->setup_and_check();
    }

    lbool solver::check(unsigned num_assumptions, expr * const * assumptions) {
        set_cancel(false);
        lbool r = m_imp->check(num_assumptions, assumptions);
        TRACE("smt_solver", tout << "check result: " << r << "\n";);
        return r;
    }

    void solver::get_model(model_ref & m) const {
        m_imp->get_model(m);
    }

    proof * solver::get_proof() {
        return m_imp->get_proof();
    }

    unsigned solver::get_unsat_core_size() const {
        return m_imp->get_unsat_core_size();
    }
        
    expr * solver::get_unsat_core_expr(unsigned idx) const {
        return m_imp->get_unsat_core_expr(idx);
    }

    failure solver::last_failure() const {
        return m_imp->last_failure();
    }

    std::string solver::last_failure_as_string() const {
        return m_imp->last_failure_as_string();
    }

    void solver::get_assignments(expr_ref_vector & result) {
        m_imp->get_assignments(result);
    }
        
    void solver::get_relevant_labels(expr * cnstr, buffer<symbol> & result) {
        m_imp->get_relevant_labels(cnstr, result);
    }
    
    void solver::get_relevant_labeled_literals(bool at_lbls, expr_ref_vector & result) {
        m_imp->get_relevant_labeled_literals(at_lbls, result);
    }

    void solver::get_relevant_literals(expr_ref_vector & result) {
        m_imp->get_relevant_literals(result);
    }

    void solver::get_guessed_literals(expr_ref_vector & result) {
        m_imp->get_guessed_literals(result);
    }

    void solver::display(std::ostream & out) const {
        m_imp->display(out);
    }

    void solver::collect_statistics(::statistics & st) const {
        m_imp->collect_statistics(st);
    }
        
    void solver::reset_statistics() {
        m_imp->reset_statistics();
    }

    void solver::display_statistics(std::ostream & out) const {
        m_imp->display_statistics(out);
    }

    void solver::display_istatistics(std::ostream & out) const {
        m_imp->display_istatistics(out);
    }

    void solver::set_cancel(bool f) {
        #pragma omp critical (smt_solver)
        {
            if (m_imp)
                m_imp->set_cancel(f);
        }
    }

    bool solver::canceled() const {
        return m_imp->canceled();
    }

    void solver::updt_params(params_ref const & p) {
        return m_imp->updt_params(p);
    }

    void solver::collect_param_descrs(param_descrs & d) const {
        return m_imp->collect_param_descrs(d);
    }

    context & solver::kernel() {
        return m_imp->m_kernel;
    }

};
