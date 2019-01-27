/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_kernel.cpp

Abstract:

    New frontend for smt::context.
    
Author:

    Leonardo de Moura (leonardo) 2012-02-09.

Revision History:

--*/
#include "smt/smt_kernel.h"
#include "smt/smt_context.h"
#include "ast/ast_smt2_pp.h"
#include "smt/params/smt_params_helper.hpp"

namespace smt {

    struct kernel::imp {
        smt::context m_kernel;
        params_ref   m_params;
        
        imp(ast_manager & m, smt_params & fp, params_ref const & p):
            m_kernel(m, fp, p),
            m_params(p) {
        }

        static void copy(imp& src, imp& dst) {
            context::copy(src.m_kernel, dst.m_kernel);
        }

        smt_params & fparams() {
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

        void display(std::ostream & out) const {
            // m_kernel.display(out); <<< for external users it is just junk
            // TODO: it will be replaced with assertion_stack.display
            unsigned num = m_kernel.get_num_asserted_formulas();
            out << "(kernel";
            for (unsigned i = 0; i < num; i++) {
                expr* f = m_kernel.get_asserted_formula(i);
                out << "\n  " << mk_ismt2_pp(f, m(), 2);
            }
            out << ")";
        }
        
        void assert_expr(expr * e) {
            TRACE("smt_kernel", tout << "assert:\n" << mk_ismt2_pp(e, m()) << "\n";);
            m_kernel.assert_expr(e);
        }
        
        void assert_expr(expr * e, proof * pr) {
            m_kernel.assert_expr(e, pr);
        }

        unsigned size() const {
            return m_kernel.get_num_asserted_formulas();
        }
        
        void get_formulas(ptr_vector<expr>& fmls) const {
            m_kernel.get_asserted_formulas(fmls);
        }

        expr* get_formula(unsigned i) const {
            return m_kernel.get_asserted_formula(i);
        }
        
        void push() {
            TRACE("smt_kernel", tout << "push()\n";);
            m_kernel.push();
        }

        void pop(unsigned num_scopes) {
            TRACE("smt_kernel", tout << "pop()\n";);
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

        lbool check(expr_ref_vector const& cube, vector<expr_ref_vector> const& clause) {
            return m_kernel.check(cube, clause);
        }        

        lbool get_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& vars, expr_ref_vector& conseq, expr_ref_vector& unfixed) {
            return m_kernel.get_consequences(assumptions, vars, conseq, unfixed);
        }

        lbool preferred_sat(expr_ref_vector const& asms, vector<expr_ref_vector>& cores) {
            return m_kernel.preferred_sat(asms, cores);
        }

        lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) {
            return m_kernel.find_mutexes(vars, mutexes);
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

        void set_reason_unknown(char const* msg) {
            m_kernel.set_reason_unknown(msg);
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

        expr* next_decision() {
            return m_kernel.next_decision();
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
        
        bool canceled() {
            return m_kernel.get_cancel_flag();
        }

        void updt_params(params_ref const & p) {
            m_kernel.updt_params(p);
        }
    };

    kernel::kernel(ast_manager & m, smt_params & fp, params_ref const & p) {
        m_imp = alloc(imp, m, fp, p);
    }

    kernel::~kernel() {
        dealloc(m_imp);
    }

    ast_manager & kernel::m() const {
        return m_imp->m();
    }

    void  kernel::copy(kernel& src, kernel& dst) {
        imp::copy(*src.m_imp, *dst.m_imp);
    }

    bool kernel::set_logic(symbol logic) {
        return m_imp->set_logic(logic);
    }

    void kernel::set_progress_callback(progress_callback * callback) {
        m_imp->set_progress_callback(callback);
    }

    void kernel::assert_expr(expr * e) {
        m_imp->assert_expr(e);
    }

    void kernel::assert_expr(expr_ref_vector const& es) {
        for (unsigned i = 0; i < es.size(); ++i) {
            m_imp->assert_expr(es[i]);
        }
    }

    void kernel::assert_expr(expr * e, proof * pr) {
        m_imp->assert_expr(e, pr);
    }

    unsigned kernel::size() const {
        return m_imp->size();
    }
    
    expr* kernel::get_formula(unsigned i) const {
        return m_imp->get_formula(i);
    }


    void kernel::push() {
        m_imp->push();
    }

    void kernel::pop(unsigned num_scopes) {
        m_imp->pop(num_scopes);
    }

    unsigned kernel::get_scope_level() const {
        return m_imp->get_scope_level();
    }

    void kernel::reset() {
        ast_manager & _m = m();
        smt_params & fps = m_imp->fparams();
        params_ref ps    = m_imp->params();
        #pragma omp critical (smt_kernel)
        {
            m_imp->~imp();
            m_imp = new (m_imp) imp(_m, fps, ps);
        }
    }

    bool kernel::inconsistent() {
        return m_imp->inconsistent();
    }

    lbool kernel::setup_and_check() {
        return m_imp->setup_and_check();
    }

    lbool kernel::check(unsigned num_assumptions, expr * const * assumptions) {
        lbool r = m_imp->check(num_assumptions, assumptions);
        TRACE("smt_kernel", tout << "check result: " << r << "\n";);
        return r;
    }

    lbool kernel::check(expr_ref_vector const& cube, vector<expr_ref_vector> const& clauses) {
        return m_imp->check(cube, clauses);
    }


    lbool kernel::get_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& vars, expr_ref_vector& conseq, expr_ref_vector& unfixed) {
        return m_imp->get_consequences(assumptions, vars, conseq, unfixed);
    }

    lbool kernel::preferred_sat(expr_ref_vector const& asms, vector<expr_ref_vector>& cores) {
        return m_imp->preferred_sat(asms, cores);
    }

    lbool kernel::find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) {
        return m_imp->find_mutexes(vars, mutexes);
    }

    void kernel::get_model(model_ref & m) const {
        m_imp->get_model(m);
    }

    proof * kernel::get_proof() {
        return m_imp->get_proof();
    }

    unsigned kernel::get_unsat_core_size() const {
        return m_imp->get_unsat_core_size();
    }
        
    expr * kernel::get_unsat_core_expr(unsigned idx) const {
        return m_imp->get_unsat_core_expr(idx);
    }

    failure kernel::last_failure() const {
        return m_imp->last_failure();
    }

    std::string kernel::last_failure_as_string() const {
        return m_imp->last_failure_as_string();
    }

    void kernel::set_reason_unknown(char const* msg) {
        m_imp->set_reason_unknown(msg);
    }

    void kernel::get_assignments(expr_ref_vector & result) {
        m_imp->get_assignments(result);
    }
        
    void kernel::get_relevant_labels(expr * cnstr, buffer<symbol> & result) {
        m_imp->get_relevant_labels(cnstr, result);
    }
    
    void kernel::get_relevant_labeled_literals(bool at_lbls, expr_ref_vector & result) {
        m_imp->get_relevant_labeled_literals(at_lbls, result);
    }

    void kernel::get_relevant_literals(expr_ref_vector & result) {
        m_imp->get_relevant_literals(result);
    }

    void kernel::get_guessed_literals(expr_ref_vector & result) {
        m_imp->get_guessed_literals(result);
    }

    expr* kernel::next_decision() {
        return m_imp->next_decision();
    }        

    void kernel::display(std::ostream & out) const {
        m_imp->display(out);
    }

    void kernel::collect_statistics(::statistics & st) const {
        m_imp->collect_statistics(st);
    }
        
    void kernel::reset_statistics() {
        m_imp->reset_statistics();
    }

    void kernel::display_statistics(std::ostream & out) const {
        m_imp->display_statistics(out);
    }

    void kernel::display_istatistics(std::ostream & out) const {
        m_imp->display_istatistics(out);
    }

    bool kernel::canceled() const {
        return m_imp->canceled();
    }

    void kernel::updt_params(params_ref const & p) {
        return m_imp->updt_params(p);
    }

    void kernel::collect_param_descrs(param_descrs & d) {
        smt_params_helper::collect_param_descrs(d);
    }

    context & kernel::get_context() {
        return m_imp->m_kernel;
    }

};
