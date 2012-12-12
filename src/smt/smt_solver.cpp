/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_solver.cpp

Abstract:

    Wraps smt::kernel as a solver for the external API and cmd_context.

Author:

    Leonardo (leonardo) 2012-10-21

Notes:

--*/
#include"solver_na2as.h"
#include"smt_kernel.h"
#include"reg_decl_plugins.h"
#include"smt_params.h"

namespace smt {

    class solver : public solver_na2as {
        smt_params          m_params;
        smt::kernel         m_context;
        progress_callback * m_callback;
        symbol              m_logic;
    public:
        solver(ast_manager & m, params_ref const & p, symbol const & l):
            solver_na2as(m),
            m_params(p),
            m_context(m, m_params) {
            m_logic = l;
            if (m_logic != symbol::null)
                m_context.set_logic(m_logic);
        }
        
        virtual ~solver() {
        }

        virtual void updt_params(params_ref const & p) {
            m_params.updt_params(p);
            m_context.updt_params(p);
        }

        virtual void collect_param_descrs(param_descrs & r) {
            m_context.collect_param_descrs(r);
        }

        virtual void collect_statistics(statistics & st) const {
            m_context.collect_statistics(st);
        }

        virtual void assert_expr(expr * t) {
            m_context.assert_expr(t);
        }

        virtual void push_core() {
            m_context.push();
        }

        virtual void pop_core(unsigned n) {
            m_context.pop(n);
        }

        virtual lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) {
            TRACE("solver_na2as", tout << "smt_solver::check_sat_core: " << num_assumptions << "\n";);
            return m_context.check(num_assumptions, assumptions);
        }

        virtual void get_unsat_core(ptr_vector<expr> & r) {
            unsigned sz = m_context.get_unsat_core_size();
            for (unsigned i = 0; i < sz; i++)
                r.push_back(m_context.get_unsat_core_expr(i));
        }

        virtual void get_model(model_ref & m) {
            m_context.get_model(m);
        }

        virtual proof * get_proof() {
            return m_context.get_proof();
        }

        virtual std::string reason_unknown() const {
            return m_context.last_failure_as_string();
        }

        virtual void get_labels(svector<symbol> & r) {
            buffer<symbol> tmp;
            m_context.get_relevant_labels(0, tmp);
            r.append(tmp.size(), tmp.c_ptr());
        }

        virtual void set_cancel(bool f) {
            m_context.set_cancel(f);
        }

        virtual void set_progress_callback(progress_callback * callback) {
            m_callback = callback;
            m_context.set_progress_callback(callback);
        }

        virtual unsigned get_num_assertions() const {
            return m_context.size();
        }
    
        virtual expr * get_assertion(unsigned idx) const {
            SASSERT(idx < get_num_assertions());
            return m_context.get_formulas()[idx];
        }

        virtual void display(std::ostream & out) const {
            m_context.display(out);
        }
   
    };

};

solver * mk_smt_solver(ast_manager & m, params_ref const & p, symbol const & logic) {
    return alloc(smt::solver, m, p, logic);
}

class smt_solver_factory : public solver_factory {
public:
    virtual solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) {
        return mk_smt_solver(m, p, logic);
    }
};

solver_factory * mk_smt_solver_factory() {
    return alloc(smt_solver_factory);
}

