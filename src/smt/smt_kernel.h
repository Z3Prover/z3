/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_kernel.h

Abstract:

    New frontend for smt::context.
    The "kernel" tries to hide details of the smt::context object.
    From now on, clients (code outside of the smt module) should be use smt::kernel instead of smt::context.
    
Author:

    Leonardo de Moura (leonardo) 2012-02-09.

Revision History:

    I initially called it smt::solver. This was confusing to others since we have the abstract solver API,
    and smt::kernel is not a subclass of ::solver.
    To increase the confusion I had a class default_solver that implemented the solver API on top of smt::context.
    To avoid this problem I renamed them in the following way:
        smt::solver     ---> smt::kernel
        default_solver  ---> smt::solver
--*/
#ifndef SMT_KERNEL_H_
#define SMT_KERNEL_H_

#include"ast.h"
#include"params.h"
#include"model.h"
#include"lbool.h"
#include"statistics.h"
#include"smt_failure.h"

struct smt_params;
class progress_callback;

namespace smt {

    class enode;
    class context;
    
    class kernel {
        struct imp;
        imp *  m_imp;
    public:
        kernel(ast_manager & m, smt_params & fp, params_ref const & p = params_ref());

        ~kernel();

        static void copy(kernel& src, kernel& dst);

        ast_manager & m() const;
        
        /**
           \brief Set logic. It must be invoked before any assertions.
           Return true if succeeded.
        */
        bool set_logic(symbol logic);

        /**
           brief Set progress meter. Kernel will invoke the callback from time to time.
        */
        void set_progress_callback(progress_callback * callback);

        /**
           \brief Assert the given assetion into the logical context.
           This method uses the "asserted" proof as a justification for e.
        */
        void assert_expr(expr * e);

        void assert_expr(expr_ref_vector const& es);
        /**
           \brief Assert the given assertion with the given proof as a justification.
        */
        void assert_expr(expr * e, proof * pr);

        /**
           \brief Return the number of asserted formulas in the kernel.
        */
        unsigned size() const;
        
        /**
           \brief Return the array of asserted formulas.
        */
        expr * const * get_formulas() const;
        
        /**
           \brief Create a backtracking point (aka scope level).
        */
        void push();

        /**
           \brief Backtrack the given number of scope levels.
        */
        void pop(unsigned num_scopes);

        /**
           \brief Return the number of backtracking points.
        */
        unsigned get_scope_level() const;

        /**
           \brief Reset the kernel.
           All assertions are erased.
        */
        void reset();

        /**
           \brief Return true if the set of asserted formulas is known to be inconsistent.
        */
        bool inconsistent();

        /**
           \brief Setup the logical context and invoke check.
        */
        lbool setup_and_check();
        
        /**
           \brief Satisfiability check.
        */
        lbool check(unsigned num_assumptions = 0, expr * const * assumptions = 0);

        lbool check(expr_ref_vector const& asms) { return check(asms.size(), asms.c_ptr()); }

        lbool check(app_ref_vector const& asms) { return check(asms.size(), (expr* const*)asms.c_ptr()); }

        /**
           \brief extract consequences among variables.
        */
        lbool get_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& vars, 
                               expr_ref_vector& conseq, expr_ref_vector& unfixed);

        /**
          \brief find mutually exclusive variables.
         */
        lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes);

        /**
           \brief Preferential SAT. 
        */
        lbool preferred_sat(expr_ref_vector const& asms, vector<expr_ref_vector>& cores);

        /**
           \brief Return the model associated with the last check command.
        */
        void get_model(model_ref & m) const;

        /**
           \brief Return the proof of unsatisfiability associated with the last check command.
        */
        proof * get_proof();

        /**
           \brief Return the size of the unsat core associated with the last check command.
        */
        unsigned get_unsat_core_size() const;
        
        /**
           \brief Return the i-th expression in the unsat core associated with the last check command.

           \pre i < get_unsat_core_size()
        */
        expr * get_unsat_core_expr(unsigned i) const;

        /**
           \brief Return the reason for failure for the last check command.
           Failure means, it returned l_undef
        */
        failure last_failure() const;

        /**
           \brief Return a string describing the failure.
        */
        std::string last_failure_as_string() const;


        /**
           \brief Set the reason for unknown.
        */
        void set_reason_unknown(char const* msg);

        /**
           \brief Return the set of formulas assigned by the kernel.
        */
        void get_assignments(expr_ref_vector & result);
        
        /**
           \brief Return the set of relevant labels in the last check command.
        */
        void get_relevant_labels(expr * cnstr, buffer<symbol> & result);

        /**
           \brief Return the relevant labeled_literals in the last check command.
        */
        void get_relevant_labeled_literals(bool at_lbls, expr_ref_vector & result);

        /**
           \brief Return the relevant literals in the last check command.
        */
        void get_relevant_literals(expr_ref_vector & result);

        /**
           \brief Return the set of guessed literals (decisions) performed in the last check command.
        */
        void get_guessed_literals(expr_ref_vector & result);

        /**
           \brief (For debubbing purposes) Prints the state of the kernel
        */
        void display(std::ostream & out) const;

        /**
           \brief Collect runtime statistics.
         */
        void collect_statistics(::statistics & st) const;
        
        /**
           \brief Reset kernel statistics.
        */
        void reset_statistics();

        /**
           \brief Display statistics.
        */
        void display_statistics(std::ostream & out) const;

        /**
           \brief Display statistics in low level format.
        */
        void display_istatistics(std::ostream & out) const;
                
        /**
           \brief Return true if the kernel was interrupted.
        */
        bool canceled() const;
        
        /**
           \brief Update configuration parameters.
        */
        void updt_params(params_ref const & p);

        /**
           \brief Collect a description of the configuration parameters.
        */
        static void collect_param_descrs(param_descrs & d);

        /**
           \brief Return a reference to smt::context.
           This is a temporary hack to support user theories.
           TODO: remove this hack.
           We need to revamp user theories too.

           This method breaks the abstraction barrier.

           \warning We should not use this method
        */
        context & get_context();
    };
};

#endif
