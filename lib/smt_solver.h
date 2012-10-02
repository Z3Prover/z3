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
#ifndef _SMT_SOLVER_H_
#define _SMT_SOLVER_H_

#include"ast.h"
#include"params.h"
#include"model.h"
#include"lbool.h"
#include"statistics.h"
#include"smt_failure.h"

struct front_end_params;
class progress_callback;

namespace smt {

    class enode;
    class context;
    
    class solver {
        struct imp;
        imp *  m_imp;
    public:
        solver(ast_manager & m, front_end_params & fp, params_ref const & p = params_ref());

        ~solver();

        ast_manager & m() const;
        
        /**
           \brief Set logic. It must be invoked before any assertions.
           Return true if succeeded.
        */
        bool set_logic(symbol logic);

        /**
           brief Set progress meter. Solver will invoke the callback from time to time.
        */
        void set_progress_callback(progress_callback * callback);

        /**
           \brief Assert the given assetion into the logical context.
           This method uses the "asserted" proof as a justification for e.
        */
        void assert_expr(expr * e);
        
        /**
           \brief Assert the given assertion with the given proof as a justification.
        */
        void assert_expr(expr * e, proof * pr);

        /**
           \brief Return the number of asserted formulas in the solver.
        */
        unsigned size() const;
        
        /**
           \brief Return the array of asserted formulas.
        */
        expr * const * get_formulas() const;
        
        /**
           \brief Reduce the set of asserted formulas using preprocessors.
           Return true if an inconsistency is detected.
           
           \remark This is mainly used by dl_smt_relation. This method 
           seens to be misplaced. This is not the right place.
        */
        bool reduce();

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
           \brief Reset the solver.
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
           \brief Return the set of formulas assigned by the solver.
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
           \brief (For debubbing purposes) Prints the state of the solver
        */
        void display(std::ostream & out) const;

        /**
           \brief Collect runtime statistics.
         */
        void collect_statistics(::statistics & st) const;
        
        /**
           \brief Reset solver statistics.
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
           \brief Interrupt the solver. 
        */
        void set_cancel(bool f = true);
        void cancel() { set_cancel(true); }

        /**
           \brief Reset interruption.
        */
        void reset_cancel() { set_cancel(false); }
        
        /**
           \brief Return true if the solver was interrupted.
        */
        bool canceled() const;
        
        /**
           \brief Update configuration parameters.
        */
        void updt_params(params_ref const & p);

        /**
           \brief Collect a description of the configuration parameters.
        */
        void collect_param_descrs(param_descrs & d) const;

        /**
           \brief Return a reference to the kernel.
           This is a temporary hack to support user theories.
           TODO: remove this hack.
           We need to revamp user theories too.

           This method breaks the abstraction barrier.

           \warning We should not use this method
        */
        context & kernel();
    };
};

#endif
