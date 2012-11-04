/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    solver.h

Abstract:

    abstract solver interface

Author:

    Leonardo (leonardo) 2011-03-19

Notes:

--*/
#ifndef _SOLVER_H_
#define _SOLVER_H_

#include"check_sat_result.h"
#include"progress_callback.h"
#include"params.h"

struct front_end_params;

/**
   \brief Abstract interface for making solvers available in the Z3
   API and front-ends such as SMT 2.0 and (legacy) SMT 1.0.

   It provides the basic functionality for incremental solvers.
     - assertions
     - push/pop
     - parameter setting (updt_params)
     - statistics
     - results based on check_sat_result API
     - interruption (set_cancel)
     - resets 
*/
class solver : public check_sat_result {
public:
    virtual ~solver() {}
    
    /**
       \brief This method is invoked to allow the solver to access the front_end_params (environment parameters).
       
       \warning This method is used for backward compatibility. The first solver implemented in Z3 used
       front_end_params to store its configuration parameters. 
    */
    virtual void set_front_end_params(front_end_params & p) {} 

    /**
       \brief Update the solver internal settings. 
    */
    virtual void updt_params(params_ref const & p) {}

    /**
       \brief Store in \c r a description of the configuration
       parameters available in this solver.
    */
    virtual void collect_param_descrs(param_descrs & r) {}
    
    /**
       \brief Enable/Disable proof production for this solver object.
    
       It is invoked before init(m, logic).
    */
    virtual void set_produce_proofs(bool f) {}
    /**
       \brief Enable/Disable model generation for this solver object.

       It is invoked before init(m, logic). 
       The user may optionally invoke it after init(m, logic).
    */
    virtual void set_produce_models(bool f) {}
    /**
       \brief Enable/Disable unsat core generation for this solver object.

       It is invoked before init(m, logic).
    */
    virtual void set_produce_unsat_cores(bool f) {}
    
    /**
       \brief Initialize the solver object with the given ast_manager and logic.
    */
    virtual void init(ast_manager & m, symbol const & logic) = 0;
    
    /**
       \brief Reset the solver internal state. All assertions should be removed.
    */
    virtual void reset() = 0;

    /**
       \brief Add a new formula to the assertion stack.
    */
    virtual void assert_expr(expr * t) = 0;

    /**
       \brief Add a new formula \c t to the assertion stack, and "tag" it with \c a.
       The propositional varialbe \c a is used to track the use of \c t in a proof
       of unsatisfiability.
    */
    virtual void assert_expr(expr * t, expr * a) = 0;

    /**
       \brief Create a backtracking point.
    */
    virtual void push() = 0;

    /**
       \brief Remove \c n backtracking points. All assertions between the pop and matching push are removed. 
    */
    virtual void pop(unsigned n) = 0;

    /**
       \brief Return the number of backtracking points.
    */
    virtual unsigned get_scope_level() const = 0;

    /**
       \brief Check if the set of assertions in the assertion stack is satisfiable modulo the given assumptions.
       
       If it is unsatisfiable, and unsat-core generation is enabled. Then, the unsat-core is a subset of these assumptions.
    */
    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) = 0;

    virtual void set_cancel(bool f) {}
    /**
       \brief Interrupt this solver.
    */
    void cancel() { set_cancel(true); }
    /**
       \brief Reset the interruption.
    */
    void reset_cancel() { set_cancel(false); }

    /**
       \brief Set a progress callback procedure that is invoked by this solver during check_sat.
       
       This is essentially for backward compatibility and integration with VCC tools.
    */
    virtual void set_progress_callback(progress_callback * callback) = 0;
    
    /**
       \brief Return the number of assertions in the assertion stack.
    */
    virtual unsigned get_num_assertions() const;

    /**
       \brief Return the assertion at position idx in the assertion stack.
    */
    virtual expr * get_assertion(unsigned idx) const;

    /**
       \brief Display the content of this solver.
    */
    virtual void display(std::ostream & out) const;
};

#endif
