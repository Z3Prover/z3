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
#ifndef SOLVER_H_
#define SOLVER_H_

#include"check_sat_result.h"
#include"progress_callback.h"
#include"params.h"

class solver;

class solver_factory {
public:
    virtual ~solver_factory() {}
    virtual solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) = 0;
};

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
*/
class solver : public check_sat_result {
public:
    virtual ~solver() {}

    /**
    \brief Creates a clone of the solver.
    */
    virtual solver* translate(ast_manager& m, params_ref const& p) = 0;

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
       \brief Enable/Disable model generation for this solver object.

       It is invoked before init(m, logic). 
       The user may optionally invoke it after init(m, logic).
    */
    virtual void set_produce_models(bool f) {}
    
    /**
       \brief Add a new formula to the assertion stack.
    */
    virtual void assert_expr(expr * t) = 0;

    /**
       \brief Add a new formula \c t to the assertion stack, and "tag" it with \c a.
       The propositional variable \c a is used to track the use of \c t in a proof
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
    \brief The number of tracked assumptions (see assert_expr(t, a)).
    */
    virtual unsigned get_num_assumptions() const = 0;

    /**
    \brief Retrieves the idx'th tracked assumption (see assert_expr(t, a)).
    */
    virtual expr * get_assumption(unsigned idx) const = 0;



    /**
       \brief Display the content of this solver.
    */
    virtual void display(std::ostream & out) const;

    class scoped_push {
        solver& s;
        bool    m_nopop;
    public:
        scoped_push(solver& s):s(s), m_nopop(false) { s.push();  }
        ~scoped_push() { if (!m_nopop) s.pop(1); }
        void disable_pop() { m_nopop = true; }
    };

protected:
    virtual void set_cancel(bool f) = 0;
};

#endif
