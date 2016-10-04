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

    void assert_expr(expr_ref_vector const& ts) { 
        for (unsigned i = 0; i < ts.size(); ++i) assert_expr(ts[i]); 
    }

    void assert_expr(ptr_vector<expr> const& ts) { 
        for (unsigned i = 0; i < ts.size(); ++i) assert_expr(ts[i]); 
    }

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

    lbool check_sat(expr_ref_vector const& asms) { return check_sat(asms.size(), asms.c_ptr()); }
    
    lbool check_sat(app_ref_vector const& asms) { return check_sat(asms.size(), (expr* const*)asms.c_ptr()); }


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
    \brief Retrieves assertions as a vector.
    */
    void get_assertions(expr_ref_vector& fmls) const;

    /**
    \brief The number of tracked assumptions (see assert_expr(t, a)).
    */
    virtual unsigned get_num_assumptions() const = 0;

    /**
    \brief Retrieves the idx'th tracked assumption (see assert_expr(t, a)).
    */
    virtual expr * get_assumption(unsigned idx) const = 0;

    /**
    \brief under assumptions, asms, retrieve set of consequences that 
    fix values for expressions that can be built from vars. 
    The consequences are clauses whose first literal constrain one of the 
    functions from vars and the other literals are negations of literals from asms.
    */
    
    virtual lbool get_consequences(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences);


    /**
       \brief Find maximal subsets A' of A such that |A'| <= 1. These subsets look somewhat similar to cores: cores have the property 
       that |~A'| >= 1, where ~A' is the set of negated formulas from A'
     */

    virtual lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes);

    /**
       \brief Display the content of this solver.
    */
    virtual std::ostream& display(std::ostream & out) const;

    class scoped_push {
        solver& s;
        bool    m_nopop;
    public:
        scoped_push(solver& s):s(s), m_nopop(false) { s.push();  }
        ~scoped_push() { if (!m_nopop) s.pop(1); }
        void disable_pop() { m_nopop = true; }
    };
 
protected:

    virtual lbool get_consequences_core(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences);

    bool is_literal(ast_manager& m, expr* e);

};

#endif
