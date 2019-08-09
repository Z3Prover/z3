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

#include "solver/check_sat_result.h"
#include "solver/progress_callback.h"
#include "util/params.h"

class solver;
class model_converter;

class solver_factory {
public:
    virtual ~solver_factory() {}
    virtual solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) = 0;
};

solver_factory * mk_smt_strategic_solver_factory(symbol const & logic = symbol::null);

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
    params_ref  m_params;
    bool        m_enforce_model_conversion;
    symbol      m_cancel_backup_file;
public:
    solver(): m_enforce_model_conversion(false) {}
    ~solver() override {}

    /**
    \brief Creates a clone of the solver.
    */
    virtual solver* translate(ast_manager& m, params_ref const& p) = 0;

    /**
       \brief Update the solver internal settings. 
    */
    virtual void updt_params(params_ref const & p);

    /**
       \brief reset parameters.
    */
    virtual void reset_params(params_ref const& p);

    /**
       \brief Retrieve set of parameters set on solver.
     */
    virtual params_ref const& get_params() const { return m_params; }

    /**
       \brief Store in \c r a description of the configuration
       parameters available in this solver.
    */
    virtual void collect_param_descrs(param_descrs & r);

    /**
       \brief Push a parameter state. It is restored upon pop.
       Only a single scope of push is supported.
    */
    virtual void push_params() {}

    /**
       \brief Pop a parameter state. \sa push_params.
    */
    virtual void pop_params() {}
    
    /**
       \brief Enable/Disable model generation for this solver object.

       It is invoked before init(m, logic). 
       The user may optionally invoke it after init(m, logic).
    */
    virtual void set_produce_models(bool f) {}
    
    /**
       \brief Add a new formula to the assertion stack.
    */
    void assert_expr(expr* f);

    virtual void assert_expr_core(expr * t) = 0;

    void assert_expr(expr_ref_vector const& ts) { 
        for (expr* e : ts) assert_expr(e);
    }

    void assert_expr(ptr_vector<expr> const& ts) { 
        for (expr* e : ts) assert_expr(e);
    }

    /**
       \brief Add a new formula \c t to the assertion stack, and "tag" it with \c a.
       The propositional variable \c a is used to track the use of \c t in a proof
       of unsatisfiability.
    */

    void assert_expr(expr * t, expr* a);

    virtual void assert_expr_core2(expr * t, expr * a) = 0;

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

    lbool check_sat(unsigned num_assumptions, expr * const * assumptions);

    lbool check_sat(expr_ref_vector const& asms) { return check_sat(asms.size(), asms.c_ptr()); }
    
    lbool check_sat(app_ref_vector const& asms) { return check_sat(asms.size(), (expr* const*)asms.c_ptr()); }

    lbool check_sat() { return check_sat(0, nullptr); }

    /**
       \brief Check satisfiability modulo a cube and a clause.

       The cube corresponds to auxiliary assumptions. The clause as an auxiliary disjunction that is also
       assumed for the check.
    */
    virtual lbool check_sat_cc(expr_ref_vector const& cube, vector<expr_ref_vector> const& clauses) {
        if (clauses.empty()) return check_sat(cube.size(), cube.c_ptr());
        NOT_IMPLEMENTED_YET();
    }

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

    expr_ref_vector get_assertions() const;

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
       \brief Preferential SAT. Prefer assumptions to be true, produce cores that witness cases when not all assumptions can be met.
       by default, preferred sat ignores the assumptions.
     */
    virtual lbool preferred_sat(expr_ref_vector const& asms, vector<expr_ref_vector>& cores);

    /**
       \brief extract a lookahead candidates for branching.
    */

    virtual expr_ref_vector cube(expr_ref_vector& vars, unsigned backtrack_level) = 0;

    /**
       \brief Display the content of this solver.
    */
    virtual std::ostream& display(std::ostream & out, unsigned n = 0, expr* const* assumptions = nullptr) const;

    /**
       \brief Display the content of this solver in DIMACS format
    */
    std::ostream& display_dimacs(std::ostream & out) const;

    /**
       \brief expose model converter when solver produces partially reduced set of assertions.
     */

    virtual model_converter_ref get_model_converter() const { return m_mc0; }

    /**
       \brief extract units from solver.
    */
    expr_ref_vector get_units();

    expr_ref_vector get_non_units();

    virtual expr_ref_vector get_trail() = 0; // { return expr_ref_vector(get_manager()); }
    
    virtual void get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) = 0;

    class scoped_push {
        solver& s;
        bool    m_nopop;
    public:
        scoped_push(solver& s):s(s), m_nopop(false) { s.push();  }
        ~scoped_push() { if (!m_nopop) s.pop(1); }
        void disable_pop() { m_nopop = true; }
    };

    virtual lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) = 0;
 
protected:

    virtual lbool get_consequences_core(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences);

    void dump_state(unsigned sz, expr* const* assumptions);

    bool is_literal(ast_manager& m, expr* e);


};

typedef ref<solver> solver_ref;

inline std::ostream& operator<<(std::ostream& out, solver const& s) {
    return s.display(out);
}

#endif
