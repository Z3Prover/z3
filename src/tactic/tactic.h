/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    tactic.h

Abstract:

    Abstract tactic object.
    It used to be called assertion_set_strategy.
    The main improvement is the support for multiple subgoals.

Author:

    Leonardo (leonardo) 2011-10-13

Notes:

--*/
#ifndef _TACTIC_H_
#define _TACTIC_H_

#include"goal.h"
#include"params.h"
#include"statistics.h"
#include"model_converter.h"
#include"proof_converter.h"
#include"tactic_exception.h"
#include"lbool.h"

class progress_callback;

typedef ptr_buffer<goal> goal_buffer;

class tactic {
    unsigned m_ref_count;
public:
    tactic():m_ref_count(0) {}
    virtual ~tactic() {}

    void inc_ref() { m_ref_count++; }
    void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (m_ref_count == 0) dealloc(this); }

    virtual void updt_params(params_ref const & p) {}
    virtual void collect_param_descrs(param_descrs & r) {}

    void cancel();
    void reset_cancel();
    
    /**
       \brief Apply tactic to goal \c in.
       
       The list of resultant subgoals is stored in \c result.
       The content of \c in may be destroyed during the operation.
       
       The resultant model converter \c mc can be used to convert a model for one of the returned subgoals
       into a model for \in. If mc == 0, then model construction is disabled or any model for a subgoal
       of \c in is also a model for \c in.
       If \c result is decided_sat (i.e., it contains a single empty subgoal), then
       the model converter is just wrapping the model.

       The resultant proof converter \c pc can be used to convert proofs for each subgoal in \c result
       into a proof for \c in. If pc == 0, then one of the following conditions should hold:
         1- proof construction is disabled, 
         2- result contains a single subgoal, and any proof of unsatisfiability for this subgoal is a proof for \c in.
         3- result is an decided_unsat (i.e., it contains a single unsat subgoal). The actual proof can be extracted from this goal.
         
       The output parameter \c core is used to accumulate the unsat core of closed subgoals.
       It must be 0 if dependency tracking is disabled, or the result is decided unsat, or 
       no tagged assertions were used to close any subgoal.
       
       Note that, this signature is not compatible with the one described in the paper:
       "The Strategy Challenge in SMT Solving".
       The approach in the paper is conceptually simpler, but (for historical reasons) it would
       require a lot of re-engineering in the Z3 code. In Z3, we keep a proof/justification for every formula
       in a goal.
       
       Therefore, in most cases, pc == 0 and core == 0 for non-branching tactics.
    */
    virtual void operator()(/* in */  goal_ref const & in, 
                            /* out */ goal_ref_buffer & result, 
                            /* out */ model_converter_ref & mc, 
                            /* out */ proof_converter_ref & pc,
                            /* out */ expr_dependency_ref & core) = 0;

    virtual void collect_statistics(statistics & st) const {}
    virtual void reset_statistics() {}
    virtual void cleanup() = 0;
    virtual void reset() { cleanup(); }

    // for backward compatibility
    virtual void set_logic(symbol const & l) {}
    virtual void set_progress_callback(progress_callback * callback) {}

    // translate tactic to the given manager
    virtual tactic * translate(ast_manager & m) = 0;
private:
    friend class nary_tactical;
    friend class binary_tactical;
    friend class unary_tactical;

    virtual void set_cancel(bool f) {}

};

typedef ref<tactic>         tactic_ref;
typedef sref_vector<tactic> tactic_ref_vector;
typedef sref_buffer<tactic> tactic_ref_buffer;

// minimum verbosity level for tactics
#define TACTIC_VERBOSITY_LVL 10

class tactic_report {
    struct imp;
    imp *  m_imp;
public:
    tactic_report(char const * id, goal const & g);
    ~tactic_report();
};

void report_tactic_progress(char const * id, unsigned val);

class skip_tactic : public tactic {
public:
    virtual void operator()(goal_ref const & in, goal_ref_buffer & result, model_converter_ref & mc, proof_converter_ref & pc, expr_dependency_ref & core);
    virtual void cleanup() {}
    virtual tactic * translate(ast_manager & m) { return this; }
};

tactic * mk_skip_tactic();
tactic * mk_fail_tactic();
tactic * mk_fail_if_undecided_tactic();

/*
  ADD_TACTIC("skip", "do nothing tactic.", "mk_skip_tactic()")
  ADD_TACTIC("fail", "always fail tactic.", "mk_fail_tactic()")
  ADD_TACTIC("fail-if-undecided", "fail if goal is undecided.", "mk_fail_if_undecided_tactic()")
*/

tactic * mk_report_verbose_tactic(char const * msg, unsigned lvl);
tactic * mk_trace_tactic(char const * tag);

class tactic_factory {
public:
    virtual ~tactic_factory() {}
    virtual tactic * operator()(ast_manager & m, params_ref const & p) = 0;
};

#define MK_TACTIC_FACTORY(NAME, CODE)                                           \
class NAME : public tactic_factory {                                            \
public:                                                                         \
    virtual ~NAME() {}                                                          \
    virtual tactic * operator()(ast_manager & m, params_ref const & p) { CODE } \
};

#define MK_SIMPLE_TACTIC_FACTORY(NAME, ST)  MK_TACTIC_FACTORY(NAME, return ST;)

void exec(tactic & t, goal_ref const & in, goal_ref_buffer & result, model_converter_ref & mc, proof_converter_ref & pc, expr_dependency_ref & core);
lbool check_sat(tactic & t, goal_ref & g, model_ref & md, proof_ref & pr, expr_dependency_ref & core, std::string & reason_unknown);

// Throws an exception if goal \c in requires proof generation.
void fail_if_proof_generation(char const * tactic_name, goal_ref const & in);
void fail_if_unsat_core_generation(char const * tactic_name, goal_ref const & in);
void fail_if_model_generation(char const * tactic_name, goal_ref const & in);

#endif
