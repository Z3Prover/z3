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
#include"front_end_params.h"
#include"progress_callback.h"
#include"params.h"

class solver : public check_sat_result {
public:
    virtual ~solver() {}
    
    // for backward compatibility
    virtual void set_front_end_params(front_end_params & p) {} 

    virtual void updt_params(params_ref const & p) {}
    virtual void collect_param_descrs(param_descrs & r) {}

    virtual void set_produce_proofs(bool f) {}
    virtual void set_produce_models(bool f) {}
    virtual void set_produce_unsat_cores(bool f) {}
    
    virtual void init(ast_manager & m, symbol const & logic) = 0;
    virtual void reset() = 0;
    virtual void assert_expr(expr * t) = 0;
    virtual void push() = 0;
    virtual void pop(unsigned n) = 0;
    virtual unsigned get_scope_level() const = 0;
    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) = 0;

    virtual void set_cancel(bool f) {}
    void cancel() { set_cancel(true); }
    void reset_cancel() { set_cancel(false); }

    virtual void set_progress_callback(progress_callback * callback) = 0;

    virtual unsigned get_num_assertions() const;
    virtual expr * get_assertion(unsigned idx) const;

    virtual void display(std::ostream & out) const;
};

solver * mk_default_solver();

#endif
