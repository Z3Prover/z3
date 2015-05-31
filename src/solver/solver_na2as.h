/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    solver_na2as.h

Abstract:

    Solver that implements "named" assertions using assumptions (aka answer literals).
    That is, a named assertion assert_expr(t, a) is mapped into
          a implies t
    and 'a' is used as an extra assumption for check_sat.

Author:

    Leonardo (leonardo) 2012-11-02

Notes:

--*/
#ifndef _SOLVER_NA2AS_H_
#define _SOLVER_NA2AS_H_

#include"solver.h"

class solver_na2as : public solver {
    ast_manager &      m_manager;
    ptr_vector<expr>   m_assumptions;
    unsigned_vector    m_scopes;
    void restore_assumptions(unsigned old_sz);
public:
    solver_na2as(ast_manager & m);
    virtual ~solver_na2as();

    virtual void assert_expr(expr * t, expr * a);
    virtual void assert_expr(expr * t) = 0;
    
    // Subclasses of solver_na2as should redefine the following *_core methods instead of these ones.
    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions);
    virtual void push();
    virtual void pop(unsigned n);
    virtual unsigned get_scope_level() const;
    
    virtual unsigned get_num_assumptions() const { return m_assumptions.size(); }
    virtual expr * get_assumption(unsigned idx) const { return m_assumptions[idx]; }
protected:
    virtual lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) = 0;
    virtual void push_core() = 0;
    virtual void pop_core(unsigned n) = 0;
};


#endif
