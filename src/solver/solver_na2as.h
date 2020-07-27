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
#pragma once

#include "solver/solver.h"

class solver_na2as : public solver {
 protected:
    ast_manager &      m;
    expr_ref_vector    m_assumptions;
    unsigned_vector    m_scopes;
    void restore_assumptions(unsigned old_sz);
public:
    solver_na2as(ast_manager & m);
    ~solver_na2as() override;

    void assert_expr_core2(expr * t, expr * a) override;

    // Subclasses of solver_na2as should redefine the following *_core methods instead of these ones.
    lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) override;
    lbool check_sat_cc(const expr_ref_vector &assumptions, vector<expr_ref_vector> const &clauses) override;
    void push() override;
    void pop(unsigned n) override;
    unsigned get_scope_level() const override;

    unsigned get_num_assumptions() const override { return m_assumptions.size(); }
    expr * get_assumption(unsigned idx) const override { return m_assumptions[idx]; }
    lbool get_consequences(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences) override;
    lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) override;
protected:
    virtual lbool check_sat_core2(unsigned num_assumptions, expr * const * assumptions) = 0;
    virtual lbool check_sat_cc_core(const expr_ref_vector &assumptions, vector<expr_ref_vector> const &clauses) { NOT_IMPLEMENTED_YET(); return l_undef; }
    virtual void push_core() = 0;
    virtual void pop_core(unsigned n) = 0;
};


