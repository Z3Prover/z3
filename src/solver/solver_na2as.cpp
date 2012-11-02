/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    solver_na2as.cpp

Abstract:

    Solver that implements "named" assertions using assumptions (aka answer literals).
    That is, a named assertion assert_expr(t, a) is mapped into
          a implies t
    and 'a' is used as an extra assumption for check_sat.

Author:

    Leonardo (leonardo) 2012-11-02

Notes:

--*/
#include"solver_na2as.h"

solver_na2as::solver_na2as() {
    m_manager = 0;
}

solver_na2as::~solver_na2as() {
    reset();
}

void solver_na2as::assert_expr(expr * t, expr * a) {
    SASSERT(m_manager != 0);
    expr * new_t = m_manager->mk_implies(a, t);
    m_manager->inc_ref(a);
    m_assumptions.push_back(a);
    assert_expr(new_t);
}
    
void solver_na2as::init(ast_manager & m, symbol const & logic) {
    SASSERT(m_assumptions.empty());
    m_manager = &m;
    init_core(m, logic);
}

struct append_assumptions {
    ptr_vector<expr> & m_assumptions;
    unsigned           m_old_sz;
    append_assumptions(ptr_vector<expr> & _m_assumptions, 
                       unsigned num_assumptions, 
                       expr * const * assumptions):
        m_assumptions(_m_assumptions) {
        m_old_sz = m_assumptions.size();
        m_assumptions.append(num_assumptions, assumptions);
    }

    ~append_assumptions() {
        m_assumptions.shrink(m_old_sz);
    }
};

lbool solver_na2as::check_sat(unsigned num_assumptions, expr * const * assumptions) {
    append_assumptions app(m_assumptions, num_assumptions, assumptions);
    return check_sat_core(num_assumptions, assumptions);
}

void solver_na2as::push() {
    m_scopes.push_back(m_assumptions.size());
    push_core();
}

void solver_na2as::pop(unsigned n) {
    pop_core(n);
    unsigned lvl = m_scopes.size();
    SASSERT(n <= lvl);
    unsigned new_lvl = lvl - n;
    restore_assumptions(m_scopes[new_lvl]);
    m_scopes.shrink(new_lvl);
}

void solver_na2as::restore_assumptions(unsigned old_sz) {
    SASSERT(m_manager);
    for (unsigned i = old_sz; i < m_assumptions.size(); i++) {
        m_manager->dec_ref(m_assumptions[i]);
    }
    m_assumptions.shrink(old_sz);
}

unsigned solver_na2as::get_scope_level() const {
    return m_scopes.size();
}

void solver_na2as::reset() {
    if (m_manager)
        restore_assumptions(0);
}
