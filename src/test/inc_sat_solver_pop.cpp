/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    inc_sat_solver_pop.cpp

Abstract:

    Assertions of the incremental SAT solver after a pop. The formulas
    asserted in a popped scope and their variables do not reappear.

--*/

#include "ast/reg_decl_plugins.h"
#include "ast/for_each_expr.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "solver/solver.h"
#include "util/util.h"

static bool mentions(expr_ref_vector const& formulas, expr_ref_vector const& constants) {
    expr_mark marked;
    for (expr* f : formulas)
        for (expr* e : subterms::all(expr_ref(f, formulas.get_manager())))
            marked.mark(e, true);
    for (expr* c : constants)
        if (marked.is_marked(c))
            return true;
    return false;
}

static expr_ref_vector mk_bools(ast_manager& m, char const* prefix, unsigned n) {
    expr_ref_vector result(m);
    for (unsigned i = 0; i < n; ++i) {
        std::string name = std::string(prefix) + std::to_string(i);
        result.push_back(m.mk_const(symbol(name), m.mk_bool_sort()));
    }
    return result;
}

// a is asserted in a scope. After the pop the assertions do not contain a.
static void tst_pop_drops_assertions() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref p;
    ref<solver> s = mk_inc_sat_solver(m, p);
    expr_ref_vector a = mk_bools(m, "a", 1);
    s->push();
    s->assert_expr(a.get(0));
    ENSURE(s->check_sat(0, nullptr) == l_true);
    ENSURE(mentions(s->get_assertions(), a));
    s->pop(1);
    ENSURE(!mentions(s->get_assertions(), a));
}

// Clauses over a0, ..., a5 are asserted in a scope, and the assertions are
// read back. After the pop, p = (q or not r) is asserted. The SAT solver
// numbers its new variables like the popped ones; the assertions read back
// mention none of a0, ..., a5.
static void tst_pop_reuses_variable_numbers() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref p;
    ref<solver> s = mk_inc_sat_solver(m, p);
    expr_ref_vector a = mk_bools(m, "a", 6);
    expr_ref_vector pqr = mk_bools(m, "p", 3);
    s->push();
    for (unsigned i = 0; i + 1 < a.size(); ++i)
        s->assert_expr(m.mk_or(a.get(i), m.mk_not(a.get(i + 1))));
    s->assert_expr(m.mk_or(a.get(5), a.get(0)));
    ENSURE(s->check_sat(0, nullptr) == l_true);
    ENSURE(mentions(s->get_assertions(), a));
    s->pop(1);
    s->assert_expr(m.mk_eq(pqr.get(0), m.mk_or(pqr.get(1), m.mk_not(pqr.get(2)))));
    ENSURE(s->check_sat(0, nullptr) == l_true);
    ENSURE(!mentions(s->get_assertions(), a));
}

void tst_inc_sat_solver_pop() {
    tst_pop_drops_assertions();
    tst_pop_reuses_variable_numbers();
}
