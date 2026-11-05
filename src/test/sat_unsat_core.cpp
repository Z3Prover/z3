/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    sat_unsat_core.cpp

Abstract:

    Unsat cores of the incremental SAT solver under assumptions that are
    fixed at level 0.

--*/

#include "ast/reg_decl_plugins.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "solver/solver.h"
#include "util/util.h"

// x or y, then not x. The assumptions not x, y, x are unsat, and {x} is a
// core: not x holds at level 0.
static void tst_assumption_false_at_level_0() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref p;
    ref<solver> s = mk_inc_sat_solver(m, p);
    expr_ref x(m.mk_const(symbol("x"), m.mk_bool_sort()), m);
    expr_ref y(m.mk_const(symbol("y"), m.mk_bool_sort()), m);
    expr_ref not_x(m.mk_not(x), m);
    s->assert_expr(m.mk_or(x, y));
    ENSURE(s->check_sat(0, nullptr) == l_true);
    s->assert_expr(not_x);
    expr* assumptions[3] = {not_x, y, x};
    ENSURE(s->check_sat(3, assumptions) == l_false);
    expr_ref_vector core(m);
    s->get_unsat_core(core);
    ENSURE(core.size() == 1 && core.get(0) == x);
}

// Random clauses and units over few variables, checked under random literal
// assumptions. Every returned core is unsat with the clauses.
static void tst_random_cores() {
    random_gen rand(17);
    unsigned num_cores = 0;
    for (unsigned round = 0; round < 300; ++round) {
        ast_manager m;
        reg_decl_plugins(m);
        params_ref p;
        ref<solver> s = mk_inc_sat_solver(m, p);
        unsigned num_vars = 2 + rand(4);
        expr_ref_vector vars(m);
        for (unsigned v = 0; v < num_vars; ++v)
            vars.push_back(m.mk_const(symbol(v), m.mk_bool_sort()));
        auto random_literal = [&]() {
            expr* v = vars.get(rand(num_vars));
            return expr_ref(rand(2) == 0 ? m.mk_not(v) : v, m);
        };
        expr_ref_vector clauses(m);
        auto add_clause = [&](unsigned size) {
            expr_ref_vector literals(m);
            for (unsigned i = 0; i < size; ++i)
                literals.push_back(random_literal());
            clauses.push_back(m.mk_or(literals));
            s->assert_expr(clauses.back());
        };
        for (unsigned i = rand(num_vars + 1); i-- > 0; )
            add_clause(1 + rand(3));
        for (unsigned query = 0; query < 4; ++query) {
            if (rand(2) == 0)
                add_clause(1);
            expr_ref_vector assumptions(m);
            for (unsigned i = 1 + rand(num_vars); i-- > 0; )
                assumptions.push_back(random_literal());
            if (s->check_sat(assumptions) != l_false)
                continue;
            expr_ref_vector core(m);
            s->get_unsat_core(core);
            ref<solver> checker = mk_inc_sat_solver(m, p);
            checker->assert_expr(clauses);
            ENSURE(checker->check_sat(core) == l_false);
            ++num_cores;
        }
    }
    ENSURE(num_cores > 0);
}

void tst_sat_unsat_core() {
    tst_assumption_false_at_level_0();
    tst_random_cores();
}
