#include "ast/reg_decl_plugins.h"
#include "solver/solver_pool.h"
#include "smt/smt_solver.h"


void tst_cube_clause() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref p;
    lbool r;
    ref<solver> solver = mk_smt_solver(m, p, symbol::null);

    expr_ref a(m.mk_const(symbol("a"), m.mk_bool_sort()), m);
    expr_ref b(m.mk_const(symbol("b"), m.mk_bool_sort()), m);
    expr_ref c(m.mk_const(symbol("c"), m.mk_bool_sort()), m);
    expr_ref d(m.mk_const(symbol("d"), m.mk_bool_sort()), m);
    expr_ref e(m.mk_const(symbol("e"), m.mk_bool_sort()), m);
    expr_ref f(m.mk_const(symbol("f"), m.mk_bool_sort()), m);
    expr_ref g(m.mk_const(symbol("g"), m.mk_bool_sort()), m);
    expr_ref fml(m);
    fml = m.mk_not(m.mk_and(a, b));
    solver->assert_expr(fml);
    fml = m.mk_not(m.mk_and(c, d));
    solver->assert_expr(fml);
    fml = m.mk_not(m.mk_and(e, f));
    solver->assert_expr(fml);
    expr_ref_vector cube(m), clause(m), core(m);
    r = solver->check_sat(cube);
    std::cout << r << "\n";
    cube.push_back(a);
    r = solver->check_sat(cube);
    std::cout << r << "\n";
    cube.push_back(c);
    cube.push_back(e);
    r = solver->check_sat(cube);
    std::cout << r << "\n";
    clause.push_back(b);
    vector<expr_ref_vector> clauses;
    clauses.push_back(clause);
    r = solver->check_sat_cc(cube, clauses);
    std::cout << r << "\n";
    core.reset();
    solver->get_unsat_core(core);
    std::cout << core << "\n";
    clause.push_back(d);
    clauses.reset();
    clauses.push_back(clause);
    r = solver->check_sat_cc(cube, clauses);
    std::cout << r << "\n";
    core.reset();
    solver->get_unsat_core(core);
    std::cout << core << "\n";
    clause.push_back(f);
    clauses.reset();
    clauses.push_back(clause);
    r = solver->check_sat_cc(cube, clauses);
    std::cout << r << "\n";
    core.reset();
    solver->get_unsat_core(core);
    std::cout << core << "\n";
    clause.push_back(g);
    clauses.reset();
    clauses.push_back(clause);
    r = solver->check_sat_cc(cube, clauses);
    std::cout << r << "\n";
}
