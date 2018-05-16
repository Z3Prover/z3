#include "ast/reg_decl_plugins.h"
#include "solver/solver_pool.h"
#include "smt/smt_solver.h"

void tst_solver_pool() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref p;
    ref<solver> base = mk_smt_solver(m, p, symbol::null);

    expr_ref a(m.mk_const(symbol("a"), m.mk_bool_sort()), m);
    expr_ref b(m.mk_const(symbol("b"), m.mk_bool_sort()), m);
    expr_ref c(m.mk_const(symbol("c"), m.mk_bool_sort()), m);
    expr_ref d(m.mk_const(symbol("d"), m.mk_bool_sort()), m);
    expr_ref fml(m);
    fml = m.mk_or(a, b);
    base->assert_expr(fml);

    solver_pool pool(base.get(), 3);

    // base solver is cloned so any assertions 
    // added to base after mk_solver() are ignored.
    ref<solver> s1 = pool.mk_solver();
    ref<solver> s2 = pool.mk_solver();
    ref<solver> s3 = pool.mk_solver();
    ref<solver> s4 = pool.mk_solver();
    
    fml = m.mk_and(b, c);
    s1->assert_expr(fml);
    fml = m.mk_and(a, b);
    s2->assert_expr(fml);
    expr_ref_vector asms(m);
    asms.push_back(m.mk_not(a));
    std::cout << base->check_sat(asms) << "\n";
    std::cout << s1->check_sat(asms) << "\n";
    std::cout << s2->check_sat(asms) << "\n";
    std::cout << s3->check_sat(asms) << "\n";
    std::cout << *s1;
    std::cout << *s2;
    std::cout << *base;
}
