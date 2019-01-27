/*++
Copyright (c) 2016 Microsoft Corporation

--*/

#include "sat/sat_solver/inc_sat_solver.h"
#include "ast/bv_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "tactic/bv/dt2bv_tactic.h"
#include "tactic/tactic.h"
#include "model/model_smt2_pp.h"
#include "tactic/fd_solver/fd_solver.h"

static expr_ref mk_const(ast_manager& m, char const* name, sort* s) {
    return expr_ref(m.mk_const(symbol(name), s), m);
}

static expr_ref mk_bool(ast_manager& m, char const* name) {
    return expr_ref(m.mk_const(symbol(name), m.mk_bool_sort()), m);
}

static expr_ref mk_bv(ast_manager& m, char const* name, unsigned sz) {
    bv_util bv(m);
    return expr_ref(m.mk_const(symbol(name), bv.mk_sort(sz)), m);
}

static void test1() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    params_ref p;

    ref<solver> solver = mk_inc_sat_solver(m, p);
    expr_ref a = mk_bool(m, "a"), b = mk_bool(m, "b"), c = mk_bool(m, "c");
    expr_ref ba = mk_bv(m, "ba", 3), bb = mk_bv(m, "bb", 3), bc = mk_bv(m, "bc", 3);

    solver->assert_expr(m.mk_implies(a, b));
    solver->assert_expr(m.mk_implies(b, c));
    expr_ref_vector asms(m), vars(m), conseq(m);
    asms.push_back(a);
    vars.push_back(b);
    vars.push_back(c);
    vars.push_back(bb);
    vars.push_back(bc);
    solver->assert_expr(m.mk_eq(ba, bc));
    solver->assert_expr(m.mk_eq(bv.mk_numeral(2, 3), ba));
    solver->get_consequences(asms, vars, conseq);

    std::cout << conseq << "\n";
}


void test2() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    datatype_util dtutil(m);
    params_ref p;

    datatype_decl_plugin & dt = *(static_cast<datatype_decl_plugin*>(m.get_plugin(m.get_family_id("datatype"))));
    sort_ref_vector new_sorts(m);
    constructor_decl* R = mk_constructor_decl(symbol("R"), symbol("is-R"), 0, nullptr);
    constructor_decl* G = mk_constructor_decl(symbol("G"), symbol("is-G"), 0, nullptr);
    constructor_decl* B = mk_constructor_decl(symbol("B"), symbol("is-B"), 0, nullptr);
    constructor_decl* constrs[3] = { R, G, B };
    datatype_decl * enum_sort = mk_datatype_decl(dtutil, symbol("RGB"), 0, nullptr, 3, constrs);
    VERIFY(dt.mk_datatypes(1, &enum_sort, 0, nullptr, new_sorts));
    sort* rgb = new_sorts[0].get();

    expr_ref x = mk_const(m, "x", rgb), y = mk_const(m, "y", rgb), z = mk_const(m, "z", rgb);
    ptr_vector<func_decl> const& enums = *dtutil.get_datatype_constructors(rgb);
    expr_ref r = expr_ref(m.mk_const(enums[0]), m);
    expr_ref g = expr_ref(m.mk_const(enums[1]), m);
    expr_ref b = expr_ref(m.mk_const(enums[2]), m);

    ref<solver> fd_solver = mk_fd_solver(m, p);
    fd_solver->assert_expr(m.mk_not(m.mk_eq(x, r)));
    fd_solver->assert_expr(m.mk_not(m.mk_eq(x, b)));

    expr_ref_vector asms(m), vars(m), conseq(m);
    vars.push_back(x);
    vars.push_back(y);

    VERIFY(l_true == fd_solver->get_consequences(asms, vars, conseq));
    std::cout << conseq << "\n";
    conseq.reset();

    fd_solver->push();
    fd_solver->assert_expr(m.mk_not(m.mk_eq(x, g)));
    VERIFY(l_false == fd_solver->check_sat(0,nullptr));
    fd_solver->pop(1);

    VERIFY(l_true == fd_solver->get_consequences(asms, vars, conseq));

    std::cout << conseq << "\n";
    conseq.reset();

    model_ref mr;
    fd_solver->get_model(mr);
    model_smt2_pp(std::cout << "model:\n", m, *mr.get(), 0);

    VERIFY(l_true == fd_solver->check_sat(0,nullptr));
    fd_solver->get_model(mr);
    ENSURE(mr.get());
    model_smt2_pp(std::cout, m, *mr.get(), 0);

}

void tst_get_consequences() {
    test1();
    test2();
}
