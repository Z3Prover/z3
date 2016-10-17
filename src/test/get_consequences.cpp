/*++
Copyright (c) 2016 Microsoft Corporation

--*/

#include "inc_sat_solver.h"
#include "bv_decl_plugin.h"
#include "datatype_decl_plugin.h"
#include "reg_decl_plugins.h"
#include "ast_pp.h"
#include "dt2bv.h"
//include 

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

static void test2() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);

    datatype_decl_plugin& dt = static_cast<datatype_decl_plugin>(*m.get_plugin(m.get_family_id("datatype")));
    sort_ref_vector new_sorts(m);
    constructor_decl* R = mk_constructor_decl(symbol("R"), symbol("is-R"), 0, 0);
    constructor_decl* G = mk_constructor_decl(symbol("G"), symbol("is-G"), 0, 0);
    constructor_decl* B = mk_constructor_decl(symbol("B"), symbol("is-B"), 0, 0);
    constructor_decl* constrs[3] = { R, G, B };
    datatype_decl const* enum_sort = mk_datatype_decl(symbol("RGB"), 3, constrs);
    VERIFY(dt.mk_datatypes(1, &enum_sort, new_sorts));    
    del_constructor_decls(3, constrs);
    sort* rgb = new_sorts[0].get();

    expr_ref x = mk_const(m, "x", rgb), y = mk_const(m, "y", rgb), z = mk_const(m, "z", rgb);
    ptr_vector<func_decl> const& enums = dt.geet_datatype_constructors(rgb);
    expr_ref r = expr_ref(m.mk_const(enums[0], m), m), g = expr_ref(m.mk_const(enums[1], m), m), b = expr_ref(m.mk_const(enums[2], m), m);

    goal_ref g = alloc(goal, m);
    g->assert_expr(m.mk_not(m.mk_eq(x, r)));
    g->assert_expr(m.mk_not(m.mk_eq(x, b)));
    g->display(std::cout);
    tactic_ref dt2bv = mk_dt2bv_tactic(m);
    goal_ref_buffer result;
    model_converter_ref mc;
    proof_converter_ref pc;
    expr_dependency_ref core;
    (*dt2bv)(g, result, mc, pc, core);
    model_ref mdl1 = alloc(model, m);
    model_ref mdl2 = (*mc)(*mdl1);
    expr_ref val(m);
    mdl2->eval(x, val);
    std::cout << val << "\n";
    
}

void tst_get_consequences() {
    test1();
    test2();


}
