/*++
Copyright (c) 2016 Microsoft Corporation

--*/

#include "inc_sat_solver.h"
#include "bv_decl_plugin.h"
#include "datatype_decl_plugin.h"
#include "reg_decl_plugins.h"
#include "ast_pp.h"
#include "dt2bv_tactic.h"
#include "tactic.h"
#include "model_smt2_pp.h"
#include "fd_solver.h"

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
    datatype_util dtutil(m);
    params_ref p;

    datatype_decl_plugin & dt = *(static_cast<datatype_decl_plugin*>(m.get_plugin(m.get_family_id("datatype"))));
    sort_ref_vector new_sorts(m);
    constructor_decl* R = mk_constructor_decl(symbol("R"), symbol("is-R"), 0, 0);
    constructor_decl* G = mk_constructor_decl(symbol("G"), symbol("is-G"), 0, 0);
    constructor_decl* B = mk_constructor_decl(symbol("B"), symbol("is-B"), 0, 0);
    constructor_decl* constrs[3] = { R, G, B };
    datatype_decl * enum_sort = mk_datatype_decl(symbol("RGB"), 3, constrs);
    VERIFY(dt.mk_datatypes(1, &enum_sort, new_sorts));    
    del_constructor_decls(3, constrs);
    sort* rgb = new_sorts[0].get();

    expr_ref x = mk_const(m, "x", rgb), y = mk_const(m, "y", rgb), z = mk_const(m, "z", rgb);
    ptr_vector<func_decl> const& enums = *dtutil.get_datatype_constructors(rgb);
    expr_ref r = expr_ref(m.mk_const(enums[0]), m);
    expr_ref g = expr_ref(m.mk_const(enums[1]), m);
    expr_ref b = expr_ref(m.mk_const(enums[2]), m);
    expr_ref val(m);

    // Eliminate enumeration data-types:
    goal_ref gl = alloc(goal, m);
    gl->assert_expr(m.mk_not(m.mk_eq(x, r)));
    gl->assert_expr(m.mk_not(m.mk_eq(x, b)));
    gl->display(std::cout);
    obj_map<func_decl, func_decl*> tr;
    obj_map<func_decl, func_decl*> rev_tr;
    ref<tactic> dt2bv = mk_dt2bv_tactic(m, p, &tr);
    goal_ref_buffer result;
    model_converter_ref mc;
    proof_converter_ref pc;
    expr_dependency_ref core(m);
    (*dt2bv)(gl, result, mc, pc, core);

    // Collect translations from enumerations to bit-vectors
    obj_map<func_decl, func_decl*>::iterator it = tr.begin(), end = tr.end();
    for (; it != end; ++it) {
        rev_tr.insert(it->m_value, it->m_key);
    }

    // Create bit-vector implication problem
    val = m.mk_const(tr.find(to_app(x)->get_decl()));
    std::cout << val << "\n";
    ptr_vector<expr> fmls;
    result[0]->get_formulas(fmls);    
    ref<solver> solver = mk_inc_sat_solver(m, p);
    for (unsigned i = 0; i < fmls.size(); ++i) {
        solver->assert_expr(fmls[i]);
    }
    expr_ref_vector asms(m), vars(m), conseq(m);
    vars.push_back(val);

    // retrieve consequences
    solver->get_consequences(asms, vars, conseq);
    
    // Convert consequences over bit-vectors to enumeration types.
    std::cout << conseq << "\n";
    for (unsigned i = 0; i < conseq.size(); ++i) {
        expr* a, *b, *u, *v;
        func_decl* f;
        rational num;
        unsigned bvsize;
        VERIFY(m.is_implies(conseq[i].get(), a, b));
        if (m.is_eq(b, u, v) && rev_tr.find(to_app(u)->get_decl(), f) && bv.is_numeral(v, num, bvsize)) {
            SASSERT(num.is_unsigned());
            expr_ref head(m);
            head = m.mk_eq(m.mk_const(f), m.mk_const(enums[num.get_unsigned()]));
            conseq[i] = m.mk_implies(a, head);
        }
    }
    std::cout << conseq << "\n";
}

void test3() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    datatype_util dtutil(m);
    params_ref p;

    datatype_decl_plugin & dt = *(static_cast<datatype_decl_plugin*>(m.get_plugin(m.get_family_id("datatype"))));
    sort_ref_vector new_sorts(m);
    constructor_decl* R = mk_constructor_decl(symbol("R"), symbol("is-R"), 0, 0);
    constructor_decl* G = mk_constructor_decl(symbol("G"), symbol("is-G"), 0, 0);
    constructor_decl* B = mk_constructor_decl(symbol("B"), symbol("is-B"), 0, 0);
    constructor_decl* constrs[3] = { R, G, B };
    datatype_decl * enum_sort = mk_datatype_decl(symbol("RGB"), 3, constrs);
    VERIFY(dt.mk_datatypes(1, &enum_sort, new_sorts));    
    del_constructor_decls(3, constrs);
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
    VERIFY(l_false == fd_solver->check_sat(0,0));
    fd_solver->pop(1);

    VERIFY(l_true == fd_solver->get_consequences(asms, vars, conseq));

    std::cout << conseq << "\n";
    conseq.reset();

    model_ref mr;
    fd_solver->get_model(mr);
    model_smt2_pp(std::cout << "model:\n", m, *mr.get(), 0);

    VERIFY(l_true == fd_solver->check_sat(0,0));
    fd_solver->get_model(mr);
    SASSERT(mr.get());
    model_smt2_pp(std::cout, m, *mr.get(), 0);

}

void tst_get_consequences() {
    test1();
    test2();
    test3();

}
