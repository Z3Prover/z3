/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_ast.cpp

Abstract:

    Test AST module

Author:

    Leonardo de Moura (leonardo) 2006-09-29.

Revision History:

--*/
#include "ast/ast.h"
#include "ast/ast_smt2_pp.h"
#include "ast/reg_decl_plugins.h"
#include <sstream>

static void tst1() {
    ast_manager m;
    
    family_id fid = m.get_basic_family_id();

    sort_ref b(m.mk_bool_sort(), m);
    expr_ref a(m.mk_const(symbol("a"), b.get()), m);
    expr_ref c(m.mk_const(symbol("c"), b.get()), m);
    expr_ref i1(m.mk_app(fid, OP_AND, a.get(), c.get()), m);
    expr_ref i2(m.mk_app(fid, OP_AND, a.get(), c.get()), m);
    expr_ref i3(m.mk_app(fid, OP_OR, a.get(), c.get()), m);
    ENSURE(i1.get() == i2.get());
    ENSURE(i1.get() != i3.get());

    // TODO use smart pointers to track references
//     ast_manager m;
//     ast_ref<numeral_ast> n1(m.mk_numeral(rational(2,3)), m);
//     ast_ref<numeral_ast> n2(m.mk_numeral(rational(2,3)), m);
//     ENSURE(n1 == n2);
//     ast_ref<numeral_ast> n3(m.mk_numeral(rational(1,2)), m);
//     ENSURE(n1 != n3);
//     ast_ref<var_ast> v1 (m.mk_var(1), m);
//     ast_ref<var_ast> v2 (m.mk_var(2), m);
//     ast_ref<var_ast> v3 (m.mk_var(1), m);
//     ENSURE(v1 != v2);
//     ENSURE(v1 == v3);
//     TRACE(ast, tout << "resetting v1\n";);
//     v1.reset();
//     TRACE(ast, tout << "overwriting v3\n";);
//     v3 = v2;

//     ast_ref<type_decl_ast> t1(m.mk_type_decl(symbol("int"), 0), m);
//     ast_ref<type_ast> i(m.mk_type(t1.get(), 0, 0), m);

//     ast_ref<const_decl_ast> foo_decl(m.mk_const_decl(symbol("foo"), i.get(), i.get()), m);
//     ast_ref<const_decl_ast> x_decl(m.mk_const_decl(symbol("x"), i.get()), m);

//     ast_ref<const_ast> x(m.mk_const(x_decl.get()), m);
//     ast_ref<const_ast> foo_x(m.mk_const(foo_decl.get(), x.get()), m);
//     ast_ref<const_ast> foo_foo_x(m.mk_const(foo_decl.get(), foo_x.get()), m);
//     ast_ref<const_ast> foo_foo_x2(m.mk_const(foo_decl.get(), m.mk_const(foo_decl.get(), m.mk_const(x_decl.get()))), m);
//     ENSURE(foo_foo_x2 == foo_foo_x);
}

static void tst2() {
//     ast_manager m;
//     ast_vector<ast> m_nodes(m);

//     m_nodes.push_back(m.mk_var(1));
//     m_nodes.push_back(m.mk_numeral(rational(1,2)));
//     m_nodes.push_back(m.mk_var(2));
//     m_nodes[1] = m.mk_var(3);
//     ENSURE(m_nodes[1]->kind() == AST_VAR);
//     ENSURE(m_nodes.get(1)->kind() == AST_VAR);
//     m_nodes.pop_back();
//     ENSURE(m_nodes.size() == 2);
//     ENSURE(!m_nodes.empty());
//     m_nodes.set(1, m.mk_var(4));
//     ENSURE(&(m_nodes.get_manager()) == &m);
}

static void tst3() {
//     ast_manager m;
//     ast_ref<> n(m.mk_var(1), m);
//     n = m.mk_var(1);
//     TRACE(ast, tout << n->get_id() << "\n";);
}

static void tst4() {
//     ast_manager m;
//     ast_ref<> n1(m.mk_var(1), m);
//     ast_ref<> n2(m.mk_var(2), m);
//     ast_ref<> n3(m.mk_var(3), m);
//     weak_memoize<int> wm1;
// #ifdef Z3DEBUG
//     int r;
// #endif
//     ENSURE(!wm1.find(n1, r));
//     wm1.insert(n2, 10);
//     ENSURE(!wm1.find(n1, r));
//     ENSURE(wm1.find(n2, r) && r == 10);
//     wm1.insert(n2, 20);
//     ENSURE(!wm1.find(n1, r));
//     ENSURE(wm1.find(n2, r) && r == 20);
//     wm1.insert(n1, 0);
//     ENSURE(wm1.find(n1, r) && r == 0);
//     ENSURE(wm1.find(n2, r) && r == 20);
}

static void tst5() {
    ast_manager m;
    sort_ref b(m.mk_bool_sort(), m);
    expr_ref a1(m.mk_const(symbol("a1"), b.get()), m);
    expr_ref a2(m.mk_const(symbol("a2"), b.get()), m);
    expr_array arr1;
    expr_array arr2;
    expr_array arr3;
    m.push_back(arr1, a1);
    m.push_back(arr1, a2);
    m.pop_back(arr1, arr2);
    m.set(arr2, 0, a2, arr3);
    ENSURE(m.size(arr1) == 2);
    ENSURE(m.size(arr2) == 1);
    ENSURE(m.size(arr3) == 1);
    ENSURE(m.get(arr1, 0) == a1);
    ENSURE(m.get(arr1, 1) == a2);
    ENSURE(m.get(arr2, 0) == a1);
    ENSURE(m.get(arr3, 0) == a2);
    m.del(arr1);
    m.del(arr2);
    m.del(arr3);
}


struct foo {
    unsigned       m_id; 
    unsigned short m_ref_count;
    unsigned char  m_kind;
    unsigned char  m_arity;
    bool           m_val1:1;
    bool           m_val2:1;
};

static void tst_smt2_format_order(char const* name, unsigned arity) {
    ast_manager m;
    reg_decl_plugins(m);
    sort* b = m.mk_bool_sort();
    expr_ref a(m.mk_const(symbol("a"), b), m);
    expr_ref c(m.mk_const(symbol("c"), b), m);
    sort* domain[] = { b, b };
    expr* args[] = { a, c };
    func_decl_ref decl(m.mk_func_decl(symbol(name), arity, domain, b), m);
    expr_ref e(m.mk_app(decl, arity, args), m);
    smt2_pp_environment_dbg env(m);
    params_ref p;
    format_ns::format_ref result(format_ns::fm(m));
    sbuffer<symbol> var_names;
    mk_smt2_format(e, env, p, 0, nullptr, result, var_names);

    app* composed = to_app(result->get_arg(1));
    app* heading = to_app(composed->get_arg(0));
    app* body = to_app(composed->get_arg(1));
    app* elements = to_app(body->get_arg(0));
    app* rest = to_app(elements->get_arg(strlen(name) > 16 ? 0 : 2));
    app* close = to_app(elements->get_arg(elements->get_num_args() - 1));
    ENSURE(heading->get_id() < rest->get_id());
    ENSURE(heading->get_id() < body->get_id());
    ENSURE(rest->get_id() < close->get_id());

    std::ostringstream out;
    ast_smt2_pp(out, e, env);
    std::string expected = std::string("(") + name + " a" + (arity == 2 ? " c)" : ")");
    ENSURE(out.str() == expected);
}

void tst_ast() {
    TRACE(ast, 
          tout << "sizeof(ast):  " << sizeof(ast) << "\n";
          tout << "sizeof(expr): " << sizeof(expr) << "\n";
          tout << "sizeof(app): " << sizeof(app) << "\n";
          );
    TRACE(ast, tout << "sizeof(foo): " << sizeof(foo) << "\n";);
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst_smt2_format_order("f", 1);
    tst_smt2_format_order("f", 2);
    tst_smt2_format_order("long_function_name", 1);
    tst_smt2_format_order("long_function_name", 2);
}

