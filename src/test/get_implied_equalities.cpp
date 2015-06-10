
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "z3.h"
#include "trace.h"
#include "debug.h"

static Z3_ast mk_var(Z3_context ctx, char const* name, Z3_sort s) {
    return Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), s);
}

static Z3_ast mk_int_var(Z3_context ctx, char const* name) {
    return mk_var(ctx, name, Z3_mk_int_sort(ctx));
}



static void tst_get_implied_equalities1() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_sort int_ty = Z3_mk_int_sort(ctx);
    Z3_ast a = mk_int_var(ctx,"a");
    Z3_ast b = mk_int_var(ctx,"b");
    Z3_ast c = mk_int_var(ctx,"c");
    Z3_ast d = mk_int_var(ctx,"d");
    Z3_func_decl f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx,"f"), 1, &int_ty, int_ty);
    Z3_ast fa = Z3_mk_app(ctx, f, 1, &a);
    Z3_ast fb = Z3_mk_app(ctx, f, 1, &b);
    Z3_ast fc = Z3_mk_app(ctx, f, 1, &c);
    unsigned const num_terms = 7;
    unsigned i;
    Z3_ast terms[7] = { a, b, c, d, fa, fb, fc };
    unsigned class_ids[7] = { 0, 0, 0, 0, 0, 0, 0 };
    Z3_solver solver = Z3_mk_simple_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);
        
    Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, a, b));
    Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, b, d));
    Z3_solver_assert(ctx, solver, Z3_mk_le(ctx, fa, fc));
    Z3_solver_assert(ctx, solver, Z3_mk_le(ctx, fc, d));
    
    Z3_get_implied_equalities(ctx, solver, num_terms, terms, class_ids);
    for (i = 0; i < num_terms; ++i) {
        printf("Class %s |-> %d\n", Z3_ast_to_string(ctx, terms[i]), class_ids[i]);
    }
    SASSERT(class_ids[1] == class_ids[0]);
    SASSERT(class_ids[2] != class_ids[0]);
    SASSERT(class_ids[3] == class_ids[0]);
    SASSERT(class_ids[4] != class_ids[0]);
    SASSERT(class_ids[5] != class_ids[0]);
    SASSERT(class_ids[6] != class_ids[0]);
    SASSERT(class_ids[4] == class_ids[5]);

    printf("asserting b <= f(a)\n");
    Z3_solver_assert(ctx, solver, Z3_mk_le(ctx, b, fa));
    Z3_get_implied_equalities(ctx, solver, num_terms, terms, class_ids);
    for (i = 0; i < num_terms; ++i) {
        printf("Class %s |-> %d\n", Z3_ast_to_string(ctx, terms[i]), class_ids[i]);
    }
    SASSERT(class_ids[1] == class_ids[0]);
    SASSERT(class_ids[2] != class_ids[0]);
    SASSERT(class_ids[3] == class_ids[0]);
    SASSERT(class_ids[4] == class_ids[0]);
    SASSERT(class_ids[5] == class_ids[0]);
    SASSERT(class_ids[6] == class_ids[0]);

    
    Z3_solver_dec_ref(ctx, solver);
    /* delete logical context */
    Z3_del_context(ctx);    
}

static void tst_get_implied_equalities2() {
    enable_trace("after_search");
    enable_trace("get_implied_equalities");
    enable_trace("implied_equalities");
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_solver solver = Z3_mk_simple_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);
    Z3_sort int_ty = Z3_mk_int_sort(ctx);
    Z3_ast a = mk_int_var(ctx,"a");
    Z3_ast b = mk_int_var(ctx,"b");
    Z3_ast one = Z3_mk_numeral(ctx, "1", int_ty);
    Z3_ast two = Z3_mk_numeral(ctx, "2", int_ty);
    Z3_ast x = Z3_mk_const_array(ctx, int_ty, one);
    Z3_ast y = Z3_mk_store(ctx, x, one, a);
    Z3_ast z = Z3_mk_store(ctx, y, two , b);
    Z3_ast u = Z3_mk_store(ctx, x, two , b);
    Z3_ast v = Z3_mk_store(ctx, u, one , a);
    unsigned const num_terms = 5;
    unsigned i;
    Z3_ast terms[5] = { x, y, z, u, v};
    unsigned class_ids[5] = { 0, 0, 0, 0, 0};
    
    Z3_get_implied_equalities(ctx, solver, num_terms, terms, class_ids);
    for (i = 0; i < num_terms; ++i) {
        printf("Class %s |-> %d\n", Z3_ast_to_string(ctx, terms[i]), class_ids[i]);
    }

    SASSERT(class_ids[1] != class_ids[0]);
    SASSERT(class_ids[2] != class_ids[0]);
    SASSERT(class_ids[3] != class_ids[0]);
    SASSERT(class_ids[4] != class_ids[0]);
    SASSERT(class_ids[4] == class_ids[2]);
    SASSERT(class_ids[2] != class_ids[1]);
    SASSERT(class_ids[3] != class_ids[1]);
    SASSERT(class_ids[4] != class_ids[1]);  
    SASSERT(class_ids[3] != class_ids[2]);

    /* delete logical context */
    Z3_solver_dec_ref(ctx, solver);
    Z3_del_context(ctx);    
}

void tst_get_implied_equalities() {
    tst_get_implied_equalities1();
    tst_get_implied_equalities2();    
}
