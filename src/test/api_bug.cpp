
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include<stdio.h>
#include"z3.h"

void tst_api_bug() {
    unsigned vmajor, vminor, vbuild, vrevision;

    Z3_get_version(&vmajor, &vminor, &vbuild, &vrevision);

    printf("Using Z3 Version %u.%u (build %u, revision %u)\n", vmajor, vminor, vbuild, vrevision);


    Z3_config  cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "MODEL", "true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_sort is = Z3_mk_int_sort(ctx);
    Z3_sort ss = Z3_mk_set_sort(ctx, is);
    Z3_ast e = Z3_mk_empty_set(ctx, is);
    // { 42 }
    Z3_ast fortytwo = Z3_mk_set_add(ctx, e, Z3_mk_int(ctx, 42, is));
    // { 42, 43 }
    Z3_ast fortythree = Z3_mk_set_add(ctx, fortytwo, Z3_mk_int(ctx, 43, is));
    // { 42 } U { 42, 43 }

    Z3_ast uargs[2] = { fortytwo, fortythree };
    Z3_ast u = Z3_mk_set_union(ctx, 2, uargs);

    Z3_symbol sym = Z3_mk_string_symbol(ctx, "mySet");
    Z3_ast sc = Z3_mk_const(ctx, sym, ss);
    Z3_ast c = Z3_mk_eq(ctx, sc, u);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, c);

    printf("result %d\n", Z3_solver_check(ctx, s));
    Z3_model m = Z3_solver_get_model(ctx, s);
    Z3_string ms = Z3_model_to_string(ctx, m);
    printf("model : %s\n", ms);
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);    
}


