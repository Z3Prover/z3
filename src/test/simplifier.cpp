#ifdef _WINDOWS
#include "z3.h"
#include "z3_private.h"
#include <iostream>
#include "util.h"
#include "trace.h"


static void ev_const(Z3_context ctx, Z3_ast e) {
    Z3_ast r = Z3_simplify(ctx, e);
    TRACE("simplifier", 
          tout << Z3_ast_to_string(ctx, e) << " -> ";
          tout << Z3_ast_to_string(ctx, r) << "\n";);
    Z3_ast_kind k = Z3_get_ast_kind(ctx, r);
    SASSERT(k == Z3_NUMERAL_AST ||
            (k == Z3_APP_AST && 
             (Z3_OP_TRUE  == Z3_get_decl_kind(ctx,Z3_get_app_decl(ctx, Z3_to_app(ctx, r))) ||
              Z3_OP_FALSE == Z3_get_decl_kind(ctx,Z3_get_app_decl(ctx, Z3_to_app(ctx, r))))));
}

static void test_bv() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort bv1 = Z3_mk_bv_sort(ctx,1);
    Z3_sort bv2 = Z3_mk_bv_sort(ctx,2);
    Z3_sort bv72 = Z3_mk_bv_sort(ctx,72);
    Z3_ast bit1_1 = Z3_mk_numeral(ctx, "1", bv1);
    Z3_ast bit3_2 = Z3_mk_numeral(ctx, "3", bv2);

    Z3_ast e = Z3_mk_eq(ctx, bit3_2, Z3_mk_sign_ext(ctx, 1, bit1_1));
    SASSERT(Z3_simplify(ctx, e) == Z3_mk_true(ctx));
    TRACE("simplifier", tout << Z3_ast_to_string(ctx, e) << "\n";);

    Z3_ast b12 = Z3_mk_numeral(ctx, "12", bv72);
    Z3_ast b13 = Z3_mk_numeral(ctx, "13", bv72);

    ev_const(ctx, Z3_mk_bvnot(ctx,b12));
    ev_const(ctx, Z3_mk_bvnot(ctx,Z3_simplify(ctx, Z3_mk_bvnot(ctx, b12))));
    ev_const(ctx, Z3_mk_bvand(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvor(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvxor(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvnand(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvnor(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvxnor(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvneg(ctx,b12));
    ev_const(ctx, Z3_mk_bvadd(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsub(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvmul(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvudiv(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsdiv(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsrem(ctx,b12,b13));

    ev_const(ctx, Z3_mk_bvuge(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsge(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvugt(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsgt(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvule(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvult(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvsle(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvslt(ctx,b12,b13));

    ev_const(ctx, Z3_mk_concat(ctx,b12,b13));
    ev_const(ctx, Z3_mk_extract(ctx,43,1,b13));
    ev_const(ctx, Z3_mk_sign_ext(ctx,33,b13));
    ev_const(ctx, Z3_mk_zero_ext(ctx,33,b13));
    ev_const(ctx, Z3_mk_bvshl(ctx,b12,b13));

    ev_const(ctx, Z3_mk_bvshl(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvlshr(ctx,b12,b13));
    ev_const(ctx, Z3_mk_bvashr(ctx,b12,b13));

    ev_const(ctx, Z3_mk_rotate_left(ctx,21,b13));
    ev_const(ctx, Z3_mk_rotate_right(ctx,21,b13));

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

static void test_datatypes() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort int_ty, int_list;
    Z3_func_decl nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl;
    Z3_ast nil, l1;    

    int_ty = Z3_mk_int_sort(ctx);

    int_list = Z3_mk_list_sort(ctx, Z3_mk_string_symbol(ctx, "int_list"), int_ty,
                               &nil_decl, &is_nil_decl, &cons_decl, &is_cons_decl, &head_decl, &tail_decl);
                    
    nil = Z3_mk_app(ctx, nil_decl, 0, 0);

    Z3_ast a = Z3_simplify(ctx, Z3_mk_app(ctx, is_nil_decl, 1, &nil));
    SASSERT(a == Z3_mk_true(ctx));

    a = Z3_simplify(ctx, Z3_mk_app(ctx, is_cons_decl, 1, &nil));
    SASSERT(a == Z3_mk_false(ctx));

    Z3_ast one = Z3_mk_numeral(ctx, "1", int_ty);
    Z3_ast args[2] = { one, nil };
    l1 = Z3_mk_app(ctx, cons_decl, 2, args);
    SASSERT(nil == Z3_simplify(ctx, Z3_mk_app(ctx, tail_decl, 1, &l1))); 
    SASSERT(one == Z3_simplify(ctx, Z3_mk_app(ctx, head_decl, 1, &l1))); 

    SASSERT(Z3_mk_false(ctx) == Z3_simplify(ctx, Z3_mk_eq(ctx, nil, l1)));
    
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}


static void test_skolemize_bug() {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "MODEL", "true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort Real = Z3_mk_real_sort(ctx);
    Z3_ast x = Z3_mk_bound(ctx, 0, Real);
    Z3_symbol x_name = Z3_mk_string_symbol(ctx, "x");
    Z3_ast y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "y"), Real);
    Z3_ast xp = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "xp"), Real);
    Z3_ast n0 = Z3_mk_numeral(ctx, "0", Real);
    Z3_ast n1 = Z3_mk_numeral(ctx, "1", Real);
    Z3_ast args1[2] = { x, n1 };
    Z3_ast args2[2] = { x, y };
    Z3_ast args[2] = { Z3_mk_eq(ctx, Z3_mk_add(ctx, 2, args1), xp), 
                       Z3_mk_ge(ctx, Z3_mk_add(ctx, 2, args2), n0) };
    Z3_ast f  = Z3_mk_and(ctx, 2, args);
    Z3_ast f2 = Z3_mk_exists(ctx, 0, 0, 0, 1, &Real, &x_name, f);
    std::cout << Z3_ast_to_string(ctx, f2) << "\n";
    Z3_ast f3 = Z3_simplify(ctx, f2);
    std::cout << Z3_ast_to_string(ctx, f3) << "\n";

}


static void test_bool() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);

    Z3_ast a = Z3_simplify(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, Z3_mk_false(ctx), Z3_mk_true(ctx))));
    Z3_ast b = Z3_simplify(ctx, Z3_mk_not(ctx, Z3_mk_iff(ctx, Z3_mk_false(ctx), Z3_mk_true(ctx))));
    SASSERT(Z3_mk_true(ctx) == a);
    SASSERT(Z3_mk_true(ctx) == b);
    TRACE("simplifier", tout << Z3_ast_to_string(ctx, a) << "\n";);
    TRACE("simplifier", tout << Z3_ast_to_string(ctx, b) << "\n";);

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

static void test_array() {
    
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort i = Z3_mk_int_sort(ctx);
    Z3_ast n1 = Z3_mk_numeral(ctx, "1", i);
    Z3_ast n2 = Z3_mk_numeral(ctx, "2", i);
    Z3_ast n3 = Z3_mk_numeral(ctx, "3", i);
    Z3_ast n4 = Z3_mk_numeral(ctx, "4", i);
    Z3_ast s1 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"s1"), i);
    Z3_ast s2 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"s2"), i);
    
    Z3_ast c1 = Z3_mk_const_array(ctx, i, n1);
    Z3_ast x1  = Z3_mk_store(ctx, Z3_mk_store(ctx, c1, n2, n3), n1, n4);
    Z3_ast x2  = Z3_mk_store(ctx, Z3_mk_store(ctx, c1, n1, n4), n2, n3);
    Z3_ast x3  = Z3_mk_store(ctx, Z3_mk_store(ctx, c1, s1, n1), n2, n3);
    Z3_ast x4  = Z3_mk_store(ctx, Z3_mk_store(ctx, Z3_mk_store(ctx, c1, n2, n3), n1, n4), n2, n3);
    Z3_ast xs[4] = { x1, x2, x3, x4};
    Z3_ast exy  = Z3_mk_eq(ctx, x2, x1);
    Z3_ast rxy  = Z3_simplify(ctx, exy);

    TRACE("simplifier", tout << Z3_ast_to_string(ctx, rxy) << "\n";);
    TRACE("simplifier", tout << Z3_ast_to_string(ctx, Z3_simplify(ctx, Z3_mk_eq(ctx, x2, x3))) << "\n";);
    // SASSERT(rxy == Z3_mk_true(ctx));
    // SASSERT(Z3_simplify(ctx, Z3_mk_eq(ctx, x2, x3)) == Z3_mk_false(ctx));
    
    for (unsigned i = 0; i < 4; ++i) {
        for (unsigned j = 0; j < 4; ++j) {
            exy  = Z3_mk_eq(ctx, xs[i], xs[j]);
            rxy  = Z3_simplify(ctx, exy);
            
            TRACE("simplifier", 
                  tout << Z3_ast_to_string(ctx, exy);
                  tout << " -> " << Z3_ast_to_string(ctx, rxy) << "\n";  
                  );
        }
    }

    Z3_ast sel1 = Z3_mk_select(ctx, x1, n1);
    Z3_ast sel2 = Z3_mk_select(ctx, x1, n4);

    TRACE("simplifier", 
          tout << Z3_ast_to_string(ctx,  Z3_simplify(ctx, sel1)) << "\n";
          tout << Z3_ast_to_string(ctx,  Z3_simplify(ctx, sel2)) << "\n";
          );

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void tst_simplifier() {

    test_array();
    test_bv();
    test_datatypes();
    test_bool();
    test_skolemize_bug();
}

#else
void tst_simplifier() {
}
#endif
