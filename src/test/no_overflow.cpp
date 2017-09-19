/*++
Copyright (c) 2009 Microsoft Corporation

Module Name:

    no_overflow.cpp

Abstract:

    Test non-overflowing checks for arithmetic.

Author:

    Yannick Moy (t-yanmoy) 2009-02-17.

Revision History:

--*/
#ifdef _WINDOWS

#include "api/z3.h"
#include "util/trace.h"
#include "util/rational.h"

#define TEST(TEST_NAME, TEST_OUTCOME, NEG_TEST_OUTCOME) \
    do { \
        if (TEST_NAME != NULL) \
        { \
            Z3_solver_push(ctx, s);            \
            Z3_solver_assert(ctx, s, TEST_NAME);     \
            ENSURE(Z3_solver_check(ctx, s) == TEST_OUTCOME);     \
            Z3_solver_pop(ctx, s, 1);                              \
            \
            Z3_solver_push(ctx, s);                            \
            Z3_solver_assert(ctx, s, Z3_mk_not(ctx, TEST_NAME)); \
            ENSURE(Z3_solver_check(ctx, s) == NEG_TEST_OUTCOME);  \
            Z3_solver_pop(ctx, s, 1);                               \
        } \
    } while (0)

#define TEST_NO_OVERFLOW TEST(test_ovfl, Z3_L_TRUE, Z3_L_FALSE)
#define TEST_OVERFLOW    TEST(test_ovfl, Z3_L_FALSE, Z3_L_TRUE)

#define TEST_NO_OVERFLOW_IFF(COND) \
    do { \
    if (COND) { \
        TEST_NO_OVERFLOW; \
    } \
    else { \
        TEST_OVERFLOW; \
    } \
    } while (0) 

#define TEST_NO_UNDERFLOW TEST(test_udfl, Z3_L_TRUE, Z3_L_FALSE)
#define TEST_UNDERFLOW    TEST(test_udfl, Z3_L_FALSE, Z3_L_TRUE)

#define TEST_NO_UNDERFLOW_IFF(COND) \
    do { \
    if (COND) { \
        TEST_NO_UNDERFLOW; \
    } \
    else { \
        TEST_UNDERFLOW; \
    } \
    } while (0) 

#define TEST_ANY(TEST_NAME) \
    do { \
        Z3_solver_push(ctx, s);            \
        Z3_solver_assert(ctx, s, TEST_NAME);          \
        Z3_solver_check(ctx, s); /* ignore result of check */     \
        Z3_solver_pop(ctx, s, 1);                                         \
    } while (0)

#define TEST_ANY_OVERFLOW  TEST_ANY(test_ovfl)
#define TEST_ANY_UNDERFLOW TEST_ANY(test_udfl)

Z3_ast mk_min(Z3_context ctx, Z3_sort bv, bool is_signed) {
    unsigned bvsize = Z3_get_bv_sort_size(ctx, bv);
    if (! is_signed) return Z3_mk_numeral(ctx, "0", bv);
    unsigned sz = bvsize - 1;
    rational min_bound = power(rational(2), sz);
    min_bound.neg();
    return Z3_mk_numeral(ctx, min_bound.to_string().c_str(), bv);
}

Z3_ast mk_max(Z3_context ctx, Z3_sort bv, bool is_signed) {
    unsigned bvsize = Z3_get_bv_sort_size(ctx, bv);
    unsigned sz = is_signed ? bvsize - 1 : bvsize;
    rational max_bound = power(rational(2), sz);
    --max_bound;
    return Z3_mk_numeral(ctx, max_bound.to_string().c_str(), bv);
}

void test_add(unsigned bvsize, bool is_signed) {

    TRACE("no_overflow", tout << "test_add: bvsize = " << bvsize << ", is_signed = " << is_signed << "\n";);

    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    Z3_sort bv = Z3_mk_bv_sort(ctx, bvsize);

    Z3_ast min = mk_min(ctx, bv, is_signed);
    Z3_ast max = mk_max(ctx, bv, is_signed);
    Z3_ast t1;
    Z3_ast t2;
    Z3_ast test_ovfl;
    Z3_ast test_udfl;

    t1 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"x"), bv);
    t2 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"y"), bv);
    test_ovfl = Z3_mk_bvadd_no_overflow(ctx, t1, t2, is_signed);
    test_udfl = is_signed ? Z3_mk_bvadd_no_underflow(ctx, t1, t2) : NULL;

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "0", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "1", bv)));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "0", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "1", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
    TEST_NO_OVERFLOW_IFF(bvsize == 1 && is_signed);
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "1", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW_IFF(! (bvsize == 1 && is_signed));
    Z3_solver_pop(ctx, s, 1);

    if (is_signed) {
        Z3_solver_push(ctx, s); 
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "-1", bv)));
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
        TEST_NO_OVERFLOW;
        TEST_UNDERFLOW;
        Z3_solver_pop(ctx, s, 1);
    }

    Z3_solver_push(ctx, s); 
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW_IFF(! is_signed);
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, max));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
    TEST_NO_OVERFLOW_IFF(bvsize == 1 && is_signed);
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_sub(unsigned bvsize, bool is_signed) {

    TRACE("no_overflow", tout << "test_sub: bvsize = " << bvsize << ", is_signed = " << is_signed << "\n";);

    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort bv = Z3_mk_bv_sort(ctx, bvsize);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);


    Z3_ast min = mk_min(ctx, bv, is_signed);
    Z3_ast max = mk_max(ctx, bv, is_signed);
    Z3_ast t1;
    Z3_ast t2;
    Z3_ast test_ovfl;
    Z3_ast test_udfl;

    t1 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"x"), bv);
    t2 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"y"), bv);
    test_ovfl = is_signed ? Z3_mk_bvsub_no_overflow(ctx, t1, t2) : NULL;
    test_udfl = Z3_mk_bvsub_no_underflow(ctx, t1, t2, is_signed);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "0", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "1", bv)));
    TEST_NO_OVERFLOW_IFF(! (bvsize == 1 && is_signed));
    TEST_NO_UNDERFLOW_IFF(is_signed);
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "0", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW_IFF(is_signed);
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "1", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW_IFF(bvsize == 1 || is_signed);
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, max));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "1", bv)));
    TEST_NO_OVERFLOW_IFF(! (bvsize == 1 && is_signed));
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "1", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
    TEST_NO_OVERFLOW_IFF(! (bvsize != 1 && is_signed));
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "1", bv)));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW_IFF(bvsize == 1 && is_signed);
    Z3_solver_pop(ctx, s, 1);

    if (is_signed) {
        Z3_solver_push(ctx, s); 
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "-1", bv)));
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
        TEST_NO_OVERFLOW;
        TEST_NO_UNDERFLOW;
        Z3_solver_pop(ctx, s, 1);
        
        Z3_solver_push(ctx, s); 
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "-1", bv)));
        TEST_NO_OVERFLOW;
        TEST_NO_UNDERFLOW;
        Z3_solver_pop(ctx, s, 1);
    }

    Z3_solver_push(ctx, s); 
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
    TEST_NO_OVERFLOW; 
    TEST_NO_UNDERFLOW_IFF(bvsize == 1 && is_signed); 
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, max));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
    TEST_NO_OVERFLOW_IFF(! is_signed);
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, max));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_neg(unsigned bvsize) {

    TRACE("no_overflow", tout << "test_neg: bvsize = " << bvsize << "\n";);

    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort bv = Z3_mk_bv_sort(ctx, bvsize);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_ast min = mk_min(ctx, bv, /* is_signed = */ true);
    Z3_ast max = mk_max(ctx, bv, /* is_signed = */ true);
    Z3_ast t1;
    Z3_ast test_ovfl;

    t1 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"x"), bv);
    test_ovfl = Z3_mk_bvneg_no_overflow(ctx, t1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "0", bv)));
    TEST_NO_OVERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "1", bv)));
    TEST_NO_OVERFLOW_IFF(bvsize != 1);
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "-1", bv)));
    TEST_NO_OVERFLOW_IFF(bvsize != 1);
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, max));
    TEST_NO_OVERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    TEST_OVERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_mul(unsigned bvsize, bool is_signed) {

    TRACE("no_overflow", tout << "test_mul: bvsize = " << bvsize << ", is_signed = " << is_signed << "\n";);

    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort bv = Z3_mk_bv_sort(ctx, bvsize);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_ast min = mk_min(ctx, bv, is_signed);
    Z3_ast max = mk_max(ctx, bv, is_signed);
    Z3_ast t1;
    Z3_ast t2;
    Z3_ast test_ovfl;
    Z3_ast test_udfl;

    t1 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"x"), bv);
    t2 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"y"), bv);
    test_ovfl = Z3_mk_bvmul_no_overflow(ctx, t1, t2, is_signed);
    test_udfl = is_signed ? Z3_mk_bvmul_no_underflow(ctx, t1, t2) : NULL;

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "1", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "1", bv)));
    TEST_NO_OVERFLOW_IFF(! (bvsize == 1 && is_signed));
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "0", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "0", bv)));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, max));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "1", bv)));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);
    
    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "1", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
    TEST_NO_OVERFLOW_IFF(! (bvsize == 1 && is_signed));
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    if (is_signed) {
        Z3_solver_push(ctx, s); 
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "-1", bv)));
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
        TEST_OVERFLOW;
        TEST_NO_UNDERFLOW;
        Z3_solver_pop(ctx, s, 1);
        
        Z3_solver_push(ctx, s); 
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "-1", bv)));
        TEST_OVERFLOW;
        TEST_NO_UNDERFLOW;
        Z3_solver_pop(ctx, s, 1);
        
        Z3_solver_push(ctx, s); 
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "-1", bv)));
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
        TEST_NO_OVERFLOW;
        TEST_NO_UNDERFLOW;
        Z3_solver_pop(ctx, s, 1);
    }

    Z3_solver_push(ctx, s); 
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
    TEST_NO_OVERFLOW_IFF(! is_signed);
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
    TEST_NO_OVERFLOW;
    TEST_NO_UNDERFLOW_IFF(! (bvsize != 1 && is_signed));
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, max));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, max));
    TEST_NO_OVERFLOW_IFF(bvsize == 1);
    TEST_NO_UNDERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_div(unsigned bvsize) {

    TRACE("no_overflow", tout << "test_div: bvsize = " << bvsize << "\n";);

    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort bv = Z3_mk_bv_sort(ctx, bvsize);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_ast min = mk_min(ctx, bv, /* is_signed = */ true);
    Z3_ast max = mk_max(ctx, bv, /* is_signed = */ true);
    Z3_ast t1;
    Z3_ast t2;
    Z3_ast test_ovfl;

    t1 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"x"), bv);
    t2 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"y"), bv);
    test_ovfl = Z3_mk_bvsdiv_no_overflow(ctx, t1, t2);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "1", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "1", bv)));
    TEST_NO_OVERFLOW_IFF(bvsize != 1);
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "0", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "1", bv)));
    TEST_NO_OVERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "0", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "-1", bv)));
    TEST_NO_OVERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "1", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "0", bv)));
    TEST_ANY_OVERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "-1", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "0", bv)));
    TEST_ANY_OVERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "0", bv)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "0", bv)));
    TEST_ANY_OVERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s); 
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "-1", bv)));
    TEST_OVERFLOW;
    Z3_solver_pop(ctx, s, 1);
    
    Z3_solver_push(ctx, s); 
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "1", bv)));
    TEST_NO_OVERFLOW_IFF(bvsize != 1);
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s); 
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, min));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
    TEST_NO_OVERFLOW_IFF(bvsize != 1);
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_push(ctx, s); 
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, max));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, min));
    TEST_NO_OVERFLOW;
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

typedef Z3_ast (Z3_API *NO_OVFL_ARITH_FUNC)(Z3_context ctx, Z3_ast t1, Z3_ast t2, Z3_bool is_signed);
typedef Z3_ast (Z3_API *ARITH_FUNC)(Z3_context ctx, Z3_ast t1, Z3_ast t2);

typedef enum { OVFL_FUNC, UDFL_FUNC } overflow_type;

typedef struct {
    std::string        name;
    NO_OVFL_ARITH_FUNC no_overflow_func;
    ARITH_FUNC         func;
    overflow_type      type;
    int                extsize;     // negative size indicates size of arguments should be doubled
    bool               do_unsigned;
    bool               non_zero;    // second argument should not be null (for division)
    bool               sign_compar; // whether signed comparison should be used even for unsigned operation
} Equivalence_params;

Z3_ast Z3_API Z3_mk_bvsdiv_no_overflow_wrapper(Z3_context ctx, Z3_ast t1, Z3_ast t2, Z3_bool is_signed) {
    return Z3_mk_bvsdiv_no_overflow(ctx, t1, t2);
}

Z3_ast Z3_API Z3_mk_bvneg_no_overflow_wrapper(Z3_context ctx, Z3_ast t1, Z3_ast t2, Z3_bool is_signed) {
    return Z3_mk_bvneg_no_overflow(ctx, t1);
}

Z3_ast Z3_API Z3_mk_bvneg_wrapper(Z3_context ctx, Z3_ast t1, Z3_ast t2) {
    return Z3_mk_bvneg(ctx, t1);
}

Z3_ast Z3_API Z3_mk_bvadd_no_underflow_wrapper(Z3_context ctx, Z3_ast t1, Z3_ast t2, Z3_bool is_signed) {
    return Z3_mk_bvadd_no_underflow(ctx, t1, t2);
}

Z3_ast Z3_API Z3_mk_bvsub_no_overflow_wrapper(Z3_context ctx, Z3_ast t1, Z3_ast t2, Z3_bool is_signed) {
    return Z3_mk_bvsub_no_overflow(ctx, t1, t2);
}

Z3_ast Z3_API Z3_mk_bvmul_no_underflow_wrapper(Z3_context ctx, Z3_ast t1, Z3_ast t2, Z3_bool is_signed) {
    return Z3_mk_bvmul_no_underflow(ctx, t1, t2);
}

void test_equiv(Equivalence_params params, unsigned bvsize, bool is_signed) {

    TRACE("no_overflow", tout << "test_" << params.name << "_equiv: bvsize = " << bvsize << ", is_signed = " << is_signed << "\n";);

    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_sort bv = Z3_mk_bv_sort(ctx, bvsize);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_ast min = mk_min(ctx, bv, is_signed);
    Z3_ast max = mk_max(ctx, bv, is_signed);
    Z3_ast t1 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"x"), bv);
    Z3_ast t2 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"y"), bv);
    Z3_ast real_test = (*params.no_overflow_func)(ctx, t1, t2, is_signed);

    Z3_ast cond = NULL;
    if (params.non_zero)
    {
        cond = Z3_mk_not(ctx, Z3_mk_eq(ctx, t2, Z3_mk_int(ctx, 0, bv)));
    }

    unsigned extsize = params.extsize < 0 ? bvsize : params.extsize;
    if (is_signed) {
        min = Z3_mk_sign_ext(ctx, extsize, min);
        max = Z3_mk_sign_ext(ctx, extsize, max);
        t1 = Z3_mk_sign_ext(ctx, extsize, t1);
        t2 = Z3_mk_sign_ext(ctx, extsize, t2);
    }
    else {
        min = Z3_mk_zero_ext(ctx, extsize, min);
        max = Z3_mk_zero_ext(ctx, extsize, max);
        t1 = Z3_mk_zero_ext(ctx, extsize, t1);
        t2 = Z3_mk_zero_ext(ctx, extsize, t2);
    }

    Z3_ast r = (*params.func)(ctx, t1, t2);
    Z3_ast check;
    if (is_signed) {
        check = (params.type == UDFL_FUNC) ? Z3_mk_bvsle(ctx, min, r) : Z3_mk_bvsle(ctx, r, max);
    }
    else {
        if (params.sign_compar) 
        {
            // check with signed comparison for subtraction of unsigned
            check = (params.type == UDFL_FUNC) ? Z3_mk_bvsle(ctx, min, r) : Z3_mk_bvsle(ctx, r, max);
        }
        else
        {
            check = (params.type == UDFL_FUNC) ? Z3_mk_bvule(ctx, min, r) : Z3_mk_bvule(ctx, r, max);
        }
    }
    
    Z3_solver_push(ctx, s);
    Z3_ast equiv = Z3_mk_iff(ctx, real_test, check);
    if (cond != NULL)
    {
        equiv = Z3_mk_implies(ctx, cond, equiv);
    }
    Z3_solver_assert(ctx, s, Z3_mk_not(ctx, equiv));
    ENSURE(Z3_solver_check(ctx, s) == Z3_L_FALSE);
    Z3_solver_pop(ctx, s, 1);

    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

//void debug_mul() {
//
//    unsigned bvsize = 2;
//    bool is_signed = true;
//
//    Z3_config cfg = Z3_mk_config();
//    Z3_context ctx = Z3_mk_context(cfg);
//    Z3_sort bv = Z3_mk_bv_sort(ctx, bvsize);
//
//    Z3_ast min = mk_min(ctx, bv, is_signed);
//    Z3_ast max = mk_max(ctx, bv, is_signed);
//    Z3_ast t1;
//    Z3_ast t2;
//    Z3_ast test_udfl;
//
//    t1 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"x"), bv);
//    t2 = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx,"y"), bv);
//    test_udfl = Z3_mk_bvmul_no_underflow(ctx, t1, t2);
//    
//    Z3_solver_push(ctx, s);
//    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t1, Z3_mk_numeral(ctx, "1", bv)));
//    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, t2, Z3_mk_numeral(ctx, "1", bv)));
//    //TEST_NO_UNDERFLOW;
//    Z3_solver_assert(ctx, s, test_udfl);
//    ENSURE(Z3_check(ctx) == Z3_TRUE);
//    Z3_solver_pop(ctx, s, 1);
//
//    Z3_del_config(cfg);
//    Z3_del_context(ctx);
//}

#define BVSIZES 4
#define TESTNUM 3

#define EQUIV_BVSIZES 4
#define EQUIV_TESTNUM 8

typedef void (*TESTFUN)(unsigned bvsize, bool is_signed);

void tst_no_overflow() {
    disable_debug("heap");
    unsigned bvsizes[BVSIZES] = { 1, 16, 32, 42 };
    TESTFUN tests[TESTNUM] = { test_add, test_sub, test_mul };

    for (int i = 0; i < BVSIZES; ++i) {
        for (int j = 0; j < TESTNUM; ++j) {
            tests[j](bvsizes[i], /* is_signed = */ true);
            tests[j](bvsizes[i], /* is_signed = */ false);
        }
        test_neg(bvsizes[i]);
        test_div(bvsizes[i]);
    }
    
    unsigned equiv_bvsizes[EQUIV_BVSIZES] = { 1, 2, 7, 16 };
    // before performing the bound test, arguments are extended by a few bits to prevent overflow:
    // * 1 is the default
    // * 2 is used for subtraction, so that 1 bit is used for the sign event for unsigned subtraction
    // * -1 to indicate that the bitsize should be doubled for multiplication
    Equivalence_params equiv_tests[EQUIV_TESTNUM] = {
        { "ovfl_add", Z3_mk_bvadd_no_overflow,          Z3_mk_bvadd,                OVFL_FUNC,
          1,          /* do_unsigned = */ true,         /* non_zero = */ false,     /* sign_compar = */ false },
        { "udfl_add", Z3_mk_bvadd_no_underflow_wrapper, Z3_mk_bvadd,                UDFL_FUNC,
          1,          /* do_unsigned = */ false,        /* non_zero = */ false,     /* sign_compar = */ false },
        { "ovfl_sub", Z3_mk_bvsub_no_overflow_wrapper,  Z3_mk_bvsub,                OVFL_FUNC,
          1,          /* do_unsigned = */ false,        /* non_zero = */ false,     /* sign_compar = */ false },
        { "udfl_sub", Z3_mk_bvsub_no_underflow,         Z3_mk_bvsub,                UDFL_FUNC,
          2,          /* do_unsigned = */ true,         /* non_zero = */ false,     /* sign_compar = */ true  },
        { "ovfl_mul", Z3_mk_bvmul_no_overflow,          Z3_mk_bvmul,                OVFL_FUNC,
          -1,         /* do_unsigned = */ true,         /* non_zero = */ false,     /* sign_compar = */ false },
        { "udfl_mul", Z3_mk_bvmul_no_underflow_wrapper, Z3_mk_bvmul,                UDFL_FUNC,
          -1,         /* do_unsigned = */ false,        /* non_zero = */ false,     /* sign_compar = */ false },
        { "ovfl_div", Z3_mk_bvsdiv_no_overflow_wrapper, Z3_mk_bvsdiv,               OVFL_FUNC,
          1,          /* do_unsigned = */ false,        /* non_zero = */ true,      /* sign_compar = */ false },
        { "ovfl_neg", Z3_mk_bvneg_no_overflow_wrapper,  Z3_mk_bvneg_wrapper,        OVFL_FUNC,
          1,          /* do_unsigned = */ false,        /* non_zero = */ false,     /* sign_compar = */ false },
    };

    for (int i = 0; i < EQUIV_BVSIZES; ++i) {
        for (int j = 0; j < EQUIV_TESTNUM; ++j) {
            test_equiv(equiv_tests[j], equiv_bvsizes[i], /* is_signed = */ true);
            if (equiv_tests[j].do_unsigned) {
                test_equiv(equiv_tests[j], equiv_bvsizes[i], /* is_signed = */ false);
            }
        }
    }
}
#else
void tst_no_overflow() {
}
#endif
