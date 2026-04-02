#include "z3.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include <setjmp.h>

#ifdef _WIN32
#include <windows.h>
#include <crtdbg.h>
#include <signal.h>

static jmp_buf jmp_env;
static volatile int in_test = 0;

void abort_handler(int sig) {
    (void)sig;
    if (in_test) {
        in_test = 0;
        signal(SIGABRT, abort_handler);
        longjmp(jmp_env, 1);
    }
}

void suppress_dialogs() {
    SetErrorMode(SEM_FAILCRITICALERRORS | SEM_NOGPFAULTERRORBOX);
    _CrtSetReportMode(_CRT_ASSERT, _CRTDBG_MODE_FILE);
    _CrtSetReportFile(_CRT_ASSERT, _CRTDBG_FILE_STDERR);
    _CrtSetReportMode(_CRT_ERROR, _CRTDBG_MODE_FILE);
    _CrtSetReportFile(_CRT_ERROR, _CRTDBG_FILE_STDERR);
    _set_invalid_parameter_handler(
        (void (*)(const wchar_t*,const wchar_t*,const wchar_t*,unsigned int,uintptr_t))0
    );
    _set_abort_behavior(0, _WRITE_ABORT_MSG | _CALL_REPORTFAULT);
    signal(SIGABRT, abort_handler);
}
#else
void suppress_dialogs() {}
#endif

static int tests_run = 0;
static int tests_passed = 0;

#define RUN_TEST(name) do { \
    fprintf(stderr, "[TEST] Running %s\n", #name); \
    tests_run++; \
    in_test = 1; \
    if (setjmp(jmp_env) == 0) { \
        __try { \
            name(); \
            in_test = 0; \
            tests_passed++; \
            fprintf(stderr, "[TEST] PASS %s\n", #name); \
        } __except(EXCEPTION_EXECUTE_HANDLER) { \
            in_test = 0; \
            fprintf(stderr, "[TEST] CRASH %s (exception 0x%08lx)\n", #name, GetExceptionCode()); \
        } \
    } else { \
        fprintf(stderr, "[TEST] ABORT %s (caught SIGABRT)\n", #name); \
    } \
} while(0)

/* Helper to create string sort, variables, constants */
Z3_sort mk_string_sort(Z3_context ctx) { return Z3_mk_string_sort(ctx); }
Z3_ast mk_string_var(Z3_context ctx, const char* name) {
    return Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), Z3_mk_string_sort(ctx));
}
Z3_ast mk_string_val(Z3_context ctx, const char* s) {
    return Z3_mk_string(ctx, s);
}
Z3_ast mk_concat(Z3_context ctx, Z3_ast a, Z3_ast b) {
    Z3_ast args[2] = {a, b};
    return Z3_mk_seq_concat(ctx, 2, args);
}

/* Create a solver configured to use the nseq (Nielsen) string solver */
Z3_solver mk_nseq_solver(Z3_context ctx) {
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    Z3_params p = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, p);
    Z3_params_set_symbol(ctx, p, Z3_mk_string_symbol(ctx, "smt.string_solver"),
                         Z3_mk_string_symbol(ctx, "nseq"));
    Z3_solver_set_params(ctx, s, p);
    Z3_params_dec_ref(ctx, p);
    return s;
}

/* === TEST GROUPS === */

/* Group A: Basic equations - exercises clone_from, simplify, solve */
void test_simple_eq() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_ast hello = mk_string_val(ctx, "hello");
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, hello));
    
    Z3_lbool r = Z3_solver_check(ctx, s);
    (void)r;
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_concat_eq() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_ast y = mk_string_var(ctx, "y");
    Z3_ast xy = mk_concat(ctx, x, y);
    Z3_ast abc = mk_string_val(ctx, "abc");
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, xy, abc));
    
    Z3_lbool r = Z3_solver_check(ctx, s);
    (void)r;
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_unsat_eq() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, mk_string_val(ctx, "a")));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, mk_string_val(ctx, "b")));
    
    Z3_lbool r = Z3_solver_check(ctx, s);
    (void)r;
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_multi_var_eq() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_ast y = mk_string_var(ctx, "y");
    Z3_ast z = mk_string_var(ctx, "z");
    Z3_ast xy = mk_concat(ctx, x, y);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, xy, z));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, z, mk_string_val(ctx, "test")));
    
    Z3_solver_check(ctx, s);
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_empty_string() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_ast empty = mk_string_val(ctx, "");
    Z3_ast xe = mk_concat(ctx, x, empty);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, xe, x));
    
    Z3_solver_check(ctx, s);
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

/* Group B: Regex membership - exercises add_str_mem, regex processing */
void test_regex_basic() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_ast re = Z3_mk_re_plus(ctx, Z3_mk_re_range(ctx, mk_string_val(ctx, "a"), mk_string_val(ctx, "z")));
    Z3_solver_assert(ctx, s, Z3_mk_seq_in_re(ctx, x, re));
    
    Z3_solver_check(ctx, s);
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_regex_combined() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_ast y = mk_string_var(ctx, "y");
    Z3_ast re = Z3_mk_re_plus(ctx, Z3_mk_re_range(ctx, mk_string_val(ctx, "0"), mk_string_val(ctx, "9")));
    Z3_solver_assert(ctx, s, Z3_mk_seq_in_re(ctx, x, re));
    
    Z3_ast xy = mk_concat(ctx, x, mk_concat(ctx, mk_string_val(ctx, "-"), y));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, xy, mk_string_val(ctx, "123-abc")));
    
    Z3_solver_check(ctx, s);
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

/* Group C: Length constraints */
void test_length_eq() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_ast len_x = Z3_mk_seq_length(ctx, x);
    Z3_ast five = Z3_mk_int(ctx, 5, Z3_mk_int_sort(ctx));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, len_x, five));
    Z3_ast re = Z3_mk_re_plus(ctx, Z3_mk_re_range(ctx, mk_string_val(ctx, "a"), mk_string_val(ctx, "z")));
    Z3_solver_assert(ctx, s, Z3_mk_seq_in_re(ctx, x, re));
    
    Z3_solver_check(ctx, s);
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_length_sum() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_ast y = mk_string_var(ctx, "y");
    Z3_ast z = mk_string_var(ctx, "z");
    Z3_ast xy = mk_concat(ctx, x, y);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, xy, z));
    
    Z3_ast ten = Z3_mk_int(ctx, 10, Z3_mk_int_sort(ctx));
    Z3_ast len_z = Z3_mk_seq_length(ctx, z);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, len_z, ten));
    
    Z3_solver_check(ctx, s);
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

/* Group D: Nielsen-specific stress */
void test_quadratic_eq() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    Z3_params p = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, p);
    Z3_params_set_uint(ctx, p, Z3_mk_string_symbol(ctx, "timeout"), 5000);
    Z3_solver_set_params(ctx, s, p);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_ast y = mk_string_var(ctx, "y");
    Z3_ast xx = mk_concat(ctx, x, x);
    Z3_ast yy = mk_concat(ctx, y, y);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, xx, yy));
    
    Z3_solver_check(ctx, s);
    
    Z3_params_dec_ref(ctx, p);
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_many_vars() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    Z3_params p = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, p);
    Z3_params_set_uint(ctx, p, Z3_mk_string_symbol(ctx, "timeout"), 5000);
    Z3_solver_set_params(ctx, s, p);
    
    char name[16];
    Z3_ast vars[10];
    for (int i = 0; i < 10; i++) {
        sprintf(name, "x%d", i);
        vars[i] = mk_string_var(ctx, name);
    }
    for (int i = 0; i < 8; i += 2) {
        Z3_ast cat = mk_concat(ctx, vars[i], vars[i+1]);
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, cat, vars[i+2 < 10 ? i+2 : 0]));
    }
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, vars[0], mk_string_val(ctx, "ab")));
    
    Z3_solver_check(ctx, s);
    
    Z3_params_dec_ref(ctx, p);
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_push_pop() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, mk_string_val(ctx, "hello")));
    Z3_solver_check(ctx, s);
    
    Z3_solver_push(ctx, s);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, mk_string_val(ctx, "world")));
    Z3_solver_check(ctx, s);
    Z3_solver_pop(ctx, s, 1);
    
    Z3_solver_check(ctx, s);
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_incremental_many() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    Z3_params p = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, p);
    Z3_params_set_uint(ctx, p, Z3_mk_string_symbol(ctx, "timeout"), 5000);
    Z3_solver_set_params(ctx, s, p);
    
    Z3_ast x = mk_string_var(ctx, "x");
    for (int i = 0; i < 20; i++) {
        Z3_solver_push(ctx, s);
        char val[32];
        sprintf(val, "test_%d", i);
        Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, x, mk_string_val(ctx, val)));
        Z3_solver_check(ctx, s);
        Z3_solver_pop(ctx, s, 1);
    }
    
    Z3_params_dec_ref(ctx, p);
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

/* Group E: Edge cases */
void test_contains() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_solver_assert(ctx, s, Z3_mk_seq_contains(ctx, x, mk_string_val(ctx, "needle")));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, Z3_mk_seq_length(ctx, x), Z3_mk_int(ctx, 10, Z3_mk_int_sort(ctx))));
    
    Z3_solver_check(ctx, s);
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_replace() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_ast y = mk_string_var(ctx, "y");
    Z3_ast replaced = Z3_mk_seq_replace(ctx, x, mk_string_val(ctx, "old"), mk_string_val(ctx, "new"));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, replaced, y));
    Z3_solver_assert(ctx, s, Z3_mk_seq_contains(ctx, x, mk_string_val(ctx, "old")));
    
    Z3_solver_check(ctx, s);
    
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_long_string_eq() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    Z3_params p = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, p);
    Z3_params_set_uint(ctx, p, Z3_mk_string_symbol(ctx, "timeout"), 10000);
    Z3_solver_set_params(ctx, s, p);
    
    char long_str[101];
    memset(long_str, 'a', 100);
    long_str[100] = 0;
    
    Z3_ast x = mk_string_var(ctx, "x");
    Z3_ast y = mk_string_var(ctx, "y");
    Z3_ast xy = mk_concat(ctx, x, y);
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, xy, mk_string_val(ctx, long_str)));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, Z3_mk_seq_length(ctx, x), Z3_mk_int(ctx, 50, Z3_mk_int_sort(ctx))));
    
    Z3_solver_check(ctx, s);
    
    Z3_params_dec_ref(ctx, p);
    Z3_solver_dec_ref(ctx, s);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

int main() {
    suppress_dialogs();
    fprintf(stderr, "[SPECBOT] Starting Z3 c3 seq solver invariant tests\n");
    
    /* Force the Nielsen seq solver globally */
    Z3_global_param_set("smt.string_solver", "nseq");
    
    /* Group A: Basic equations */
    RUN_TEST(test_simple_eq);
    RUN_TEST(test_concat_eq);
    RUN_TEST(test_unsat_eq);
    RUN_TEST(test_multi_var_eq);
    RUN_TEST(test_empty_string);
    
    /* Group B: Regex */
    RUN_TEST(test_regex_basic);
    RUN_TEST(test_regex_combined);
    
    /* Group C: Length */
    RUN_TEST(test_length_eq);
    RUN_TEST(test_length_sum);
    
    /* Group D: Nielsen stress */
    RUN_TEST(test_quadratic_eq);
    RUN_TEST(test_many_vars);
    RUN_TEST(test_push_pop);
    RUN_TEST(test_incremental_many);
    
    /* Group E: Edge cases */
    RUN_TEST(test_contains);
    RUN_TEST(test_replace);
    RUN_TEST(test_long_string_eq);
    
    printf("=== SpecBot Z3-c3 Seq Tests: %d/%d passed ===\n", tests_passed, tests_run);
    return tests_run - tests_passed;
}
