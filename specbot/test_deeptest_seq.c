/*
 * DeepTest: High-coverage tests for Z3-c3 seq solver (Nielsen graph)
 * Targets under-exercised SPECBOT invariants/pre/postconditions in seq_nielsen.cpp
 *
 * Groups:
 *   A: Prefix/suffix cancellation (simplify pass 2)
 *   B: Symbol clash / conflict paths
 *   C: Deep variable chains (clone_from + apply_subst depth)
 *   D: Quadratic / VarNielsen modifier tests
 *   E: Regex derivatives + membership
 *   F: Power/repeat tests (simplify passes 3a-3e)
 *   G: Incremental solving stress (push/pop cycles)
 *   H: UNSAT / conflict collection
 *   I: Contains/replace/substr operation expansion
 *   J: Mixed theory (string + integer + boolean)
 */

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
static int tests_crashed = 0;

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
            tests_crashed++; \
            fprintf(stderr, "[TEST] CRASH %s (exception 0x%08lx)\n", #name, GetExceptionCode()); \
        } \
    } else { \
        tests_crashed++; \
        fprintf(stderr, "[TEST] ABORT %s (caught SIGABRT)\n", #name); \
    } \
} while(0)

/* ===== Helpers ===== */
static Z3_sort mk_string_sort(Z3_context ctx) { return Z3_mk_string_sort(ctx); }
static Z3_ast mk_str(Z3_context ctx, const char* s) { return Z3_mk_string(ctx, s); }
static Z3_ast mk_svar(Z3_context ctx, const char* name) {
    return Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, name), Z3_mk_string_sort(ctx));
}
static Z3_ast mk_cat(Z3_context ctx, Z3_ast a, Z3_ast b) {
    Z3_ast args[2] = {a, b};
    return Z3_mk_seq_concat(ctx, 2, args);
}
static Z3_ast mk_cat3(Z3_context ctx, Z3_ast a, Z3_ast b, Z3_ast c) {
    Z3_ast args[3] = {a, b, c};
    return Z3_mk_seq_concat(ctx, 3, args);
}
static Z3_ast mk_len(Z3_context ctx, Z3_ast s) { return Z3_mk_seq_length(ctx, s); }
static Z3_ast mk_int(Z3_context ctx, int v) { return Z3_mk_int(ctx, v, Z3_mk_int_sort(ctx)); }

/* Create nseq solver with timeout */
static Z3_solver mk_nseq(Z3_context ctx, unsigned timeout_ms) {
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    Z3_params p = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, p);
    Z3_params_set_symbol(ctx, p,
        Z3_mk_string_symbol(ctx, "smt.string_solver"),
        Z3_mk_string_symbol(ctx, "nseq"));
    Z3_params_set_uint(ctx, p, Z3_mk_string_symbol(ctx, "timeout"), timeout_ms);
    Z3_solver_set_params(ctx, s, p);
    Z3_params_dec_ref(ctx, p);
    return s;
}

/* Create context + solver, return both */
typedef struct { Z3_config cfg; Z3_context ctx; Z3_solver sol; } TestEnv;

static TestEnv mk_env(unsigned timeout_ms) {
    TestEnv e;
    e.cfg = Z3_mk_config();
    e.ctx = Z3_mk_context(e.cfg);
    e.sol = mk_nseq(e.ctx, timeout_ms);
    return e;
}
static void free_env(TestEnv* e) {
    Z3_solver_dec_ref(e->ctx, e->sol);
    Z3_del_config(e->cfg);
    Z3_del_context(e->ctx);
}

/* Helper: char range regex [lo-hi] */
static Z3_ast mk_range(Z3_context ctx, const char* lo, const char* hi) {
    return Z3_mk_re_range(ctx, mk_str(ctx, lo), mk_str(ctx, hi));
}

/* Helper: regex from literal string */
static Z3_ast mk_re_lit(Z3_context ctx, const char* s) {
    return Z3_mk_seq_to_re(ctx, mk_str(ctx, s));
}

/* =====================================================================
 * GROUP A: Prefix/suffix cancellation (simplify_and_init pass 2)
 * ===================================================================== */

/* "abc" ++ x = "abc" ++ y  => prefix cancellation */
void test_prefix_cancel() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast lhs = mk_cat(e.ctx, mk_str(e.ctx, "abc"), x);
    Z3_ast rhs = mk_cat(e.ctx, mk_str(e.ctx, "abc"), y);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, lhs, rhs));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* x ++ "xyz" = y ++ "xyz"  => suffix cancellation */
void test_suffix_cancel() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast lhs = mk_cat(e.ctx, x, mk_str(e.ctx, "xyz"));
    Z3_ast rhs = mk_cat(e.ctx, y, mk_str(e.ctx, "xyz"));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, lhs, rhs));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* "ab" ++ x ++ "cd" = "ab" ++ y ++ "cd"  => both prefix and suffix cancelled */
void test_prefix_suffix_cancel() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast lhs = mk_cat3(e.ctx, mk_str(e.ctx, "ab"), x, mk_str(e.ctx, "cd"));
    Z3_ast rhs = mk_cat3(e.ctx, mk_str(e.ctx, "ab"), y, mk_str(e.ctx, "cd"));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, lhs, rhs));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* Long shared prefix: "hello_world_" ++ x = "hello_world_" ++ y with length constraints */
void test_long_prefix_cancel() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast lhs = mk_cat(e.ctx, mk_str(e.ctx, "hello_world_"), x);
    Z3_ast rhs = mk_cat(e.ctx, mk_str(e.ctx, "hello_world_"), y);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, lhs, rhs));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 5)));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, y), mk_int(e.ctx, 5)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* Partial prefix overlap: "abc" ++ x = "abd" ++ y  => 'ab' cancels, then 'c' vs 'd' clash */
void test_partial_prefix_clash() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast lhs = mk_cat(e.ctx, mk_str(e.ctx, "abc"), x);
    Z3_ast rhs = mk_cat(e.ctx, mk_str(e.ctx, "abd"), y);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, lhs, rhs));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* =====================================================================
 * GROUP B: Symbol clash / conflict detection
 * ===================================================================== */

/* "a" ++ x = "b" ++ y  => first char clash */
void test_symbol_clash_ab() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
        mk_cat(e.ctx, mk_str(e.ctx, "a"), x),
        mk_cat(e.ctx, mk_str(e.ctx, "b"), y)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* "x" ++ a = "y" ++ a => prefix clash, same suffix */
void test_symbol_clash_same_suffix() {
    TestEnv e = mk_env(10000);
    Z3_ast a = mk_svar(e.ctx, "a");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
        mk_cat(e.ctx, mk_str(e.ctx, "x"), a),
        mk_cat(e.ctx, mk_str(e.ctx, "y"), a)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* "abc" = "abd"  => direct constant clash (UNSAT) */
void test_const_clash() {
    TestEnv e = mk_env(10000);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
        mk_str(e.ctx, "abc"), mk_str(e.ctx, "abd")));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* Multiple clash patterns in conjunction */
void test_multi_clash() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast z = mk_svar(e.ctx, "z");
    /* "a"++x = "b"++y AND "c"++y = "d"++z */
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
        mk_cat(e.ctx, mk_str(e.ctx, "a"), x),
        mk_cat(e.ctx, mk_str(e.ctx, "b"), y)));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
        mk_cat(e.ctx, mk_str(e.ctx, "c"), y),
        mk_cat(e.ctx, mk_str(e.ctx, "d"), z)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* Clash with length constraint making it clearly UNSAT */
void test_clash_with_length() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
        mk_cat(e.ctx, mk_str(e.ctx, "aa"), x),
        mk_cat(e.ctx, mk_str(e.ctx, "bb"), x)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* =====================================================================
 * GROUP C: Deep variable chains (many clone_from + apply_subst)
 * ===================================================================== */

/* Chain of 10 equations: x1++x2=x3, x3++x4=x5, ..., x9++x10=result="abcdefghij" */
void test_deep_chain_10() {
    TestEnv e = mk_env(15000);
    char name[16];
    Z3_ast vars[11];
    for (int i = 0; i < 11; i++) {
        sprintf(name, "v%d", i);
        vars[i] = mk_svar(e.ctx, name);
    }
    /* v0++v1=v2, v2++v3=v4, v4++v5=v6, v6++v7=v8, v8++v9=v10 */
    for (int i = 0; i < 10; i += 2) {
        Z3_ast cat = mk_cat(e.ctx, vars[i], vars[i+1]);
        Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, cat, vars[i+2 < 11 ? i+2 : 10]));
    }
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, vars[10], mk_str(e.ctx, "abcdefghij")));
    /* Constrain first var to single char to force cascading resolution */
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, vars[0]), mk_int(e.ctx, 1)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* Linear chain: x1=a++x2, x2=b++x3, ..., x7=h++x8, x8="" => forces all substitutions */
void test_linear_subst_chain() {
    TestEnv e = mk_env(15000);
    char name[16];
    Z3_ast vars[9];
    const char* letters[] = {"a","b","c","d","e","f","g","h"};
    for (int i = 0; i < 9; i++) {
        sprintf(name, "w%d", i);
        vars[i] = mk_svar(e.ctx, name);
    }
    for (int i = 0; i < 8; i++) {
        Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
            vars[i], mk_cat(e.ctx, mk_str(e.ctx, letters[i]), vars[i+1])));
    }
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, vars[8], mk_str(e.ctx, "")));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* Diamond pattern: x++y=z, x++w=z, y=w => forces clone + merge */
void test_diamond_subst() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast z = mk_svar(e.ctx, "z");
    Z3_ast w = mk_svar(e.ctx, "w");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_cat(e.ctx, x, y), z));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_cat(e.ctx, x, w), z));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, z, mk_str(e.ctx, "abcdef")));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 2)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* Wide fan: x=a1++a2++a3++a4++a5 with all ai having length constraints */
void test_wide_fan() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    char nm[8];
    Z3_ast parts[5];
    for (int i = 0; i < 5; i++) {
        sprintf(nm, "a%d", i);
        parts[i] = mk_svar(e.ctx, nm);
        Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, parts[i]), mk_int(e.ctx, 2)));
    }
    /* x = a0 ++ a1 ++ a2 ++ a3 ++ a4 */
    Z3_ast cat01 = mk_cat(e.ctx, parts[0], parts[1]);
    Z3_ast cat012 = mk_cat(e.ctx, cat01, parts[2]);
    Z3_ast cat0123 = mk_cat(e.ctx, cat012, parts[3]);
    Z3_ast cat01234 = mk_cat(e.ctx, cat0123, parts[4]);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, x, cat01234));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, x, mk_str(e.ctx, "aabbccddee")));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* =====================================================================
 * GROUP D: Quadratic / VarNielsen modifier
 * ===================================================================== */

/* x ++ y = y ++ x  (commutativity — classic quadratic) */
void test_commutative_eq() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_cat(e.ctx, x, y), mk_cat(e.ctx, y, x)));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 2)));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, y), mk_int(e.ctx, 3)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* x ++ x ++ x = y ++ y  (repeated variable, power reasoning) */
void test_triple_double() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast xxx = mk_cat3(e.ctx, x, x, x);
    Z3_ast yy = mk_cat(e.ctx, y, y);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, xxx, yy));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 2)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* x ++ "a" ++ y = y ++ "a" ++ x  (interleaved constant in quadratic) */
void test_quadratic_interleaved() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast a = mk_str(e.ctx, "a");
    Z3_ast lhs = mk_cat3(e.ctx, x, a, y);
    Z3_ast rhs = mk_cat3(e.ctx, y, a, x);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, lhs, rhs));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 1)));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, y), mk_int(e.ctx, 1)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* x ++ y ++ x = "abcab"  (variable appears on both sides) */
void test_var_both_sides() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast lhs = mk_cat3(e.ctx, x, y, x);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, lhs, mk_str(e.ctx, "abcab")));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* x ++ x = "abab" (power / repeat equation) */
void test_power_eq() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast xx = mk_cat(e.ctx, x, x);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, xx, mk_str(e.ctx, "abab")));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* =====================================================================
 * GROUP E: Regex derivatives + membership
 * ===================================================================== */

/* x in (a|b)* with |x| = 5 */
void test_regex_star_len() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast re_a = mk_re_lit(e.ctx, "a");
    Z3_ast re_b = mk_re_lit(e.ctx, "b");
    Z3_ast re_ab[2] = {re_a, re_b};
    Z3_ast re_union = Z3_mk_re_union(e.ctx, 2, re_ab);
    Z3_ast re_star = Z3_mk_re_star(e.ctx, re_union);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, re_star));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 5)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* x in [0-9]{3}-[0-9]{4}  (phone pattern) */
void test_regex_phone() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast digit = mk_range(e.ctx, "0", "9");
    Z3_ast d3 = Z3_mk_re_loop(e.ctx, digit, 3, 3);
    Z3_ast dash = mk_re_lit(e.ctx, "-");
    Z3_ast d4 = Z3_mk_re_loop(e.ctx, digit, 4, 4);
    Z3_ast parts[3] = {d3, dash, d4};
    Z3_ast phone_re = Z3_mk_re_concat(e.ctx, 3, parts);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, phone_re));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* x in (ab)* intersect (a|b){6}  (intersection + bounded loop) */
void test_regex_intersect() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast re_ab_star = Z3_mk_re_star(e.ctx, mk_re_lit(e.ctx, "ab"));
    Z3_ast re_a = mk_re_lit(e.ctx, "a");
    Z3_ast re_b = mk_re_lit(e.ctx, "b");
    Z3_ast ab_union[2] = {re_a, re_b};
    Z3_ast re_ab_single = Z3_mk_re_union(e.ctx, 2, ab_union);
    Z3_ast re_6 = Z3_mk_re_loop(e.ctx, re_ab_single, 6, 6);
    Z3_ast inter[2] = {re_ab_star, re_6};
    Z3_ast re_isect = Z3_mk_re_intersect(e.ctx, 2, inter);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, re_isect));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* Multiple regex memberships: x in [a-z]+ AND x in .*"abc".* */
void test_regex_multi_member() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    /* x in [a-z]+ */
    Z3_ast lower = Z3_mk_re_plus(e.ctx, mk_range(e.ctx, "a", "z"));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, lower));
    /* x in .*abc.* (contains "abc" via regex) */
    Z3_ast any = Z3_mk_re_star(e.ctx, Z3_mk_re_full(e.ctx,
        Z3_mk_re_sort(e.ctx, Z3_mk_string_sort(e.ctx))));
    Z3_ast abc_lit = mk_re_lit(e.ctx, "abc");
    Z3_ast contain_parts[3] = {any, abc_lit, any};
    Z3_ast contain_re = Z3_mk_re_concat(e.ctx, 3, contain_parts);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, contain_re));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 6)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* Regex with complement: x in [a-z]+ AND x NOT in .*"bad".* */
void test_regex_complement() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast lower_plus = Z3_mk_re_plus(e.ctx, mk_range(e.ctx, "a", "z"));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, lower_plus));
    /* NOT contain "bad" */
    Z3_ast any = Z3_mk_re_star(e.ctx, Z3_mk_re_full(e.ctx,
        Z3_mk_re_sort(e.ctx, Z3_mk_string_sort(e.ctx))));
    Z3_ast bad_re_parts[3] = {any, mk_re_lit(e.ctx, "bad"), any};
    Z3_ast bad_re = Z3_mk_re_concat(e.ctx, 3, bad_re_parts);
    Z3_ast no_bad = Z3_mk_re_complement(e.ctx, bad_re);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, no_bad));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 4)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* Regex + equation: x in [a-z]{3} AND x ++ y = "abcdef" */
void test_regex_plus_eq() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast lower3 = Z3_mk_re_loop(e.ctx, mk_range(e.ctx, "a", "z"), 3, 3);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, lower3));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_cat(e.ctx, x, y), mk_str(e.ctx, "abcdef")));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* =====================================================================
 * GROUP F: Power/repeat (simplify passes 3a-3e)
 * ===================================================================== */

/* x in a{3,5} with |x| = 4 */
void test_power_bounded_loop() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast re_a = mk_re_lit(e.ctx, "a");
    Z3_ast re_loop = Z3_mk_re_loop(e.ctx, re_a, 3, 5);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, re_loop));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 4)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* x ++ x = y with |y| = 10 => forces power reasoning */
void test_power_double_eq() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_cat(e.ctx, x, x), y));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, y), mk_int(e.ctx, 10)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* x in (ab){2,4} (multi-char repeat) */
void test_power_multichar_loop() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast re_ab = mk_re_lit(e.ctx, "ab");
    Z3_ast re_loop = Z3_mk_re_loop(e.ctx, re_ab, 2, 4);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, re_loop));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 6)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* x ++ x ++ x ++ x = "abcdabcdabcdabcd" (x repeated 4 times) */
void test_power_four_repeat() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast x4_inner = mk_cat(e.ctx, x, x);
    Z3_ast x4 = mk_cat(e.ctx, x4_inner, x4_inner);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, x4, mk_str(e.ctx, "abcdabcdabcdabcd")));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* x in [a-z]{1,3} AND y in [0-9]{2,4} AND x++y has fixed length 5 */
void test_power_mixed_ranges() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast alpha_re = Z3_mk_re_loop(e.ctx, mk_range(e.ctx, "a", "z"), 1, 3);
    Z3_ast digit_re = Z3_mk_re_loop(e.ctx, mk_range(e.ctx, "0", "9"), 2, 4);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, alpha_re));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, y, digit_re));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
        mk_len(e.ctx, mk_cat(e.ctx, x, y)), mk_int(e.ctx, 5)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* =====================================================================
 * GROUP G: Incremental solving stress (push/pop cycles)
 * ===================================================================== */

/* 50 rounds of push/assert/check/pop with simple equations */
void test_incremental_simple_50() {
    TestEnv e = mk_env(30000);
    Z3_ast x = mk_svar(e.ctx, "x");
    for (int i = 0; i < 50; i++) {
        char val[32];
        sprintf(val, "round_%d", i);
        Z3_solver_push(e.ctx, e.sol);
        Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, x, mk_str(e.ctx, val)));
        Z3_solver_check(e.ctx, e.sol);
        Z3_solver_pop(e.ctx, e.sol, 1);
    }
    free_env(&e);
}

/* Incremental with concat equations of increasing complexity */
void test_incremental_concat_varying() {
    TestEnv e = mk_env(30000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    for (int i = 0; i < 30; i++) {
        Z3_solver_push(e.ctx, e.sol);
        char s1[16], s2[16];
        sprintf(s1, "a%d", i);
        sprintf(s2, "b%d", i);
        Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
            mk_cat(e.ctx, x, y), mk_str(e.ctx, s1)));
        Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
            mk_len(e.ctx, x), mk_int(e.ctx, 1)));
        Z3_solver_check(e.ctx, e.sol);
        Z3_solver_pop(e.ctx, e.sol, 1);
    }
    free_env(&e);
}

/* Incremental with regex memberships */
void test_incremental_regex() {
    TestEnv e = mk_env(30000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast lower_plus = Z3_mk_re_plus(e.ctx, mk_range(e.ctx, "a", "z"));
    /* Keep regex membership across all pushes */
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, lower_plus));
    for (int i = 1; i <= 20; i++) {
        Z3_solver_push(e.ctx, e.sol);
        Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, i)));
        Z3_solver_check(e.ctx, e.sol);
        Z3_solver_pop(e.ctx, e.sol, 1);
    }
    free_env(&e);
}

/* Nested push/pop: 2 levels deep with string constraints */
void test_incremental_nested() {
    TestEnv e = mk_env(15000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    for (int i = 0; i < 10; i++) {
        Z3_solver_push(e.ctx, e.sol);
        char v1[16];
        sprintf(v1, "outer_%d", i);
        Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
            mk_cat(e.ctx, x, y), mk_str(e.ctx, v1)));
        Z3_solver_check(e.ctx, e.sol);
        for (int j = 0; j < 5; j++) {
            Z3_solver_push(e.ctx, e.sol);
            Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx,
                mk_len(e.ctx, x), mk_int(e.ctx, j)));
            Z3_solver_check(e.ctx, e.sol);
            Z3_solver_pop(e.ctx, e.sol, 1);
        }
        Z3_solver_pop(e.ctx, e.sol, 1);
    }
    free_env(&e);
}

/* =====================================================================
 * GROUP H: UNSAT / conflict collection paths
 * ===================================================================== */

/* x = "abc" AND x = "def"  (direct contradiction) */
void test_unsat_direct() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, x, mk_str(e.ctx, "abc")));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, x, mk_str(e.ctx, "def")));
    Z3_lbool r = Z3_solver_check(e.ctx, e.sol);
    fprintf(stderr, "  [unsat_direct] result=%d\n", r);
    free_env(&e);
}

/* |x| = 3 AND x in [a-z]{5}  (length conflict) */
void test_unsat_length_regex() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 3)));
    Z3_ast re = Z3_mk_re_loop(e.ctx, mk_range(e.ctx, "a", "z"), 5, 5);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, re));
    Z3_lbool r = Z3_solver_check(e.ctx, e.sol);
    fprintf(stderr, "  [unsat_length_regex] result=%d\n", r);
    free_env(&e);
}

/* x ++ y = "ab" AND |x| = 3  (length impossible: |x|+|y|=2, |x|=3) */
void test_unsat_length_impossible() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_cat(e.ctx, x, y), mk_str(e.ctx, "ab")));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 3)));
    Z3_lbool r = Z3_solver_check(e.ctx, e.sol);
    fprintf(stderr, "  [unsat_length_impossible] result=%d\n", r);
    free_env(&e);
}

/* x in empty regex */
void test_unsat_empty_regex() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_sort re_sort = Z3_mk_re_sort(e.ctx, Z3_mk_string_sort(e.ctx));
    Z3_ast empty_re = Z3_mk_re_empty(e.ctx, re_sort);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, empty_re));
    Z3_lbool r = Z3_solver_check(e.ctx, e.sol);
    fprintf(stderr, "  [unsat_empty_regex] result=%d\n", r);
    free_env(&e);
}

/* x = "abc" AND NOT(x = "abc")  (tautological unsat) */
void test_unsat_negation() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast abc = mk_str(e.ctx, "abc");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, x, abc));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_not(e.ctx, Z3_mk_eq(e.ctx, x, abc)));
    Z3_lbool r = Z3_solver_check(e.ctx, e.sol);
    fprintf(stderr, "  [unsat_negation] result=%d\n", r);
    free_env(&e);
}

/* x ++ y = "abc" AND x = "ab" AND y = "cd" (suffix mismatch) */
void test_unsat_concat_mismatch() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_cat(e.ctx, x, y), mk_str(e.ctx, "abc")));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, x, mk_str(e.ctx, "ab")));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, y, mk_str(e.ctx, "cd")));
    Z3_lbool r = Z3_solver_check(e.ctx, e.sol);
    fprintf(stderr, "  [unsat_concat_mismatch] result=%d\n", r);
    free_env(&e);
}

/* =====================================================================
 * GROUP I: Contains/replace/substr operation expansion
 * ===================================================================== */

/* contains(x, "needle") AND |x| = 6 (exact fit) */
void test_contains_exact() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_contains(e.ctx, x, mk_str(e.ctx, "needle")));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 6)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* replace(x, "old", "new") = y AND x = "hold" */
void test_replace_known() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast replaced = Z3_mk_seq_replace(e.ctx, x, mk_str(e.ctx, "old"), mk_str(e.ctx, "new"));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, replaced, y));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, x, mk_str(e.ctx, "hold")));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* substr(x, 1, 3) = "ell" AND prefix(x, "h") => x starts with "hell" */
void test_substr_extract() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast sub = Z3_mk_seq_extract(e.ctx, x, mk_int(e.ctx, 1), mk_int(e.ctx, 3));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, sub, mk_str(e.ctx, "ell")));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_prefix(e.ctx, mk_str(e.ctx, "h"), x));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 5)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* indexof(x, "bc", 0) = 1 AND |x| = 5 */
void test_indexof_constraint() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast idx = Z3_mk_seq_index(e.ctx, x, mk_str(e.ctx, "bc"), mk_int(e.ctx, 0));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, idx, mk_int(e.ctx, 1)));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 5)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* contains(x, "ab") AND contains(x, "cd") AND |x| = 4 => x must be "abcd" or similar */
void test_multi_contains() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_contains(e.ctx, x, mk_str(e.ctx, "ab")));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_contains(e.ctx, x, mk_str(e.ctx, "cd")));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 4)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* prefix and suffix constraints together */
void test_prefix_suffix_ops() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_prefix(e.ctx, mk_str(e.ctx, "hel"), x));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_suffix(e.ctx, mk_str(e.ctx, "llo"), x));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 5)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* =====================================================================
 * GROUP J: Mixed theory (string + integer + boolean)
 * ===================================================================== */

/* |x| + |y| = 10 AND x ++ y = z AND |x| > |y| */
void test_mixed_len_arith() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_ast z = mk_svar(e.ctx, "z");
    Z3_ast int_sort_args[2] = {mk_len(e.ctx, x), mk_len(e.ctx, y)};
    Z3_ast len_sum = Z3_mk_add(e.ctx, 2, int_sort_args);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, len_sum, mk_int(e.ctx, 10)));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_cat(e.ctx, x, y), z));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_gt(e.ctx, mk_len(e.ctx, x), mk_len(e.ctx, y)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* ite(contains(x, "a"), x = "abc", x = "def") */
void test_mixed_ite_contains() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast cond = Z3_mk_seq_contains(e.ctx, x, mk_str(e.ctx, "a"));
    Z3_ast then_eq = Z3_mk_eq(e.ctx, x, mk_str(e.ctx, "abc"));
    Z3_ast else_eq = Z3_mk_eq(e.ctx, x, mk_str(e.ctx, "def"));
    Z3_ast ite = Z3_mk_ite(e.ctx, cond, then_eq, else_eq);
    Z3_solver_assert(e.ctx, e.sol, ite);
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* str.to_int(x) = 42 AND x in [0-9]+ */
void test_mixed_str_to_int() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast to_int = Z3_mk_str_to_int(e.ctx, x);
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, to_int, mk_int(e.ctx, 42)));
    Z3_ast digit_plus = Z3_mk_re_plus(e.ctx, mk_range(e.ctx, "0", "9"));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_in_re(e.ctx, x, digit_plus));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* int.to_str(n) = x AND n >= 100 AND n <= 999 */
void test_mixed_int_to_str() {
    TestEnv e = mk_env(10000);
    Z3_ast n = Z3_mk_const(e.ctx, Z3_mk_string_symbol(e.ctx, "n"), Z3_mk_int_sort(e.ctx));
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, Z3_mk_int_to_str(e.ctx, n), x));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_ge(e.ctx, n, mk_int(e.ctx, 100)));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_le(e.ctx, n, mk_int(e.ctx, 999)));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 3)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* Multiple string ops combined: contains + replace + length */
void test_mixed_ops_combined() {
    TestEnv e = mk_env(10000);
    Z3_ast x = mk_svar(e.ctx, "x");
    Z3_ast y = mk_svar(e.ctx, "y");
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_seq_contains(e.ctx, x, mk_str(e.ctx, "hello")));
    Z3_ast replaced = Z3_mk_seq_replace(e.ctx, x, mk_str(e.ctx, "hello"), mk_str(e.ctx, "world"));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, replaced, y));
    Z3_solver_assert(e.ctx, e.sol, Z3_mk_eq(e.ctx, mk_len(e.ctx, x), mk_int(e.ctx, 8)));
    Z3_solver_check(e.ctx, e.sol);
    free_env(&e);
}

/* =====================================================================
 * MAIN
 * ===================================================================== */
int main() {
    suppress_dialogs();
    fprintf(stderr, "[SPECBOT] Starting DeepTest Z3-c3 seq solver tests\n");

    Z3_global_param_set("smt.string_solver", "nseq");

    /* Group A: Prefix/suffix cancellation */
    RUN_TEST(test_prefix_cancel);
    RUN_TEST(test_suffix_cancel);
    RUN_TEST(test_prefix_suffix_cancel);
    RUN_TEST(test_long_prefix_cancel);
    RUN_TEST(test_partial_prefix_clash);

    /* Group B: Symbol clash */
    RUN_TEST(test_symbol_clash_ab);
    RUN_TEST(test_symbol_clash_same_suffix);
    RUN_TEST(test_const_clash);
    RUN_TEST(test_multi_clash);
    RUN_TEST(test_clash_with_length);

    /* Group C: Deep variable chains */
    RUN_TEST(test_deep_chain_10);
    RUN_TEST(test_linear_subst_chain);
    RUN_TEST(test_diamond_subst);
    RUN_TEST(test_wide_fan);

    /* Group D: Quadratic / VarNielsen */
    RUN_TEST(test_commutative_eq);
    RUN_TEST(test_triple_double);
    RUN_TEST(test_quadratic_interleaved);
    RUN_TEST(test_var_both_sides);
    RUN_TEST(test_power_eq);

    /* Group E: Regex derivatives */
    RUN_TEST(test_regex_star_len);
    RUN_TEST(test_regex_phone);
    RUN_TEST(test_regex_intersect);
    RUN_TEST(test_regex_multi_member);
    RUN_TEST(test_regex_complement);
    RUN_TEST(test_regex_plus_eq);

    /* Group F: Power/repeat */
    RUN_TEST(test_power_bounded_loop);
    RUN_TEST(test_power_double_eq);
    RUN_TEST(test_power_multichar_loop);
    RUN_TEST(test_power_four_repeat);
    RUN_TEST(test_power_mixed_ranges);

    /* Group G: Incremental stress */
    RUN_TEST(test_incremental_simple_50);
    RUN_TEST(test_incremental_concat_varying);
    RUN_TEST(test_incremental_regex);
    RUN_TEST(test_incremental_nested);

    /* Group H: UNSAT / conflict */
    RUN_TEST(test_unsat_direct);
    RUN_TEST(test_unsat_length_regex);
    RUN_TEST(test_unsat_length_impossible);
    RUN_TEST(test_unsat_empty_regex);
    RUN_TEST(test_unsat_negation);
    RUN_TEST(test_unsat_concat_mismatch);

    /* Group I: Contains/replace/substr */
    RUN_TEST(test_contains_exact);
    RUN_TEST(test_replace_known);
    RUN_TEST(test_substr_extract);
    RUN_TEST(test_indexof_constraint);
    RUN_TEST(test_multi_contains);
    RUN_TEST(test_prefix_suffix_ops);

    /* Group J: Mixed theory */
    RUN_TEST(test_mixed_len_arith);
    RUN_TEST(test_mixed_ite_contains);
    RUN_TEST(test_mixed_str_to_int);
    RUN_TEST(test_mixed_int_to_str);
    RUN_TEST(test_mixed_ops_combined);

    printf("=== DeepTest Z3-c3 Seq: %d/%d passed, %d crashed ===\n",
           tests_passed, tests_run, tests_crashed);
    return tests_run - tests_passed;
}
