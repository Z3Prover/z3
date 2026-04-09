#include <iostream>
#include <iomanip>
#include <string>
#include <cstring>
#include <cstdio>
#include <vector>
#include <sstream>
#include "util/util.h"
#include "util/trace.h"
#include "util/debug.h"
#include "util/timeit.h"
#include "util/warning.h"
#include "util/memory_manager.h"
#include "util/gparams.h"

#ifndef __EMSCRIPTEN__
#include <thread>
#include <mutex>
#include <chrono>
#endif

#if !defined(__EMSCRIPTEN__) && !defined(_WINDOWS)
#include <sys/wait.h>
#endif

#ifdef _WINDOWS
#define Z3_POPEN  _popen
#define Z3_PCLOSE _pclose
#else
#define Z3_POPEN  popen
#define Z3_PCLOSE pclose
#endif

//
// Unit tests fail by asserting.
// If they return, we assume the unit test succeeds
// and print "PASS" to indicate success.
//

// ========================================================================
// Test list definitions using X-macros.
// X(name) is for regular tests, X_ARGV(name) is for tests needing arguments.
// FOR_EACH_ALL_TEST: tests run with /a flag.
// FOR_EACH_EXTRA_TEST: tests only run when explicitly named.
// ========================================================================

#define FOR_EACH_ALL_TEST(X, X_ARGV) \
    X(random) \
    X(symbol_table) \
    X(region) \
    X(symbol) \
    X(heap) \
    X(hashtable) \
    X(rational) \
    X(inf_rational) \
    X(ast) \
    X(optional) \
    X(bit_vector) \
    X(fixed_bit_vector) \
    X(tbv) \
    X(doc) \
    X(udoc_relation) \
    X(string_buffer) \
    X(map) \
    X(diff_logic) \
    X(uint_set) \
    X_ARGV(expr_rand) \
    X(list) \
    X(small_object_allocator) \
    X(timeout) \
    X(proof_checker) \
    X(simplifier) \
    X(bit_blaster) \
    X(var_subst) \
    X(simple_parser) \
    X(api) \
    X(max_reg) \
    X(max_rev) \
    X(scaled_min) \
    X(box_mod_opt) \
    X(box_independent) \
    X(deep_api_bugs) \
    X(api_algebraic) \
    X(api_polynomial) \
    X(api_pb) \
    X(api_datalog) \
    X(parametric_datatype) \
    X(cube_clause) \
    X(old_interval) \
    X(get_implied_equalities) \
    X(arith_simplifier_plugin) \
    X(matcher) \
    X(object_allocator) \
    X(mpz) \
    X(mpq) \
    X(mpf) \
    X(total_order) \
    X(dl_table) \
    X(dl_context) \
    X(dlist) \
    X(dl_util) \
    X(dl_product_relation) \
    X(dl_relation) \
    X(parray) \
    X(stack) \
    X(escaped) \
    X(buffer) \
    X(chashtable) \
    X(egraph) \
    X(ex) \
    X(nlarith_util) \
    X(api_ast_map) \
    X(api_bug) \
    X(api_special_relations) \
    X(arith_rewriter) \
    X(check_assumptions) \
    X(smt_context) \
    X(theory_dl) \
    X(model_retrieval) \
    X(model_based_opt) \
    X(factor_rewriter) \
    X(smt2print_parse) \
    X(substitution) \
    X(polynomial) \
    X(polynomial_factorization) \
    X(upolynomial) \
    X(algebraic) \
    X(algebraic_numbers) \
    X(ackermannize) \
    X(monomial_bounds) \
    X(nla_intervals) \
    X(horner) \
    X(prime_generator) \
    X(permutation) \
    X(nlsat) \
    X(13) \
    X(zstring)

#define FOR_EACH_EXTRA_TEST(X, X_ARGV) \
    X(ext_numeral) \
    X(interval) \
    X(value_generator) \
    X(value_sweep) \
    X(vector) \
    X(f2n) \
    X(hwf) \
    X(trigo) \
    X(bits) \
    X(mpbq) \
    X(mpfx) \
    X(mpff) \
    X(horn_subsume_model_converter) \
    X(model2expr) \
    X(hilbert_basis) \
    X(heap_trie) \
    X(karr) \
    X(mod_factor) \
    X(no_overflow) \
    X(datalog_parser) \
    X_ARGV(datalog_parser_file) \
    X(dl_query) \
    X(quant_solve) \
    X(rcf) \
    X(polynorm) \
    X(qe_arith) \
    X(expr_substitution) \
    X(sorting_network) \
    X(theory_pb) \
    X(simplex) \
    X(sat_user_scope) \
    X_ARGV(ddnf) \
    X(ddnf1) \
    X(model_evaluator) \
    X(get_consequences) \
    X(pb2bv) \
    X_ARGV(sat_lookahead) \
    X_ARGV(sat_local_search) \
    X_ARGV(cnf_backbones) \
    X(bdd) \
    X(pdd) \
    X(pdd_solver) \
    X(scoped_timer) \
    X(solver_pool) \
    X(finder) \
    X(totalizer) \
    X(distribution) \
    X(euf_bv_plugin) \
    X(euf_arith_plugin) \
    X(sls_test) \
    X(scoped_vector) \
    X(sls_seq_plugin) \
    X(ho_matcher) \
    X(finite_set) \
    X(finite_set_rewriter) \
    X(fpa)

#define FOR_EACH_TEST(X, X_ARGV) \
    FOR_EACH_ALL_TEST(X, X_ARGV) \
    FOR_EACH_EXTRA_TEST(X, X_ARGV)

// Forward declarations for all test functions
#define DECL_TST(M) void tst_##M();
#define DECL_TST_ARGV(M) void tst_##M(char** argv, int argc, int& i);
FOR_EACH_TEST(DECL_TST, DECL_TST_ARGV)
#undef DECL_TST
#undef DECL_TST_ARGV

// ========================================================================
// Helper functions
// ========================================================================

void error(const char * msg) {
    std::cerr << "Error: " << msg << "\n";
    std::cerr << "For usage information: test /h\n";
    exit(1);
}

void display_usage() {
    std::cout << "Z3 unit tests [version 1.0]. (C) Copyright 2006 Microsoft Corp.\n";
    std::cout << "Usage: test [options] [module names]\n";
    std::cout << "\nMisc.:\n";
    std::cout << "  /h          prints this message.\n";
    std::cout << "  /v:level    be verbose, where <level> is the verbosity level.\n";
    std::cout << "  /w          enable warning messages.\n";
    std::cout << "  /a          run all unit tests that don't require arguments.\n";
#ifndef __EMSCRIPTEN__
    std::cout << "  /j[:N]      run tests in parallel using N jobs (default: number of cores).\n";
    std::cout << "  /seq        run tests sequentially, disabling parallel execution.\n";
#endif
#if defined(Z3DEBUG) || defined(_TRACE)
    std::cout << "\nDebugging support:\n";
#endif
#ifdef _TRACE
    std::cout << "  /tr:tag     enable trace messages tagged with <tag>.\n";
#endif
#ifdef Z3DEBUG
    std::cout << "  /dbg:tag    enable assertions tagged with <tag>.\n";
#endif
    std::cout << "\nModule names:\n";
}

void parse_cmd_line_args(int argc, char ** argv, bool& do_display_usage, bool& test_all,
                         unsigned& num_jobs, std::vector<std::string>& extra_args) {
    int i = 1;
    if (argc == 1) {
        display_usage();
        do_display_usage = true;
    }
    while (i < argc) {
        char * arg = argv[i];
        char * eq_pos = nullptr;

        if (arg[0] == '-' || arg[0] == '/') {
            char * opt_name = arg + 1;
            char * opt_arg  = nullptr;
            char * colon    = strchr(arg, ':');
            if (colon) {
                opt_arg = colon + 1;
                *colon  = 0;
            }
            if (strcmp(opt_name, "h") == 0 ||
                strcmp(opt_name, "?") == 0) {
                display_usage();
                do_display_usage = true;
                return;
            }
            else if (strcmp(opt_name, "v") == 0) {
                if (!opt_arg)
                    error("option argument (/v:level) is missing.");
                long lvl = strtol(opt_arg, nullptr, 10);
                set_verbosity_level(lvl);
                extra_args.push_back(std::string("/v:") + opt_arg);
            }
            else if (strcmp(opt_name, "w") == 0) {
                enable_warning_messages(true);
                extra_args.push_back("/w");
            }
            else if (strcmp(opt_name, "a") == 0) {
                test_all = true;
            }
            else if (strcmp(opt_name, "j") == 0) {
#ifndef __EMSCRIPTEN__
                if (opt_arg) {
                    long n = strtol(opt_arg, nullptr, 10);
                    if (n <= 0) error("invalid number of jobs for /j option.");
                    num_jobs = static_cast<unsigned>(n);
                }
                else {
                    unsigned hw = std::thread::hardware_concurrency();
                    num_jobs = hw > 0 ? hw : 4;
                }
#else
                error("/j option is not supported on this platform.");
#endif
            }
            else if (strcmp(opt_name, "seq") == 0) {
                num_jobs = 0;
            }
#ifdef _TRACE
            else if (strcmp(opt_name, "tr") == 0) {
                if (!opt_arg)
                    error("option argument (/tr:tag) is missing.");
                enable_trace(opt_arg);
                extra_args.push_back(std::string("/tr:") + opt_arg);
            }
#endif
#ifdef Z3DEBUG
            else if (strcmp(opt_name, "dbg") == 0) {
                if (!opt_arg)
                    error("option argument (/dbg:tag) is missing.");
                enable_debug(opt_arg);
                extra_args.push_back(std::string("/dbg:") + opt_arg);
            }
#endif
        }
        else if (arg[0] != '"' && (eq_pos = strchr(arg, '='))) {
            char * key   = arg;
            *eq_pos      = 0;
            char * value = eq_pos+1;
            try {
                gparams::set(key, value);
                extra_args.push_back(std::string(key) + "=" + value);
            }
            catch (z3_exception& ex) {
                std::cerr << ex.what() << "\n";
            }
        }
        i++;
    }
}


// ========================================================================
// Parallel test execution using child processes
// ========================================================================

#ifndef __EMSCRIPTEN__

struct test_result {
    std::string name;
    int exit_code;
    std::string output;
    double elapsed_secs;
};

static test_result run_test_child(const char* exe_path, const char* test_name,
                                  const std::vector<std::string>& extra_args) {
    test_result result;
    result.name = test_name;

    std::ostringstream cmd;
    cmd << "\"" << exe_path << "\"" << " /seq " << test_name;
    for (const auto& arg : extra_args)
        cmd << " " << arg;
    cmd << " 2>&1";

    auto start = std::chrono::steady_clock::now();

    FILE* pipe = Z3_POPEN(cmd.str().c_str(), "r");
    if (!pipe) {
        result.exit_code = -1;
        result.output = "Failed to start child process\n";
        result.elapsed_secs = 0;
        return result;
    }

    char buf[4096];
    while (fgets(buf, sizeof(buf), pipe))
        result.output += buf;

    int raw = Z3_PCLOSE(pipe);
#ifdef _WINDOWS
    result.exit_code = raw;
#else
    if (WIFEXITED(raw))
        result.exit_code = WEXITSTATUS(raw);
    else if (WIFSIGNALED(raw))
        result.exit_code = 128 + WTERMSIG(raw);
    else
        result.exit_code = -1;
#endif

    auto end = std::chrono::steady_clock::now();
    result.elapsed_secs = std::chrono::duration<double>(end - start).count();
    return result;
}

static int run_parallel(const char* exe_path, bool test_all, unsigned num_jobs,
                        const std::vector<std::string>& extra_args,
                        const std::vector<std::string>& requested_tests) {
    std::vector<std::string> tests_to_run;

    if (test_all) {
        #define COLLECT_ALL(M) tests_to_run.push_back(#M);
        #define SKIP_ARGV_1(M)
        FOR_EACH_ALL_TEST(COLLECT_ALL, SKIP_ARGV_1)
        #undef COLLECT_ALL
        #undef SKIP_ARGV_1
    }
    else {
        #define MAYBE_COLLECT(M) \
            for (const auto& req : requested_tests) \
                if (req == #M) { tests_to_run.push_back(#M); break; }
        #define SKIP_ARGV_2(M)
        FOR_EACH_TEST(MAYBE_COLLECT, SKIP_ARGV_2)
        #undef MAYBE_COLLECT
        #undef SKIP_ARGV_2
    }

    if (tests_to_run.empty()) {
        std::cout << "No tests to run in parallel mode." << std::endl;
        return 0;
    }

    unsigned total = static_cast<unsigned>(tests_to_run.size());
    if (num_jobs > total)
        num_jobs = total;

    std::cout << "Running " << total << " tests with "
              << num_jobs << " parallel jobs..." << std::endl;

    auto wall_start = std::chrono::steady_clock::now();

    std::mutex queue_mtx;
    std::mutex output_mtx;
    size_t next_idx = 0;
    unsigned completed = 0;
    unsigned passed = 0;
    unsigned failed = 0;
    std::vector<std::string> failed_names;

    auto worker = [&]() {
        while (true) {
            size_t idx;
            {
                std::lock_guard<std::mutex> lock(queue_mtx);
                if (next_idx >= tests_to_run.size())
                    return;
                idx = next_idx++;
            }

            test_result result = run_test_child(exe_path, tests_to_run[idx].c_str(), extra_args);

            {
                std::lock_guard<std::mutex> lock(output_mtx);
                ++completed;
                if (result.exit_code == 0) {
                    ++passed;
                    std::cout << "[" << completed << "/" << total << "] "
                              << result.name << " PASS ("
                              << std::fixed << std::setprecision(1)
                              << result.elapsed_secs << "s)" << std::endl;
                }
                else {
                    ++failed;
                    failed_names.push_back(result.name);
                    std::cout << "[" << completed << "/" << total << "] "
                              << result.name << " FAIL (exit code "
                              << result.exit_code << ", "
                              << std::fixed << std::setprecision(1)
                              << result.elapsed_secs << "s)" << std::endl;
                }
                if (!result.output.empty()) {
                    std::cout << result.output;
                    if (result.output.back() != '\n')
                        std::cout << std::endl;
                }
            }
        }
    };

    std::vector<std::thread> threads;
    for (unsigned i = 0; i < num_jobs; ++i)
        threads.emplace_back(worker);
    for (auto& t : threads)
        t.join();

    auto wall_end = std::chrono::steady_clock::now();
    double wall_secs = std::chrono::duration<double>(wall_end - wall_start).count();

    std::cout << "\n=== Test Summary ===" << std::endl;
    std::cout << passed << " passed, " << failed << " failed, "
              << total << " total" << std::endl;
    std::cout << "Wall time: " << std::fixed << std::setprecision(1)
              << wall_secs << "s" << std::endl;

    if (!failed_names.empty()) {
        std::cout << "Failed tests:";
        for (const auto& name : failed_names)
            std::cout << " " << name;
        std::cout << std::endl;
    }

    return failed > 0 ? 1 : 0;
}

#endif // !__EMSCRIPTEN__


// ========================================================================
// main
// ========================================================================

int main(int argc, char ** argv) {
    memory::initialize(0);

    // Collect potential test names before parsing modifies argv
    std::vector<std::string> requested_tests;
    for (int i = 1; i < argc; ++i) {
        const char* a = argv[i];
        if (a[0] != '-' && a[0] != '/' && !strchr(a, '='))
            requested_tests.push_back(a);
    }

    bool do_display_usage = false;
    bool test_all = false;
#ifndef __EMSCRIPTEN__
    unsigned hw = std::thread::hardware_concurrency();
    unsigned num_jobs = hw > 0 ? hw : 4;
#else
    unsigned num_jobs = 0;
#endif
    std::vector<std::string> extra_args;
    parse_cmd_line_args(argc, argv, do_display_usage, test_all, num_jobs, extra_args);

    if (do_display_usage) {
        #define DISPLAY_TST(M) std::cout << "    " << #M << "\n";
        #define DISPLAY_TST_ARGV(M) std::cout << "    " << #M << "(...)\n";
        FOR_EACH_TEST(DISPLAY_TST, DISPLAY_TST_ARGV)
        #undef DISPLAY_TST
        #undef DISPLAY_TST_ARGV
        return 0;
    }

#ifndef __EMSCRIPTEN__
    if (num_jobs > 0)
        return run_parallel(argv[0], test_all, num_jobs, extra_args, requested_tests);
#endif

    // Serial execution, original behavior
    #define RUN_TST(M) { \
        bool run = test_all; \
        for (int i = 0; !run && i < argc; ++i) \
            run = strcmp(argv[i], #M) == 0; \
        if (run) { \
            std::string s("test "); \
            s += #M; \
            enable_debug(#M); \
            timeit timeit(true, s.c_str()); \
            tst_##M(); \
            std::cout << "PASS" << std::endl; \
        } \
    }

    #define RUN_TST_ARGV(M) { \
        for (int i = 0; i < argc; ++i) \
            if (strcmp(argv[i], #M) == 0) { \
                enable_trace(#M); \
                enable_debug(#M); \
                std::string s("test "); \
                s += #M; \
                timeit timeit(true, s.c_str()); \
                tst_##M(argv, argc, i); \
                std::cout << "PASS" << std::endl; \
            } \
    }

    FOR_EACH_ALL_TEST(RUN_TST, RUN_TST_ARGV)
    if (test_all) return 0;
    FOR_EACH_EXTRA_TEST(RUN_TST, RUN_TST_ARGV)

    #undef RUN_TST
    #undef RUN_TST_ARGV
    return 0;
}
