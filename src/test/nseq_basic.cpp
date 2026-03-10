/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_basic.cpp

Abstract:

    Basic unit tests for theory_nseq and supporting infrastructure.

--*/
#include "util/util.h"
#include "ast/reg_decl_plugins.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_nielsen.h"
#include "params/smt_params.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_context.h"
#include "smt/theory_nseq.h"
#include <iostream>

// Trivial solver that always returns sat and ignores all assertions.
class nseq_basic_dummy_solver : public seq::simple_solver {
public:
    void push() override {}
    void pop(unsigned) override {}
    void assert_expr(expr*) override {}
    lbool check() override { return l_true; }
};

// Test 1: instantiation of nielsen_graph compiles and doesn't crash
static void test_nseq_instantiation() {
    std::cout << "test_nseq_instantiation\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::nielsen_graph ng(sg, solver);
    SASSERT(ng.root() == nullptr);
    SASSERT(ng.num_nodes() == 0);
    std::cout << "  ok\n";
}

// Test 2: parameter validation accepts "nseq"
static void test_nseq_param_validation() {
    std::cout << "test_nseq_param_validation\n";
    smt_params p;
    // Should not throw
    try {
        p.validate_string_solver(symbol("nseq"));
        std::cout << "  ok: nseq accepted\n";
    } catch (...) {
        SASSERT(false && "nseq should be accepted as a valid string_solver value");
    }
    // Should not throw for legacy values
    try {
        p.validate_string_solver(symbol("seq"));
        p.validate_string_solver(symbol("auto"));
        p.validate_string_solver(symbol("none"));
        std::cout << "  ok: legacy values still accepted\n";
    } catch (...) {
        SASSERT(false && "legacy values should still be accepted");
    }
}

// Test 2b: parameter validation rejects invalid variants of "nseq"
static void test_nseq_param_validation_rejects_invalid() {
    std::cout << "test_nseq_param_validation_rejects_invalid\n";
    smt_params p;
    static const char* invalid_variants[] = { "nseq2", "NSEQ", "nseqq", "nse", "Nseq", "nseq ", "" };
    for (auto s : invalid_variants) {
        bool threw = false;
        try {
            p.validate_string_solver(symbol(s));
        } catch (...) {
            threw = true;
        }
        if (!threw) {
            std::cerr << "  FAIL: '" << s << "' should have been rejected\n";
            SASSERT(false && "invalid string solver variant was accepted");
        }
    }
    std::cout << "  ok: all invalid variants rejected\n";
}

// Test 3: nielsen graph simplification (trivial case)
static void test_nseq_simplification() {
    std::cout << "test_nseq_simplification\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::nielsen_graph ng(sg, solver);

    // Add a trivial equality: empty = empty
    euf::snode* empty1 = sg.mk_empty();
    euf::snode* empty2 = sg.mk_empty();

    ng.add_str_eq(empty1, empty2);

    seq::nielsen_graph::search_result r = ng.solve();
    // empty = empty is trivially satisfied
    SASSERT(r == seq::nielsen_graph::search_result::sat);
    std::cout << "  ok: trivial equality solved as sat\n";
}

// Test 4: node is_satisfied check
static void test_nseq_node_satisfied() {
    std::cout << "test_nseq_node_satisfied\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::nielsen_graph ng(sg, solver);

    seq::nielsen_node* node = ng.mk_node();
    // empty node has no constraints => satisfied
    SASSERT(node->is_satisfied());

    // add a trivial equality
    euf::snode* empty = sg.mk_empty();
    seq::dep_tracker dep;
    seq::str_eq eq(empty, empty, dep);
    node->add_str_eq(eq);
    SASSERT(node->str_eqs().size() == 1);
    SASSERT(!node->str_eqs()[0].is_trivial() || node->str_eqs()[0].m_lhs == node->str_eqs()[0].m_rhs);
    // After simplification, trivial equalities should be removed
    seq::simplify_result sr = node->simplify_and_init(ng);
    VERIFY(sr == seq::simplify_result::satisfied || sr == seq::simplify_result::proceed);
    std::cout << "  ok\n";
}

// Test 5: symbol clash conflict ("a" = "b" is unsat)
static void test_nseq_symbol_clash() {
    std::cout << "test_nseq_symbol_clash\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* a = sg.mk_char('a');
    euf::snode* b = sg.mk_char('b');
    ng.add_str_eq(a, b);

    auto r = ng.solve();
    SASSERT(r == seq::nielsen_graph::search_result::unsat);

    // verify conflict explanation returns the equality index
    unsigned_vector eq_idx, mem_idx;
    ng.explain_conflict(eq_idx, mem_idx);
    SASSERT(eq_idx.size() == 1);
    SASSERT(eq_idx[0] == 0);
    SASSERT(mem_idx.empty());
    std::cout << "  ok: symbol clash detected as unsat\n";
}

// Test 6: variable equality x = x is sat
static void test_nseq_var_eq_self() {
    std::cout << "test_nseq_var_eq_self\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    ng.add_str_eq(x, x);

    auto r = ng.solve();
    SASSERT(r == seq::nielsen_graph::search_result::sat);
    std::cout << "  ok: x = x solved as sat\n";
}

// Test 7: x·a = x·b is unsat (prefix match then clash)
static void test_nseq_prefix_clash() {
    std::cout << "test_nseq_prefix_clash\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a = sg.mk_char('a');
    euf::snode* b = sg.mk_char('b');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* xb = sg.mk_concat(x, b);

    ng.add_str_eq(xa, xb);
    auto r = ng.solve();
    SASSERT(r == seq::nielsen_graph::search_result::unsat);
    std::cout << "  ok: x·a = x·b detected as unsat\n";
}

// Test 8: a·x = a·y has solutions (not unsat)
static void test_nseq_const_nielsen_solvable() {
    std::cout << "test_nseq_const_nielsen_solvable\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('a');
    euf::snode* ax = sg.mk_concat(a, x);
    euf::snode* ay = sg.mk_concat(a, y);

    ng.add_str_eq(ax, ay);
    auto r = ng.solve();
    // a·x = a·y simplifies to x = y which is satisfiable (x = y = ε)
    SASSERT(r == seq::nielsen_graph::search_result::sat);
    std::cout << "  ok: a·x = a·y solved as sat\n";
}

// Test 9: length mismatch - "ab" = "a" is unsat
static void test_nseq_length_mismatch() {
    std::cout << "test_nseq_length_mismatch\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* a = sg.mk_char('a');
    euf::snode* b = sg.mk_char('b');
    euf::snode* ab = sg.mk_concat(a, b);

    ng.add_str_eq(ab, a);
    auto r = ng.solve();
    SASSERT(r == seq::nielsen_graph::search_result::unsat);
    std::cout << "  ok: ab = a detected as unsat\n";
}

// Test 10: setup_seq_str dispatches to setup_nseq() when string_solver == "nseq"
static void test_setup_seq_str_dispatches_nseq() {
    std::cout << "test_setup_seq_str_dispatches_nseq\n";
    ast_manager m;
    reg_decl_plugins(m);

    smt_params params;
    params.m_string_solver = symbol("nseq");

    smt::context ctx(m, params);

    // Assert a string equality to trigger string theory setup during check()
    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    app_ref x(m.mk_const(symbol("x_setup_test"), str_sort), m);
    app_ref eq(m.mk_eq(x.get(), x.get()), m);
    ctx.assert_expr(eq);
    ctx.check();

    // Verify that theory_nseq (not theory_seq) was registered for the "seq" family
    family_id seq_fid = m.mk_family_id("seq");
    SASSERT(ctx.get_theory(seq_fid) != nullptr);
    SASSERT(dynamic_cast<smt::theory_nseq*>(ctx.get_theory(seq_fid)) != nullptr);
    std::cout << "  ok: setup_seq_str dispatched to setup_nseq for 'nseq'\n";
}

void tst_nseq_basic() {
    test_nseq_instantiation();
    test_nseq_param_validation();
    test_nseq_param_validation_rejects_invalid();
    test_nseq_simplification();
    test_nseq_node_satisfied();
    test_nseq_symbol_clash();
    test_nseq_var_eq_self();
    test_nseq_prefix_clash();
    test_nseq_const_nielsen_solvable();
    test_nseq_length_mismatch();
    test_setup_seq_str_dispatches_nseq();
    std::cout << "nseq_basic: all tests passed\n";
}
