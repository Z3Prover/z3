/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_parikh.cpp

Abstract:

    Unit tests for seq_parikh (Parikh image filter for the ZIPT Nielsen solver).

    Tests cover:
    - compute_length_stride / get_length_stride for all regex forms
    - generate_parikh_constraints: constraint shape, count, and dependency
    - apply_to_node: integration with nielsen_node
    - check_parikh_conflict: lightweight feasibility pre-check
    - minterm_to_char_set: regex-minterm to char_set conversion

Author:

    Clemens Eisenhofer 2026-03-11
    Nikolaj Bjorner (nbjorner) 2026-03-11

--*/

#include "util/util.h"
#include "util/zstring.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_nielsen.h"
#include "smt/seq/seq_parikh.h"
#include "smt/seq/seq_regex.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include <iostream>

// ---------------------------------------------------------------------------
// Minimal solver stub (no-op)
// ---------------------------------------------------------------------------
class parikh_test_solver : public seq::simple_solver {
public:
    void push() override {}
    void pop(unsigned) override {}
    void assert_expr(expr*) override {}
    void reset() override {}
    lbool check() override { return l_true; }
};

// ---------------------------------------------------------------------------
// Helpers to build common regex expressions
// ---------------------------------------------------------------------------

// build to_re("AB") — a fixed two-character string regex
static expr_ref mk_to_re_ab(ast_manager& m, seq_util& seq) {
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref ab(seq.str.mk_concat(unit_a, unit_b), m);
    return expr_ref(seq.re.mk_to_re(ab), m);
}

// build (ab)* — star of the two-character sequence
static expr_ref mk_ab_star(ast_manager& m, seq_util& seq) {
    return expr_ref(seq.re.mk_star(mk_to_re_ab(m, seq)), m);
}

// build (abc)* — star of a three-character sequence
static expr_ref mk_abc_star(ast_manager& m, seq_util& seq) {
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref ch_c(seq.str.mk_char('C'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref unit_c(seq.str.mk_unit(ch_c), m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);
    expr_ref abc(seq.str.mk_concat(unit_a, seq.str.mk_concat(unit_b, unit_c)), m);
    return expr_ref(seq.re.mk_star(seq.re.mk_to_re(abc)), m);
}

// build to_re("A") — single-character regex
static expr_ref mk_to_re_a(ast_manager& m, seq_util& seq) {
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    return expr_ref(seq.re.mk_to_re(unit_a), m);
}

// ---------------------------------------------------------------------------
// Stride tests: compute_length_stride / get_length_stride
// ---------------------------------------------------------------------------

// stride(to_re("AB")) == 0 (fixed length)
static void test_stride_fixed_length() {
    std::cout << "test_stride_fixed_length\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);

    expr_ref re = mk_to_re_ab(m, seq);
    SASSERT(parikh.get_length_stride(re) == 0);
}

// stride((ab)*) == 2
static void test_stride_star_fixed_body() {
    std::cout << "test_stride_star_fixed_body\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);

    expr_ref re = mk_ab_star(m, seq);
    unsigned stride = parikh.get_length_stride(re);
    std::cout << "  stride((ab)*) = " << stride << "\n";
    SASSERT(stride == 2);
}

// stride((abc)*) == 3
static void test_stride_star_three_char() {
    std::cout << "test_stride_star_three_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);

    expr_ref re = mk_abc_star(m, seq);
    unsigned stride = parikh.get_length_stride(re);
    std::cout << "  stride((abc)*) = " << stride << "\n";
    SASSERT(stride == 3);
}

// stride((ab)+) == 2
static void test_stride_plus() {
    std::cout << "test_stride_plus\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);

    expr_ref re_body = mk_to_re_ab(m, seq);
    expr_ref re(seq.re.mk_plus(re_body), m);
    unsigned stride = parikh.get_length_stride(re);
    std::cout << "  stride((ab)+) = " << stride << "\n";
    SASSERT(stride == 2);
}

// stride(a* b*) == 1 — union of independent stars → every length possible
static void test_stride_concat_stars() {
    std::cout << "test_stride_concat_stars\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);

    expr_ref a_star(seq.re.mk_star(mk_to_re_a(m, seq)), m);
    expr_ref b_star(seq.re.mk_star(mk_to_re_a(m, seq)), m);
    expr_ref re(seq.re.mk_concat(a_star, b_star), m);
    unsigned stride = parikh.get_length_stride(re);
    std::cout << "  stride(a* b*) = " << stride << "\n";
    // both stars have stride 1 (single-char body → gcd(1,0)=1) → gcd(1,1)=1
    SASSERT(stride == 1);
}

// stride((ab)* | (abc)*) == gcd(2,3) = 1
static void test_stride_union_no_common_period() {
    std::cout << "test_stride_union_no_common_period\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);

    expr_ref ab_star = mk_ab_star(m, seq);
    expr_ref abc_star = mk_abc_star(m, seq);
    expr_ref re(seq.re.mk_union(ab_star, abc_star), m);
    unsigned stride = parikh.get_length_stride(re);
    std::cout << "  stride((ab)*|(abc)*) = " << stride << "\n";
    // lengths: {0,2,4,...} union {0,3,6,...} → GCD(2,3)=1
    SASSERT(stride == 1);
}

// stride((ab)*|(de)*) == gcd(2,2) = 2
static void test_stride_union_same_period() {
    std::cout << "test_stride_union_same_period\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);

    expr_ref ab_star = mk_ab_star(m, seq);
    // de_star: (de)* — same stride 2
    expr_ref ch_d(seq.str.mk_char('D'), m);
    expr_ref ch_e(seq.str.mk_char('E'), m);
    expr_ref unit_d(seq.str.mk_unit(ch_d), m);
    expr_ref unit_e(seq.str.mk_unit(ch_e), m);
    expr_ref de(seq.str.mk_concat(unit_d, unit_e), m);
    expr_ref de_star(seq.re.mk_star(seq.re.mk_to_re(de)), m);
    expr_ref re(seq.re.mk_union(ab_star, de_star), m);
    unsigned stride = parikh.get_length_stride(re);
    std::cout << "  stride((ab)*|(de)*) = " << stride << "\n";
    SASSERT(stride == 2);
}

// stride(loop((ab), 1, 3)) == 2 — loop with fixed-length body
static void test_stride_loop() {
    std::cout << "test_stride_loop\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);

    expr_ref ab = mk_to_re_ab(m, seq);
    expr_ref re(seq.re.mk_loop(ab, 1, 3), m);
    unsigned stride = parikh.get_length_stride(re);
    std::cout << "  stride(loop(ab,1,3)) = " << stride << "\n";
    SASSERT(stride == 2);
}

// stride(re.full_seq) == 1 (every length possible)
static void test_stride_full_seq() {
    std::cout << "test_stride_full_seq\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref re(seq.re.mk_full_seq(str_sort), m);
    unsigned stride = parikh.get_length_stride(re);
    std::cout << "  stride(.*)  = " << stride << "\n";
    SASSERT(stride == 1);
}

// stride(re.empty) == 0
static void test_stride_empty_regex() {
    std::cout << "test_stride_empty_regex\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref re(seq.re.mk_empty(str_sort), m);
    unsigned stride = parikh.get_length_stride(re);
    std::cout << "  stride(empty) = " << stride << "\n";
    SASSERT(stride == 0);
}

// stride(re.epsilon) == 0
static void test_stride_epsilon() {
    std::cout << "test_stride_epsilon\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    // epsilon is to_re("") — empty string
    sort_ref str_s(seq.str.mk_string_sort(), m);
    expr_ref empty_str(seq.str.mk_empty(str_s), m);
    expr_ref re(seq.re.mk_to_re(empty_str), m);
    unsigned stride = parikh.get_length_stride(re);
    std::cout << "  stride(epsilon) = " << stride << "\n";
    SASSERT(stride == 0);
}

// stride((ab)?) == 2  (gcd(2, 0) = 2 via opt handling; min_len(ab)=2)
static void test_stride_opt() {
    std::cout << "test_stride_opt\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_parikh parikh(sg);
    seq_util seq(m);

    expr_ref ab = mk_to_re_ab(m, seq);
    expr_ref re(seq.re.mk_opt(ab), m);
    unsigned stride = parikh.get_length_stride(re);
    std::cout << "  stride((ab)?) = " << stride << "\n";
    SASSERT(stride == 2);
}

// ---------------------------------------------------------------------------
// generate_parikh_constraints tests
// ---------------------------------------------------------------------------

// (ab)* → len(x) = 0 + 2·k, k ≥ 0  (stride 2, min_len 0)
static void test_generate_constraints_ab_star() {
    std::cout << "test_generate_constraints_ab_star\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    arith_util arith(m);
    seq::seq_parikh parikh(sg);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    expr_ref re = mk_ab_star(m, seq);
    euf::snode* regex = sg.mk(re);
    seq::dep_manager dm;
    sat::literal lit = sat::null_literal;  // dummy literal for dependency tracking 
    seq::dep_tracker dep = dm.mk_leaf(lit);
    seq::str_mem mem(x, regex, nullptr, 0, dep);

    vector<seq::int_constraint> out;
    parikh.generate_parikh_constraints(mem, out);

    // expect at least: len(x)=0+2k and k>=0
    // (no upper bound because max_length is UINT_MAX for unbounded star)
    std::cout << "  generated " << out.size() << " constraints\n";
    SASSERT(out.size() >= 2);

    // check that one constraint is an equality (len(x) = 0 + 2·k)
    bool has_eq = false;
    for (auto const& ic : out)
        if (ic.m_kind == seq::int_constraint_kind::eq) has_eq = true;
    SASSERT(has_eq);

    // check that one constraint is k >= 0
    bool has_ge = false;
    for (auto const& ic : out)
        if (ic.m_kind == seq::int_constraint_kind::ge) has_ge = true;
    SASSERT(has_ge);

    // should NOT have an upper bound (star is unbounded)
    bool has_le = false;
    for (auto const& ic : out)
        if (ic.m_kind == seq::int_constraint_kind::le) has_le = true;
    SASSERT(!has_le);
}

// loop((ab), 1, 3): bounded → k ≤ floor((6-2)/2) = 2
static void test_generate_constraints_bounded_loop() {
    std::cout << "test_generate_constraints_bounded_loop\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    seq::seq_parikh parikh(sg);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    // loop("ab", 1, 3): min_len=2, max_len=6, stride=2
    expr_ref ab = mk_to_re_ab(m, seq);
    expr_ref re(seq.re.mk_loop(ab, 1, 3), m);
    euf::snode* regex = sg.mk(re);
    seq::dep_manager dm;
    seq::dep_tracker dep = dm.mk_leaf(sat::null_literal);
    seq::str_mem mem(x, regex, nullptr, 0, dep);

    vector<seq::int_constraint> out;
    parikh.generate_parikh_constraints(mem, out);

    // expect: eq + ge + le = 3 constraints
    std::cout << "  generated " << out.size() << " constraints\n";
    SASSERT(out.size() == 3);

    bool has_eq = false, has_ge = false, has_le = false;
    for (auto const& ic : out) {
        if (ic.m_kind == seq::int_constraint_kind::eq)  has_eq = true;
        if (ic.m_kind == seq::int_constraint_kind::ge)  has_ge = true;
        if (ic.m_kind == seq::int_constraint_kind::le)  has_le = true;
    }
    SASSERT(has_eq);
    SASSERT(has_ge);
    SASSERT(has_le);
}

// stride == 1 → no constraints generated
static void test_generate_constraints_stride_one() {
    std::cout << "test_generate_constraints_stride_one\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    seq::seq_parikh parikh(sg);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    // full_seq: stride=1 → no modular constraint
    expr_ref re(seq.re.mk_full_seq(str_sort), m);
    euf::snode* regex = sg.mk(re);
    seq::dep_manager dm;
    seq::dep_tracker dep = dm.mk_leaf(sat::null_literal);
    seq::str_mem mem(x, regex, nullptr, 0, dep);

    vector<seq::int_constraint> out;
    parikh.generate_parikh_constraints(mem, out);
    std::cout << "  generated " << out.size() << " constraints (expect 0)\n";
    SASSERT(out.empty());
}

// fixed-length regex (min == max) → no constraints generated
static void test_generate_constraints_fixed_length() {
    std::cout << "test_generate_constraints_fixed_length\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    seq::seq_parikh parikh(sg);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    expr_ref re = mk_to_re_ab(m, seq);  // fixed len 2
    euf::snode* regex = sg.mk(re);
    seq::dep_manager dm;
    seq::dep_tracker dep = dm.mk_leaf(sat::null_literal);
    seq::str_mem mem(x, regex, nullptr, 0, dep);

    vector<seq::int_constraint> out;
    parikh.generate_parikh_constraints(mem, out);
    std::cout << "  generated " << out.size() << " constraints (expect 0)\n";
    SASSERT(out.empty());
}

// dependency is propagated to all generated constraints
static void test_generate_constraints_dep_propagated() {
    std::cout << "test_generate_constraints_dep_propagated\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    seq::seq_parikh parikh(sg);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    expr_ref re = mk_ab_star(m, seq);
    euf::snode* regex = sg.mk(re);
    seq::dep_manager dm;
    sat::literal lit(7);
    seq::dep_tracker dep = dm.mk_leaf(lit);
    seq::str_mem mem(x, regex, nullptr, 0, dep);

    vector<seq::int_constraint> out;
    parikh.generate_parikh_constraints(mem, out);

    // all generated constraints must carry dep_source{mem,7} in their dependency
    for (auto const& ic : out) {
        SASSERT(ic.m_dep != nullptr);
        vector<seq::dep_source, false> vs;
        dm.linearize(ic.m_dep, vs);
        bool found = false;
        for (auto const& d : vs)
            if (std::get<sat::literal>(d) == lit) found = true;
        SASSERT(found);
    }
    std::cout << "  all constraints carry dep {mem,7}\n";
}

// ---------------------------------------------------------------------------
// apply_to_node tests
// ---------------------------------------------------------------------------

// applying to a node with one membership adds constraints to node
static void test_apply_to_node_adds_constraints() {
    std::cout << "test_apply_to_node_adds_constraints\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    parikh_test_solver solver;
    seq::nielsen_graph ng(sg, solver);
    seq::seq_parikh parikh(sg);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    expr_ref re = mk_ab_star(m, seq);  // stride 2 → generates constraints
    euf::snode* regex = sg.mk(re);
    ng.add_str_mem(x, regex);

    // root node should have no int_constraints initially
    SASSERT(ng.root() != nullptr);
    unsigned before = ng.root()->int_constraints().size();

    parikh.apply_to_node(*ng.root());

    unsigned after = ng.root()->int_constraints().size();
    std::cout << "  before=" << before << " after=" << after << "\n";
    SASSERT(after > before);
}

// applying twice is idempotent (m_parikh_applied would prevent double-add
// via nielsen_graph::apply_parikh_to_node, but seq_parikh::apply_to_node
// itself does not guard — so calling apply_to_node directly adds again;
// this test verifies the direct call does add, not the idempotency guard)
static void test_apply_to_node_stride_one_no_constraints() {
    std::cout << "test_apply_to_node_stride_one_no_constraints\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);
    parikh_test_solver solver;
    seq::nielsen_graph ng(sg, solver);
    seq::seq_parikh parikh(sg);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    expr_ref re(seq.re.mk_full_seq(str_sort), m);  // stride 1 → no constraints
    euf::snode* regex = sg.mk(re);
    ng.add_str_mem(x, regex);

    unsigned before = ng.root()->int_constraints().size();
    parikh.apply_to_node(*ng.root());
    unsigned after = ng.root()->int_constraints().size();
    std::cout << "  before=" << before << " after=" << after << " (expect no change)\n";
    SASSERT(after == before);
}

// ---------------------------------------------------------------------------
// check_parikh_conflict tests
// ---------------------------------------------------------------------------

// no conflict when var_lb=0, var_ub=UINT_MAX (unconstrained)
static void test_check_conflict_unconstrained_no_conflict() {
    std::cout << "test_check_conflict_unconstrained_no_conflict\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    parikh_test_solver solver;
    seq::nielsen_graph ng(sg, solver);
    seq::seq_parikh parikh(sg);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    expr_ref re = mk_ab_star(m, seq);  // stride 2, min_len 0
    euf::snode* regex = sg.mk(re);
    ng.add_str_mem(x, regex);

    // no bounds set → default lb=0, ub=UINT_MAX → no conflict
    bool conflict = parikh.check_parikh_conflict(*ng.root());
    std::cout << "  conflict = " << conflict << " (expect 0)\n";
    SASSERT(!conflict);
}

// conflict: lb=3, ub=5, stride=2, min_len=0
// valid lengths: 0,2,4,6,... ∩ [3,5] = {4} → no conflict
static void test_check_conflict_valid_k_exists() {
    std::cout << "test_check_conflict_valid_k_exists\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    parikh_test_solver solver;
    seq::nielsen_graph ng(sg, solver);
    seq::seq_parikh parikh(sg);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    expr_ref re = mk_ab_star(m, seq);  // stride 2, min_len 0; lengths 0,2,4,...
    euf::snode* regex = sg.mk(re);
    ng.add_str_mem(x, regex);

    // lb=3, ub=5: length 4 is achievable (k=2) → no conflict
    seq::dep_tracker dep = ng.dep_mgr().mk_leaf(sat::literal(0));
    ng.root()->add_lower_int_bound(x, 3, dep);
    ng.root()->add_upper_int_bound(x, 5, dep);

    bool conflict = parikh.check_parikh_conflict(*ng.root());
    std::cout << "  conflict = " << conflict << " (expect 0)\n";
    SASSERT(!conflict);
}

// conflict: lb=3, ub=3, stride=2, min_len=0
// valid lengths: {0,2,4,...} ∩ [3,3] = {} → conflict
static void test_check_conflict_no_valid_k() {
    std::cout << "test_check_conflict_no_valid_k\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    parikh_test_solver solver;
    seq::nielsen_graph ng(sg, solver);
    seq::seq_parikh parikh(sg);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    expr_ref re = mk_ab_star(m, seq);  // stride 2, min_len 0; lengths {0,2,4,...}
    euf::snode* regex = sg.mk(re);
    ng.add_str_mem(x, regex);

    // lb=3, ub=3: only odd length 3 — never a multiple of 2 → conflict
    seq::dep_tracker dep = ng.dep_mgr().mk_leaf(sat::literal(0));
    ng.root()->add_lower_int_bound(x, 3, dep);
    ng.root()->add_upper_int_bound(x, 3, dep);

    bool conflict = parikh.check_parikh_conflict(*ng.root());
    std::cout << "  conflict = " << conflict << " (expect 1)\n";
    SASSERT(conflict);
}

// conflict: lb=5, ub=5, stride=3, min_len=0
// valid lengths of (abc)*: {0,3,6,...} ∩ {5} = {} → conflict
static void test_check_conflict_abc_star() {
    std::cout << "test_check_conflict_abc_star\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    parikh_test_solver solver;
    seq::nielsen_graph ng(sg, solver);
    seq::seq_parikh parikh(sg);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    expr_ref re = mk_abc_star(m, seq);  // stride 3, min_len 0; lengths {0,3,6,...}
    euf::snode* regex = sg.mk(re);
    ng.add_str_mem(x, regex);

    // lb=5, ub=5 → no valid k (5 is not a multiple of 3) → conflict
    seq::dep_tracker dep = ng.dep_mgr().mk_leaf(sat::literal(0));
    ng.root()->add_lower_int_bound(x, 5, dep);
    ng.root()->add_upper_int_bound(x, 5, dep);

    bool conflict = parikh.check_parikh_conflict(*ng.root());
    std::cout << "  conflict = " << conflict << " (expect 1)\n";
    SASSERT(conflict);
}

// no conflict for stride==1 regex even with narrow bounds
static void test_check_conflict_stride_one_never_conflicts() {
    std::cout << "test_check_conflict_stride_one_never_conflicts\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);
    parikh_test_solver solver;
    seq::nielsen_graph ng(sg, solver);
    seq::seq_parikh parikh(sg);

    euf::snode* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    expr_ref re(seq.re.mk_full_seq(str_sort), m);  // stride 1 → no constraint
    euf::snode* regex = sg.mk(re);
    ng.add_str_mem(x, regex);

    seq::dep_tracker dep = ng.dep_mgr().mk_leaf(sat::literal(0));
    ng.root()->add_lower_int_bound(x, 7, dep);
    ng.root()->add_upper_int_bound(x, 7, dep);

    bool conflict = parikh.check_parikh_conflict(*ng.root());
    std::cout << "  conflict = " << conflict << " (expect 0: stride=1 skipped)\n";
    SASSERT(!conflict);
}

// ---------------------------------------------------------------------------
// minterm_to_char_set tests
// ---------------------------------------------------------------------------

// re.full_char → full alphabet [0, max_char]
static void test_minterm_full_char() {
    std::cout << "test_minterm_full_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    seq::seq_regex regex(sg);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref re(seq.re.mk_full_char(str_sort), m);
    char_set cs = regex.minterm_to_char_set(re);
    std::cout << "  full_char char_count = " << cs.char_count() << "\n";
    SASSERT(cs.is_full(seq.max_char()));
}

// re.empty → empty char_set
static void test_minterm_empty_regex() {
    std::cout << "test_minterm_empty_regex\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    seq::seq_regex regex(sg);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref re(seq.re.mk_empty(str_sort), m);
    char_set cs = regex.minterm_to_char_set(re);
    std::cout << "  empty regex → char_set empty: " << cs.is_empty() << "\n";
    SASSERT(cs.is_empty());
}

// re.range('A','Z') → 26 characters
static void test_minterm_range() {
    std::cout << "test_minterm_range\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    seq::seq_regex regex(sg);

    // Z3 re.range takes string arguments "A" and "Z"
    expr_ref lo_str(seq.str.mk_string(zstring("A")), m);
    expr_ref hi_str(seq.str.mk_string(zstring("Z")), m);
    expr_ref re(seq.re.mk_range(lo_str, hi_str), m);
    char_set cs = regex.minterm_to_char_set(re);
    std::cout << "  range(A,Z) char_count = " << cs.char_count() << "\n";
    SASSERT(cs.char_count() == 26);
    SASSERT(cs.contains('A'));
    SASSERT(cs.contains('Z'));
    SASSERT(!cs.contains('a'));
}

// complement of re.range('A','Z') should not contain A-Z
static void test_minterm_complement() {
    std::cout << "test_minterm_complement\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    seq::seq_regex regex(sg);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref lo_str(seq.str.mk_string(zstring("A")), m);
    expr_ref hi_str(seq.str.mk_string(zstring("Z")), m);
    expr_ref range(seq.re.mk_range(lo_str, hi_str), m);
    expr_ref re(seq.re.mk_complement(range), m);
    char_set cs = regex.minterm_to_char_set(re);

    // complement of [A-Z] should not contain any letter in A-Z
    for (unsigned c = 'A'; c <= 'Z'; ++c)
        SASSERT(!cs.contains(c));
    // but should contain e.g. '0'
    SASSERT(cs.contains('0'));
    std::cout << "  complement ok: A-Z excluded, '0' included\n";
}

// intersection of range('A','Z') and range('M','Z') == range('M','Z')
static void test_minterm_intersection() {
    std::cout << "test_minterm_intersection\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    seq::seq_regex regex(sg);

    expr_ref lo_az(seq.str.mk_string(zstring("A")), m);
    expr_ref hi_az(seq.str.mk_string(zstring("Z")), m);
    expr_ref lo_mz(seq.str.mk_string(zstring("M")), m);

    expr_ref range_az(seq.re.mk_range(lo_az, hi_az), m);
    expr_ref range_mz(seq.re.mk_range(lo_mz, hi_az), m);
    expr_ref re(seq.re.mk_inter(range_az, range_mz), m);
    char_set cs = regex.minterm_to_char_set(re);

    // intersection [A-Z] ∩ [M-Z] = [M-Z]: 14 characters
    std::cout << "  intersection [A-Z]∩[M-Z] char_count = " << cs.char_count() << "\n";
    SASSERT(cs.char_count() == 14); // M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z
    SASSERT(!cs.contains('A'));
    SASSERT(cs.contains('M'));
    SASSERT(cs.contains('Z'));
}

// diff(range('A','Z'), range('A','M')) == range('N','Z')
static void test_minterm_diff() {
    std::cout << "test_minterm_diff\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    seq::seq_regex regex(sg);

    expr_ref lo_az(seq.str.mk_string(zstring("A")), m);
    expr_ref hi_az(seq.str.mk_string(zstring("Z")), m);
    expr_ref lo_am(seq.str.mk_string(zstring("A")), m);
    expr_ref hi_am(seq.str.mk_string(zstring("M")), m);

    expr_ref range_az(seq.re.mk_range(lo_az, hi_az), m);
    expr_ref range_am(seq.re.mk_range(lo_am, hi_am), m);
    expr_ref re(seq.re.mk_diff(range_az, range_am), m);
    char_set cs = regex.minterm_to_char_set(re);

    // diff [A-Z] \ [A-M] = [N-Z]: 13 characters
    std::cout << "  diff [A-Z]\\[A-M] char_count = " << cs.char_count() << "\n";
    SASSERT(cs.char_count() == 13); // N..Z
    SASSERT(!cs.contains('A'));
    SASSERT(!cs.contains('M'));
    SASSERT(cs.contains('N'));
    SASSERT(cs.contains('Z'));
}

// to_re(unit('A')) → singleton {'A'}
static void test_minterm_singleton() {
    std::cout << "test_minterm_singleton\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    seq::seq_regex regex(sg);

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref re(seq.re.mk_to_re(unit_a), m);
    char_set cs = regex.minterm_to_char_set(re);

    std::cout << "  singleton char_count = " << cs.char_count() << "\n";
    SASSERT(cs.char_count() == 1);
    SASSERT(cs.contains('A'));
    SASSERT(!cs.contains('B'));
}

// nullptr → full set (conservative fallback)
static void test_minterm_nullptr_is_full() {
    std::cout << "test_minterm_nullptr_is_full\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex regex(sg);
    seq_util seq(m);

    char_set cs = regex.minterm_to_char_set(nullptr);
    SASSERT(cs.is_full(seq.max_char()));
    std::cout << "  nullptr → full set ok\n";
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

void tst_seq_parikh() {
    // stride tests
    test_stride_fixed_length();
    test_stride_star_fixed_body();
    test_stride_star_three_char();
    test_stride_plus();
    test_stride_concat_stars();
    test_stride_union_no_common_period();
    test_stride_union_same_period();
    test_stride_loop();
    test_stride_full_seq();
    test_stride_empty_regex();
    test_stride_epsilon();
    test_stride_opt();

    // generate_parikh_constraints tests
    test_generate_constraints_ab_star();
    test_generate_constraints_bounded_loop();
    test_generate_constraints_stride_one();
    test_generate_constraints_fixed_length();
    test_generate_constraints_dep_propagated();

    // apply_to_node tests
    test_apply_to_node_adds_constraints();
    test_apply_to_node_stride_one_no_constraints();

    // check_parikh_conflict tests
    test_check_conflict_unconstrained_no_conflict();
    test_check_conflict_valid_k_exists();
    test_check_conflict_no_valid_k();
    test_check_conflict_abc_star();
    test_check_conflict_stride_one_never_conflicts();

    // minterm_to_char_set tests
    test_minterm_full_char();
    test_minterm_empty_regex();
    test_minterm_range();
    test_minterm_complement();
    test_minterm_intersection();
    test_minterm_diff();
    test_minterm_singleton();
    test_minterm_nullptr_is_full();
}

