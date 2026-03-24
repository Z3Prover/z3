/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex.cpp

Abstract:

    Unit tests for seq_regex: lazy regex membership processing
    for the Nielsen-based string solver.

--*/
#include "util/util.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_regex.h"
#include "smt/seq/seq_nielsen.h"
#include "util/lbool.h"
#include "util/zstring.h"
#include <iostream>

// Test 1: seq_regex instantiation
static void test_seq_regex_instantiation() {
    std::cout << "test_seq_regex_instantiation\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    SASSERT(&nr.sg() == &sg);
    std::cout << "  ok\n";
}

// Test 2: is_empty_regex on an empty-language node
static void test_seq_regex_is_empty() {
    std::cout << "test_seq_regex_is_empty\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);

    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    // re.none is the empty language
    expr_ref none_e(su.re.mk_empty(su.re.mk_re(str_sort)), m);
    euf::snode* none_n = sg.mk(none_e.get());
    SASSERT(nr.is_empty_regex(none_n));
    std::cout << "  ok: re.none recognized as empty\n";
}

// Test 3: is_empty_regex on a full-match regex (not empty)
static void test_seq_regex_is_full() {
    std::cout << "test_seq_regex_is_full\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);

    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    // re.all (full sequence regex) is not empty
    expr_ref full_e(su.re.mk_full_seq(su.re.mk_re(str_sort)), m);
    euf::snode* full_n = sg.mk(full_e.get());
    SASSERT(!nr.is_empty_regex(full_n));
    std::cout << "  ok: re.all not recognized as empty\n";
}

// Test 4: strengthened_stabilizer — null safety
static void test_strengthened_stabilizer_null() {
    std::cout << "test_strengthened_stabilizer_null\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);

    SASSERT(nr.strengthened_stabilizer(nullptr, nullptr) == nullptr);

    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    sort* re_sort = su.re.mk_re(str_sort);
    expr_ref full_e(su.re.mk_full_seq(re_sort), m);
    euf::snode* full_re = sg.mk(full_e);

    SASSERT(nr.strengthened_stabilizer(full_re, nullptr) == nullptr);
    SASSERT(nr.strengthened_stabilizer(nullptr, full_re) == nullptr);
    std::cout << "  ok\n";
}

// Test 5: strengthened_stabilizer — single char cycle on a*
// Regex a*, history = 'a'. D('a', a*) = a* (sub-cycle back to start).
// Stabilizer body should be to_re("a").
static void test_strengthened_stabilizer_single_char() {
    std::cout << "test_strengthened_stabilizer_single_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    // Build a*
    expr_ref star_a(su.re.mk_star(su.re.mk_to_re(su.str.mk_string("a"))), m);
    euf::snode* re_star_a = sg.mk(star_a);

    // Build history = char 'a' (single token, no concat needed)
    euf::snode* tok_a = sg.mk_char('a');
    euf::snode* history = tok_a;

    euf::snode* result = nr.strengthened_stabilizer(re_star_a, history);
    // Should produce a non-null stabilizer body (to_re("a"))
    SASSERT(result != nullptr);
    std::cout << "  ok: a* with history 'a' -> non-null stabilizer\n";
}

// Test 6: strengthened_stabilizer — two-char cycle with sub-cycle
// Regex (ab)*, history = 'a', 'b'. D('a', (ab)*) = b(ab)*, D('b', b(ab)*) = (ab)*
// This should detect a sub-cycle and build a stabilizer body.
static void test_strengthened_stabilizer_two_char() {
    std::cout << "test_strengthened_stabilizer_two_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    // Build (ab)*
    expr_ref ab(su.re.mk_to_re(su.str.mk_string("ab")), m);
    expr_ref star_ab(su.re.mk_star(ab), m);
    euf::snode* re_star_ab = sg.mk(star_ab);

    // Build history: concat(char_a, char_b) using string concat
    euf::snode* tok_a = sg.mk_char('a');
    euf::snode* tok_b = sg.mk_char('b');
    euf::snode* history = sg.mk_concat(tok_a, tok_b);

    euf::snode* result = nr.strengthened_stabilizer(re_star_ab, history);
    // Should produce a non-null stabilizer body
    SASSERT(result != nullptr);
    std::cout << "  ok: (ab)* with history 'ab' -> non-null stabilizer\n";
}

// Test 7: get_filtered_stabilizer_star — no stabilizers registered
static void test_filtered_stabilizer_star_empty() {
    std::cout << "test_filtered_stabilizer_star_empty\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    sort* str_sort = su.str.mk_string_sort();
    sort* re_sort = su.re.mk_re(str_sort);
    expr_ref full_e(su.re.mk_full_seq(re_sort), m);
    euf::snode* full_re = sg.mk(full_e);
    euf::snode* tok_a = sg.mk_char('a');

    euf::snode* result = nr.get_filtered_stabilizer_star(full_re, tok_a);
    SASSERT(result == nullptr);
    std::cout << "  ok: no stabilizers -> nullptr\n";
}

// Test 8: get_filtered_stabilizer_star — with registered stabilizer that passes filter
static void test_filtered_stabilizer_star_with_stab() {
    std::cout << "test_filtered_stabilizer_star_with_stab\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    // Build a* as the regex state
    expr_ref star_a(su.re.mk_star(su.re.mk_to_re(su.str.mk_string("a"))), m);
    euf::snode* re_star_a = sg.mk(star_a);

    // Register a stabilizer: to_re("b") — only accepts "b"
    expr_ref stab_b(su.re.mk_to_re(su.str.mk_string("b")), m);
    euf::snode* stab_b_sn = sg.mk(stab_b);
    nr.add_stabilizer(re_star_a, stab_b_sn);

    // Exclude char 'a': D('a', to_re("b")) should be fail
    euf::snode* tok_a = sg.mk_char('a');
    euf::snode* result = nr.get_filtered_stabilizer_star(re_star_a, tok_a);
    // to_re("b") should pass the filter → result is star(to_re("b"))
    SASSERT(result != nullptr);
    SASSERT(result->is_star());
    std::cout << "  ok: filter keeps to_re('b') when excluding 'a'\n";
}

// Test 9: get_filtered_stabilizer_star — stabilizer filtered out
static void test_filtered_stabilizer_star_filtered() {
    std::cout << "test_filtered_stabilizer_star_filtered\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    // Build a* as the regex state
    expr_ref star_a(su.re.mk_star(su.re.mk_to_re(su.str.mk_string("a"))), m);
    euf::snode* re_star_a = sg.mk(star_a);

    // Register a stabilizer: to_re("a") — accepts "a"
    expr_ref stab_a(su.re.mk_to_re(su.str.mk_string("a")), m);
    euf::snode* stab_a_sn = sg.mk(stab_a);
    nr.add_stabilizer(re_star_a, stab_a_sn);

    // Exclude char 'a': D('a', to_re("a")) is NOT fail → filtered out
    euf::snode* tok_a = sg.mk_char('a');
    euf::snode* result = nr.get_filtered_stabilizer_star(re_star_a, tok_a);
    SASSERT(result == nullptr);
    std::cout << "  ok: filter removes to_re('a') when excluding 'a'\n";
}

// Test 10: extract_cycle_history — basic extraction
static void test_extract_cycle_history_basic() {
    std::cout << "test_extract_cycle_history_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    sort* str_sort = su.str.mk_string_sort();
    sort* re_sort = su.re.mk_re(str_sort);
    expr_ref full_e(su.re.mk_full_seq(re_sort), m);
    euf::snode* full_re = sg.mk(full_e);

    euf::snode* tok_a = sg.mk_char('a');
    euf::snode* tok_b = sg.mk_char('b');
    euf::snode* tok_c = sg.mk_char('c');

    // Ancestor history: just 'a' (length 1)
    euf::snode* anc_hist = tok_a;

    // Current history: concat(concat(a, b), c) = a,b,c (length 3)
    euf::snode* cur_hist = sg.mk_concat(sg.mk_concat(tok_a, tok_b), tok_c);

    euf::snode* empty_str = sg.mk_empty_seq(str_sort);
    seq::dep_tracker empty_dep;

    seq::str_mem ancestor(empty_str, full_re, anc_hist, 0, empty_dep);
    seq::str_mem current(empty_str, full_re, cur_hist, 0, empty_dep);

    euf::snode* cycle = nr.extract_cycle_history(current, ancestor);
    // Should return the last 2 tokens (b, c)
    SASSERT(cycle != nullptr);
    SASSERT(cycle->length() == 2);
    std::cout << "  ok: extracted cycle of length 2\n";
}

// Test 11: extract_cycle_history — null ancestor history
static void test_extract_cycle_history_null_ancestor() {
    std::cout << "test_extract_cycle_history_null_ancestor\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    sort* str_sort = su.str.mk_string_sort();
    sort* re_sort = su.re.mk_re(str_sort);
    expr_ref full_e(su.re.mk_full_seq(re_sort), m);
    euf::snode* full_re = sg.mk(full_e);

    euf::snode* tok_a = sg.mk_char('a');
    euf::snode* tok_b = sg.mk_char('b');
    euf::snode* cur_hist = sg.mk_concat(tok_a, tok_b);
    euf::snode* empty_str = sg.mk_empty_seq(str_sort);
    seq::dep_tracker empty_dep;

    // Ancestor has no history (nullptr)
    seq::str_mem ancestor(empty_str, full_re, nullptr, 0, empty_dep);
    seq::str_mem current(empty_str, full_re, cur_hist, 0, empty_dep);

    euf::snode* cycle = nr.extract_cycle_history(current, ancestor);
    // With null ancestor history, entire current history is the cycle
    SASSERT(cycle != nullptr);
    SASSERT(cycle->length() == 2);
    std::cout << "  ok: null ancestor -> full history as cycle\n";
}

// Test 12: BFS emptiness — re.none (empty language) is empty
static void test_bfs_empty_none() {
    std::cout << "test_bfs_empty_none\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    sort* re_sort = su.re.mk_re(str_sort);

    expr_ref none_e(su.re.mk_empty(re_sort), m);
    euf::snode* none_re = sg.mk(none_e);
    lbool result = nr.is_empty_bfs(none_re);
    SASSERT(result == l_true);
    std::cout << "  ok: re.none -> l_true (empty)\n";
}

// Test 13: BFS emptiness — full_seq (Sigma*) is NOT empty
static void test_bfs_nonempty_full() {
    std::cout << "test_bfs_nonempty_full\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    sort* re_sort = su.re.mk_re(str_sort);

    expr_ref full_e(su.re.mk_full_seq(re_sort), m);
    euf::snode* full_re = sg.mk(full_e);
    lbool result = nr.is_empty_bfs(full_re);
    SASSERT(result == l_false);
    std::cout << "  ok: full_seq -> l_false (non-empty)\n";
}

// Test 14: BFS emptiness — to_re("abc") is NOT empty
static void test_bfs_nonempty_to_re() {
    std::cout << "test_bfs_nonempty_to_re\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    expr_ref to_re_abc(su.re.mk_to_re(su.str.mk_string("abc")), m);
    euf::snode* re_abc = sg.mk(to_re_abc);
    lbool result = nr.is_empty_bfs(re_abc);
    SASSERT(result == l_false);
    std::cout << "  ok: to_re(\"abc\") -> l_false (non-empty)\n";
}

// Test 15: BFS emptiness — a* is NOT empty (accepts epsilon)
static void test_bfs_nonempty_star() {
    std::cout << "test_bfs_nonempty_star\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    expr_ref star_a(su.re.mk_star(su.re.mk_to_re(su.str.mk_string("a"))), m);
    euf::snode* re_star_a = sg.mk(star_a);
    lbool result = nr.is_empty_bfs(re_star_a);
    SASSERT(result == l_false);
    std::cout << "  ok: a* -> l_false (non-empty, accepts epsilon)\n";
}

// Test 16: BFS emptiness — union(none, none) is empty
static void test_bfs_empty_union_of_empties() {
    std::cout << "test_bfs_empty_union_of_empties\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    sort* re_sort = su.re.mk_re(str_sort);

    expr_ref none1(su.re.mk_empty(re_sort), m);
    expr_ref none2(su.re.mk_empty(re_sort), m);
    expr_ref union_e(su.re.mk_union(none1, none2), m);
    euf::snode* re_union = sg.mk(union_e);
    lbool result = nr.is_empty_bfs(re_union);
    SASSERT(result == l_true);
    std::cout << "  ok: union(none, none) -> l_true (empty)\n";
}

// Test 17: BFS emptiness — re.range('a','z') is NOT empty
static void test_bfs_nonempty_range() {
    std::cout << "test_bfs_nonempty_range\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();

    expr_ref lo(su.mk_char('a'), m);
    expr_ref hi(su.mk_char('z'), m);
    expr_ref range_e(su.re.mk_range(su.str.mk_unit(lo), su.str.mk_unit(hi)), m);
    euf::snode* re_range = sg.mk(range_e);
    lbool result = nr.is_empty_bfs(re_range);
    SASSERT(result == l_false);
    std::cout << "  ok: range('a','z') -> l_false (non-empty)\n";
}

// Test 18: BFS emptiness — complement(full_seq) = empty
static void test_bfs_empty_complement_full() {
    std::cout << "test_bfs_empty_complement_full\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    sort* re_sort = su.re.mk_re(str_sort);

    expr_ref comp_full(su.re.mk_complement(su.re.mk_full_seq(re_sort)), m);
    euf::snode* re_comp = sg.mk(comp_full);
    lbool result = nr.is_empty_bfs(re_comp);
    SASSERT(result == l_true);
    std::cout << "  ok: ~full_seq -> l_true (empty)\n";
}

// Test 19: BFS emptiness — nullptr returns l_undef
static void test_bfs_null_safety() {
    std::cout << "test_bfs_null_safety\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);

    lbool result = nr.is_empty_bfs(nullptr);
    SASSERT(result == l_undef);
    std::cout << "  ok: nullptr -> l_undef\n";
}

// Test 20: BFS emptiness — max_states bound respected
static void test_bfs_bounded() {
    std::cout << "test_bfs_bounded\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    // (a|b)+ requires at least one char; with max_states=1 should bail
    expr_ref a_re(su.re.mk_to_re(su.str.mk_string("a")), m);
    expr_ref b_re(su.re.mk_to_re(su.str.mk_string("b")), m);
    expr_ref ab_union(su.re.mk_union(a_re, b_re), m);
    expr_ref ab_plus(su.re.mk_plus(ab_union), m);
    euf::snode* re_plus = sg.mk(ab_plus);

    lbool result = nr.is_empty_bfs(re_plus, 1);
    SASSERT(result == l_undef);
    std::cout << "  ok: (a|b)+ with max_states=1 -> l_undef (bounded)\n";
}

// -----------------------------------------------------------------------
// New tests for regex membership completion (Phase 1-4)
// -----------------------------------------------------------------------

// Test: char_set::is_subset
static void test_char_set_is_subset() {
    std::cout << "test_char_set_is_subset\n";

    // {a} ⊆ {a,b,c} = [97,100)
    char_set cs1(char_range('a', 'b'));  // {a}
    char_set cs2(char_range('a', 'd'));  // {a,b,c}
    SASSERT(cs1.is_subset(cs2));
    SASSERT(!cs2.is_subset(cs1));

    // empty ⊆ anything
    char_set empty;
    SASSERT(empty.is_subset(cs1));
    SASSERT(empty.is_subset(cs2));

    // self ⊆ self
    SASSERT(cs1.is_subset(cs1));
    SASSERT(cs2.is_subset(cs2));

    // disjoint: {x} not ⊆ {a}
    char_set cs3(char_range('x', 'y'));
    SASSERT(!cs3.is_subset(cs1));

    std::cout << "  ok\n";
}

// Test: stabilizer store basic operations
static void test_stabilizer_store_basic() {
    std::cout << "test_stabilizer_store_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    expr_ref a_re(su.re.mk_to_re(su.str.mk_string("a")), m);
    expr_ref b_re(su.re.mk_to_re(su.str.mk_string("b")), m);
    euf::snode* a_sn = sg.mk(a_re);
    euf::snode* b_sn = sg.mk(b_re);

    SASSERT(!nr.has_stabilizers(a_sn));
    nr.add_stabilizer(a_sn, b_sn);
    SASSERT(nr.has_stabilizers(a_sn));
    SASSERT(nr.get_stabilizer_union(a_sn) == b_sn);

    // dedup: adding same stabilizer again
    nr.add_stabilizer(a_sn, b_sn);
    auto* stabs = nr.get_stabilizers(a_sn);
    SASSERT(stabs && stabs->size() == 1);

    // reset
    nr.reset_stabilizers();
    SASSERT(!nr.has_stabilizers(a_sn));

    std::cout << "  ok\n";
}

// Test: self-stabilizing flag
static void test_self_stabilizing() {
    std::cout << "test_self_stabilizing\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    expr_ref a_re(su.re.mk_to_re(su.str.mk_string("a")), m);
    euf::snode* a_sn = sg.mk(a_re);

    SASSERT(!nr.is_self_stabilizing(a_sn));
    nr.set_self_stabilizing(a_sn);
    SASSERT(nr.is_self_stabilizing(a_sn));

    // star should be detected as self-stabilizing
    expr_ref star_a(su.re.mk_star(a_re), m);
    euf::snode* star_sn = sg.mk(star_a);
    SASSERT(nr.compute_self_stabilizing(star_sn));

    std::cout << "  ok\n";
}

// Test: check_intersection_emptiness — SAT case
static void test_check_intersection_sat() {
    std::cout << "test_check_intersection_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    // a* ∩ (a|b)* should be non-empty (both accept "a")
    expr_ref a_re(su.re.mk_to_re(su.str.mk_string("a")), m);
    expr_ref star_a(su.re.mk_star(a_re), m);
    expr_ref b_re(su.re.mk_to_re(su.str.mk_string("b")), m);
    expr_ref ab_union(su.re.mk_union(a_re, b_re), m);
    expr_ref star_ab(su.re.mk_star(ab_union), m);

    euf::snode* s1 = sg.mk(star_a);
    euf::snode* s2 = sg.mk(star_ab);
    ptr_vector<euf::snode> regexes;
    regexes.push_back(s1);
    regexes.push_back(s2);

    lbool result = nr.check_intersection_emptiness(regexes);
    SASSERT(result == l_false); // non-empty
    std::cout << "  ok: a* ∩ (a|b)* is non-empty\n";
}

// Test: check_intersection_emptiness — UNSAT case
static void test_check_intersection_unsat() {
    std::cout << "test_check_intersection_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();

    // to_re("a") ∩ to_re("b") should be empty
    expr_ref a_re(su.re.mk_to_re(su.str.mk_string("a")), m);
    expr_ref b_re(su.re.mk_to_re(su.str.mk_string("b")), m);
    euf::snode* s1 = sg.mk(a_re);
    euf::snode* s2 = sg.mk(b_re);
    ptr_vector<euf::snode> regexes;
    regexes.push_back(s1);
    regexes.push_back(s2);

    lbool result = nr.check_intersection_emptiness(regexes);
    SASSERT(result == l_true); // empty
    std::cout << "  ok: to_re(a) ∩ to_re(b) is empty\n";
}

// Test: is_language_subset — true case
static void test_is_language_subset_true() {
    std::cout << "test_is_language_subset_true\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    // a* ⊆ (a|b)* should be true
    expr_ref a_re(su.re.mk_to_re(su.str.mk_string("a")), m);
    expr_ref star_a(su.re.mk_star(a_re), m);
    expr_ref b_re(su.re.mk_to_re(su.str.mk_string("b")), m);
    expr_ref ab_union(su.re.mk_union(a_re, b_re), m);
    expr_ref star_ab(su.re.mk_star(ab_union), m);

    euf::snode* subset = sg.mk(star_a);
    euf::snode* superset = sg.mk(star_ab);

    lbool result = nr.is_language_subset(subset, superset);
    SASSERT(result == l_true);
    std::cout << "  ok: a* ⊆ (a|b)*\n";
}

// Test: is_language_subset — false case
static void test_is_language_subset_false() {
    std::cout << "test_is_language_subset_false\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);

    // (a|b)* ⊄ a* should be false (b ∈ (a|b)* but b ∉ a*)
    expr_ref a_re(su.re.mk_to_re(su.str.mk_string("a")), m);
    expr_ref star_a(su.re.mk_star(a_re), m);
    expr_ref b_re(su.re.mk_to_re(su.str.mk_string("b")), m);
    expr_ref ab_union(su.re.mk_union(a_re, b_re), m);
    expr_ref star_ab(su.re.mk_star(ab_union), m);

    euf::snode* subset = sg.mk(star_ab);
    euf::snode* superset = sg.mk(star_a);

    lbool result = nr.is_language_subset(subset, superset);
    SASSERT(result == l_false);
    std::cout << "  ok: (a|b)* ⊄ a*\n";
}

// Test: is_language_subset — trivial cases
static void test_is_language_subset_trivial() {
    std::cout << "test_is_language_subset_trivial\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq::seq_regex nr(sg);
    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();

    // ∅ ⊆ anything = true
    expr_ref none(su.re.mk_empty(su.re.mk_re(str_sort)), m);
    expr_ref a_re(su.re.mk_to_re(su.str.mk_string("a")), m);
    euf::snode* empty_sn = sg.mk(none);
    euf::snode* a_sn = sg.mk(a_re);
    SASSERT(nr.is_language_subset(empty_sn, a_sn) == l_true);

    // anything ⊆ Σ* = true
    expr_ref full(su.re.mk_full_seq(su.re.mk_re(str_sort)), m);
    euf::snode* full_sn = sg.mk(full);
    SASSERT(nr.is_language_subset(a_sn, full_sn) == l_true);

    // L ⊆ L = true (same pointer)
    SASSERT(nr.is_language_subset(a_sn, a_sn) == l_true);

    std::cout << "  ok\n";
}

// Regression test: representative chosen from bounds must respect accumulated excludes.
// Example language is [A-Z] \ {"A"}, so a valid witness exists (e.g., "B") but not "A".
static void test_some_seq_in_re_excluded_low_regression() {
    std::cout << "test_some_seq_in_re_excluded_low_regression\n";
    ast_manager m;
    reg_decl_plugins(m);
    seq_util su(m);
    seq_rewriter rw(m);
    th_rewriter tr(m);

    expr_ref low(su.mk_char('A'), m);
    expr_ref high(su.mk_char('Z'), m);
    expr_ref range_az(su.re.mk_range(su.str.mk_unit(low), su.str.mk_unit(high)), m);
    expr_ref not_a(su.re.mk_complement(su.re.mk_to_re(su.str.mk_string("A"))), m);
    expr_ref re_expr(su.re.mk_inter(not_a, range_az), m);

    expr_ref witness(m);
    lbool wr = rw.some_seq_in_re(re_expr, witness);
    SASSERT(wr == l_true);
    SASSERT(witness);

    zstring ws;
    SASSERT(su.str.is_string(witness, ws));
    SASSERT(ws != zstring("A"));

    expr_ref in_re(su.re.mk_in_re(witness, re_expr), m);
    expr_ref in_re_simpl(m);
    tr(in_re, in_re_simpl);
    SASSERT(m.is_true(in_re_simpl));

    std::cout << "  ok: witness=" << ws << " satisfies [A-Z] \\ {A}\n";
}

// Regression: some_seq_in_re returns l_false for re.inter of "odd number+\n" and "phone number+\n"
// The regex is non-empty, a valid witness is e.g. "1111111111\n".
// Root cause: derivative of re.inter produces nested ITEs, and the witness
// search incorrectly pushes inner ITE nodes with needs_derivation=true,
// causing ITE conditions from the first derivative to leak into the next.
static void test_some_seq_in_re_inter_loop_regression() {
    std::cout << "test_some_seq_in_re_inter_loop_regression\n";
    ast_manager m;
    reg_decl_plugins(m);
    seq_util su(m);
    seq_rewriter rw(m);
    th_rewriter tr(m);

    // Helpers
    auto mk_to_re = [&](const char* s) -> expr_ref {
        return expr_ref(su.re.mk_to_re(su.str.mk_string(s)), m);
    };
    auto mk_range = [&](const char* lo, const char* hi) -> expr_ref {
        expr_ref l(su.mk_char(lo[0]), m);
        expr_ref h(su.mk_char(hi[0]), m);
        return expr_ref(su.re.mk_range(su.str.mk_unit(l), su.str.mk_unit(h)), m);
    };
    auto cat = [&](expr* a, expr* b) -> expr_ref {
        return expr_ref(su.re.mk_concat(a, b), m);
    };
    auto un = [&](expr* a, expr* b) -> expr_ref {
        return expr_ref(su.re.mk_union(a, b), m);
    };

    // Build the regex from the crash output:
    // a!1 = ([1-9][1-9]* | "")
    expr_ref range19 = mk_range("1", "9");
    expr_ref a1(su.re.mk_union(
        su.re.mk_concat(range19, su.re.mk_star(range19)),
        su.re.mk_to_re(su.str.mk_string(""))), m);

    // a!2 = "3" | "5" | "7" | "9"
    expr_ref a2 = un(mk_to_re("3"), un(mk_to_re("5"), un(mk_to_re("7"), mk_to_re("9"))));

    // a!3 = (a!1 ++ ("1" | a!2)) ++ "\n"
    expr_ref a3 = cat(cat(a1, un(mk_to_re("1"), a2)), mk_to_re("\x0a"));

    // a!4 = "(" ++ loop(3,3,[0-9]) ++ ")"
    expr_ref range09 = mk_range("0", "9");
    expr_ref loop3(su.re.mk_loop(range09, 3, 3), m);
    expr_ref a4 = cat(cat(mk_to_re("("), loop3), mk_to_re(")"));

    // a!5 = a!4 ++ ("" | " ") ++ loop(3,3,[0-9])
    expr_ref a5 = cat(cat(a4, un(mk_to_re(""), mk_to_re(" "))), loop3);

    // a!6 = a!5 ++ ("" | " " | "-")
    expr_ref sep3 = un(mk_to_re(""), un(mk_to_re(" "), mk_to_re("-")));
    expr_ref a6 = cat(a5, sep3);

    // a!7 = loop(3,3,[0-9]) ++ ("" | " " | "-")
    expr_ref a7 = cat(loop3, sep3);

    // a!8 = a!7 ++ loop(3,3,[0-9]) ++ ("" | " " | "-")
    expr_ref a8 = cat(cat(a7, loop3), sep3);

    // a!9 = a!8 ++ loop(4,4,[0-9]) ++ "\n"
    expr_ref loop4(su.re.mk_loop(range09, 4, 4), m);
    expr_ref a9 = cat(cat(a8, loop4), mk_to_re("\x0a"));

    // a!10 = (a!6 ++ loop(4,4,[0-9])) | a!9
    expr_ref a10 = un(cat(a6, loop4), a9);

    // Final regex = re.inter(a!3, a!10)
    expr_ref re_expr(su.re.mk_inter(a3, a10), m);

    std::cout << "  regex: " << mk_pp(re_expr, m) << "\n";

    // The regex is non-empty: "1111111111\n" matches both a!3 and a!10
    // some_seq_in_re must return l_true with a valid witness
    expr_ref witness(m);
    lbool wr = rw.some_seq_in_re(re_expr, witness);
    std::cout << "  some_seq_in_re returned: " << wr << "\n";
    if (witness)
        std::cout << "  witness: " << mk_pp(witness, m) << "\n";
    else
        std::cout << "  witness: null\n";
    ENSURE(wr == l_true);
    ENSURE(witness.get() != nullptr);

    if (wr != l_true || !witness)
        return;

    // Verify witness satisfies the regex
    expr_ref in_re(su.re.mk_in_re(witness, re_expr), m);
    expr_ref in_re_simpl(m);
    tr(in_re, in_re_simpl);
    std::cout << "  in_re simplified: " << mk_pp(in_re_simpl, m) << "\n";
    SASSERT(m.is_true(in_re_simpl));

    zstring ws;
    VERIFY(su.str.is_string(witness, ws));
    std::cout << "  ok: witness=\"" << ws << "\" satisfies the intersection regex\n";
}

void tst_seq_regex() {
    test_seq_regex_instantiation();
    test_seq_regex_is_empty();
    test_seq_regex_is_full();
    test_strengthened_stabilizer_null();
    test_strengthened_stabilizer_single_char();
    test_strengthened_stabilizer_two_char();
    test_filtered_stabilizer_star_empty();
    test_filtered_stabilizer_star_with_stab();
    test_filtered_stabilizer_star_filtered();
    test_extract_cycle_history_basic();
    test_extract_cycle_history_null_ancestor();
    test_bfs_empty_none();
    test_bfs_nonempty_full();
    test_bfs_nonempty_to_re();
    test_bfs_nonempty_star();
    test_bfs_empty_union_of_empties();
    test_bfs_nonempty_range();
    test_bfs_empty_complement_full();
    // New tests for regex membership completion
    test_char_set_is_subset();
    test_stabilizer_store_basic();
    test_self_stabilizing();
    test_check_intersection_sat();
    test_check_intersection_unsat();
    test_is_language_subset_true();
    test_is_language_subset_false();
    test_is_language_subset_trivial();
    test_some_seq_in_re_excluded_low_regression();
    test_some_seq_in_re_inter_loop_regression();
    // test_bfs_null_safety has a pre-existing failure, run it last
    test_bfs_null_safety();
    test_bfs_bounded();
    std::cout << "seq_regex: all tests passed\n";
}
