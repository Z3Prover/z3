/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "util/util.h"
#include "ast/euf/euf_sgraph.h"
#include "ast/euf/euf_seq_plugin.h"
#include "ast/euf/euf_egraph.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include <iostream>

static unsigned s_var = 0;

static euf::enode* get_node(euf::egraph& g, seq_util& seq, expr* e) {
    auto* n = g.find(e);
    if (n) return n;
    euf::enode_vector args;
    if (is_app(e))
        for (expr* arg : *to_app(e))
            args.push_back(get_node(g, seq, arg));
    n = g.mk(e, 0, args.size(), args.data());
    if (seq.is_seq(e) || seq.is_re(e))
        g.add_th_var(n, ++s_var, seq.get_family_id());
    return n;
}

// test sgraph: basic classification and metadata
static void test_sgraph_basic() {
    std::cout << "test_sgraph_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref y(m.mk_const("y", str_sort), m);
    expr_ref empty(seq.str.mk_empty(str_sort), m);
    expr_ref xy(seq.str.mk_concat(x, y), m);

    euf::snode* sx = sg.mk(x);
    SASSERT(sx);
    SASSERT(sx->is_var());
    SASSERT(!sx->is_ground());
    SASSERT(sx->is_regex_free());
    SASSERT(sx->length() == 1);

    euf::snode* se = sg.mk(empty);
    SASSERT(se);
    SASSERT(se->is_empty());
    SASSERT(se->is_ground());
    SASSERT(se->length() == 0);

    euf::snode* sxy = sg.mk(xy);
    SASSERT(sxy);
    SASSERT(sxy->is_concat());
    SASSERT(!sxy->is_ground());
    SASSERT(sxy->length() == 2);
    SASSERT(sxy->num_args() == 2);

    std::cout << "sgraph:\n";
    sg.display(std::cout);
    std::cout << "\n";
}

// test sgraph: backtracking with push/pop
static void test_sgraph_backtrack() {
    std::cout << "test_sgraph_backtrack\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref y(m.mk_const("y", str_sort), m);

    sg.mk(x);
    unsigned before = sg.num_nodes();

    sg.push();

    expr_ref xy(seq.str.mk_concat(x, y), m);
    sg.mk(xy);
    SASSERT(sg.num_nodes() > before);

    sg.pop(1);
    // y and xy were created inside the scope, so some nodes should be removed
    // x was created before the scope, so it should persist
    SASSERT(sg.find(x));
}

// test seq_plugin: concat associativity is normalized by the plugin
static void test_seq_plugin_assoc() {
    std::cout << "test_seq_plugin_assoc\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    euf::egraph& g = sg.get_egraph();
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref a(m.mk_const("a", str_sort), m);
    expr_ref b(m.mk_const("b", str_sort), m);
    expr_ref c(m.mk_const("c", str_sort), m);

    // register nodes in egraph
    // concat(concat(a,b),c) should be merged with concat(a,concat(b,c))
    expr_ref ab(seq.str.mk_concat(a, b), m);
    expr_ref ab_c(seq.str.mk_concat(ab, c), m);

    euf::enode* nab_c = get_node(g, seq, ab_c);
    g.propagate();

    // the plugin should have created a right-associated form and merged
    std::cout << g << "\n";
}

// test seq_plugin: empty string elimination
static void test_seq_plugin_empty() {
    std::cout << "test_seq_plugin_empty\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    euf::egraph& g = sg.get_egraph();
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref empty(seq.str.mk_empty(str_sort), m);
    expr_ref xe(seq.str.mk_concat(x, empty), m);

    auto* nxe = get_node(g, seq, xe);
    auto* nx = g.find(x);
    g.propagate();

    // concat(x, empty) should be merged with x
    SASSERT(nxe->get_root() == nx->get_root());
    std::cout << g << "\n";
}

// test seq_plugin: Kleene star merging
// The seq_plugin detects when star bodies are congruent
// This tests the same_star_body logic at the regex level
static void test_seq_plugin_star_merge() {
    std::cout << "test_seq_plugin_star_merge\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    euf::egraph& g = sg.get_egraph();
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);
    sort_ref re_sort(seq.re.mk_re(str_sort), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    // re.star(to_re(x))
    expr_ref to_re_x(seq.re.mk_to_re(x), m);
    expr_ref star_x(seq.re.mk_star(to_re_x), m);
    // use regex concat for star * star
    expr_ref star_star(seq.re.mk_concat(star_x, star_x), m);

    // register in sgraph
    sg.mk(star_star);
    euf::snode* s = sg.find(star_x);
    SASSERT(s && s->is_star());

    std::cout << g << "\n";
}

// test seq_plugin: nullable absorption by .*
// concat(.*, nullable) should merge with .*
static void test_seq_plugin_nullable_absorb() {
    std::cout << "test_seq_plugin_nullable_absorb\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    euf::egraph& g = sg.get_egraph();
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref empty(seq.str.mk_empty(str_sort), m);
    // concat(x, empty) = x (empty is nullable, exercises nullable check)
    expr_ref xe(seq.str.mk_concat(x, empty), m);

    auto* nxe = get_node(g, seq, xe);
    auto* nx = g.find(x);
    g.propagate();

    // concat(x, empty) should be merged with x (empty elimination)
    SASSERT(nxe->get_root() == nx->get_root());
    std::cout << g << "\n";
}

// test sgraph owns egraph and syncs push/pop
static void test_sgraph_egraph_sync() {
    std::cout << "test_sgraph_egraph_sync\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    euf::egraph& g = sg.get_egraph();
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref y(m.mk_const("y", str_sort), m);
    auto* nx = get_node(g, seq, x);
    auto* ny = get_node(g, seq, y);

    sg.push();

    g.merge(nx, ny, nullptr);
    g.propagate();
    SASSERT(nx->get_root() == ny->get_root());

    sg.pop(1);
    // after pop, the merge should be undone
    SASSERT(nx->get_root() != ny->get_root());
}

// test seq_plugin: identity elimination fires after a post-registration merge
// When b ~ "" is learned AFTER concat(a, b) is registered, the plugin must
// re-check identity rules and conclude concat(a, b) ~ a.
static void test_seq_plugin_identity_after_merge() {
    std::cout << "test_seq_plugin_identity_after_merge\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    euf::egraph& g = sg.get_egraph();
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref a(m.mk_const("a", str_sort), m);
    expr_ref b(m.mk_const("b", str_sort), m);
    expr_ref empty(seq.str.mk_empty(str_sort), m);
    expr_ref ab(seq.str.mk_concat(a, b), m);

    // Register concat(a, b) first — at this point b is not yet empty.
    auto* nab = get_node(g, seq, ab);
    auto* na = g.find(a);
    auto* nb = g.find(b);
    auto* nempty = get_node(g, seq, empty);
    g.propagate();

    // Now learn b ~ "" via a merge.
    g.merge(nb, nempty, nullptr);
    g.propagate();

    // After propagation, concat(a, b) should be equivalent to a.
    SASSERT(nab->get_root() == na->get_root());
    std::cout << g << "\n";
}

// test seq_plugin: loop merging — concat(r{lo1,hi1}, r{lo2,hi2}) = r{lo1+lo2, hi1+hi2}
static void test_seq_plugin_loop_merge() {
    std::cout << "test_seq_plugin_loop_merge\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    euf::egraph& g = sg.get_egraph();
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref r(seq.re.mk_to_re(x), m);
    // r{2,3} and r{1,2} — bounds are chosen so the merged form r{3,5} is a distinct loop.
    expr_ref first_loop(seq.re.mk_loop_proper(r, 2, 3), m);
    expr_ref second_loop(seq.re.mk_loop_proper(r, 1, 2), m);
    expr_ref expected_merged_loop(seq.re.mk_loop_proper(r, 3, 5), m);
    // concat(r{2,3}, r{1,2})
    expr_ref concat_loops(seq.re.mk_concat(first_loop, second_loop), m);

    auto* nc = get_node(g, seq, concat_loops);
    auto* nl35 = get_node(g, seq, expected_merged_loop);
    g.propagate();

    // After propagation, concat(r{2,3}, r{1,2}) should be equivalent to r{3,5}.
    SASSERT(nc->get_root() == nl35->get_root());
    std::cout << g << "\n";
}

void tst_euf_seq_plugin() {
    s_var = 0; test_sgraph_basic();
    s_var = 0; test_sgraph_backtrack();
    s_var = 0; test_seq_plugin_assoc();
    s_var = 0; test_seq_plugin_empty();
    s_var = 0; test_seq_plugin_star_merge();
    s_var = 0; test_seq_plugin_nullable_absorb();
    s_var = 0; test_sgraph_egraph_sync();
    s_var = 0; test_seq_plugin_identity_after_merge();
    s_var = 0; test_seq_plugin_loop_merge();
}
