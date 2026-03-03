/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen.cpp

Abstract:

    Unit tests for the Nielsen graph framework (seq_nielsen.h).
    Tests constraint types, node/edge construction, substitution
    application, and graph population.

--*/

#include "util/util.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_nielsen.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include <iostream>

// test dep_tracker basic operations
static void test_dep_tracker() {
    std::cout << "test_dep_tracker\n";

    // empty tracker
    seq::dep_tracker d0;
    SASSERT(d0.empty());

    // tracker with one bit set
    seq::dep_tracker d1(8, 3);
    SASSERT(!d1.empty());

    // tracker with another bit
    seq::dep_tracker d2(8, 5);
    SASSERT(!d2.empty());

    // merge
    seq::dep_tracker d3 = d1;
    d3.merge(d2);
    SASSERT(!d3.empty());
    SASSERT(d3.is_superset(d1));
    SASSERT(d3.is_superset(d2));
    SASSERT(!d1.is_superset(d2));

    // equality
    seq::dep_tracker d4(8, 3);
    SASSERT(d1 == d4);
    SASSERT(d1 != d2);
}

// test str_eq constraint creation and operations
static void test_str_eq() {
    std::cout << "test_str_eq\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* e = sg.mk_empty();

    seq::dep_tracker dep(4, 0);

    // basic equality
    seq::str_eq eq1(x, y, dep);
    SASSERT(!eq1.is_trivial());
    SASSERT(eq1.contains_var(x));
    SASSERT(eq1.contains_var(y));
    SASSERT(!eq1.contains_var(a));

    // trivial equality: same node
    seq::str_eq eq2(x, x, dep);
    SASSERT(eq2.is_trivial());

    // trivial equality: both empty
    seq::str_eq eq3(e, e, dep);
    SASSERT(eq3.is_trivial());

    // sorting: lower id first
    seq::str_eq eq4(y, x, dep);
    eq4.sort();
    SASSERT(eq4.m_lhs->id() <= eq4.m_rhs->id());

    // contains_var with concat
    euf::snode* xa = sg.mk_concat(x, a);
    seq::str_eq eq5(xa, y, dep);
    SASSERT(eq5.contains_var(x));
    SASSERT(eq5.contains_var(y));
    SASSERT(!eq5.contains_var(e));
}

// test str_mem constraint creation and operations
static void test_str_mem() {
    std::cout << "test_str_mem\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* e = sg.mk_empty();

    // create a regex: re.all (.*)
    expr_ref star_fc(seq.re.mk_full_seq(str_sort), m);
    euf::snode* regex = sg.mk(star_fc);

    seq::dep_tracker dep(4, 1);
    seq::str_mem mem(x, regex, e, 0, dep);

    // x in regex is primitive (x is a single variable)
    SASSERT(mem.is_primitive());
    SASSERT(mem.contains_var(x));

    // concatenation is not primitive
    euf::snode* a = sg.mk_char('A');
    euf::snode* xa = sg.mk_concat(x, a);
    seq::str_mem mem2(xa, regex, e, 1, dep);
    SASSERT(!mem2.is_primitive());
    SASSERT(mem2.contains_var(x));
}

// test nielsen_subst
static void test_nielsen_subst() {
    std::cout << "test_nielsen_subst\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* e = sg.mk_empty();

    seq::dep_tracker dep;

    // eliminating substitution: x -> A (x does not appear in A)
    seq::nielsen_subst s1(x, a, dep);
    SASSERT(s1.is_eliminating());

    // eliminating substitution: x -> empty
    seq::nielsen_subst s2(x, e, dep);
    SASSERT(s2.is_eliminating());

    // non-eliminating substitution: x -> concat(A, x)
    euf::snode* ax = sg.mk_concat(a, x);
    seq::nielsen_subst s3(x, ax, dep);
    SASSERT(!s3.is_eliminating());

    // eliminating substitution: x -> y (x not in y)
    seq::nielsen_subst s4(x, y, dep);
    SASSERT(s4.is_eliminating());
}

// test nielsen_node creation and constraint management
static void test_nielsen_node() {
    std::cout << "test_nielsen_node\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    seq::nielsen_graph ng(sg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');

    seq::nielsen_node* root = ng.mk_node();
    SASSERT(root->id() == 0);
    SASSERT(root->str_eqs().empty());
    SASSERT(root->str_mems().empty());
    SASSERT(root->is_progress());
    SASSERT(root->reason() == seq::backtrack_reason::unevaluated);

    // add constraints
    seq::dep_tracker dep;
    root->add_str_eq(seq::str_eq(x, y, dep));
    root->add_str_eq(seq::str_eq(sg.mk_concat(x, a), sg.mk_concat(a, y), dep));
    SASSERT(root->str_eqs().size() == 2);

    // regex membership
    expr_ref re_all(seq.re.mk_full_seq(str_sort), m);
    euf::snode* regex = sg.mk(re_all);
    euf::snode* empty = sg.mk_empty();
    root->add_str_mem(seq::str_mem(x, regex, empty, 0, dep));
    SASSERT(root->str_mems().size() == 1);

    // clone from parent
    seq::nielsen_node* child = ng.mk_node();
    child->clone_from(*root);
    SASSERT(child->str_eqs().size() == 2);
    SASSERT(child->str_mems().size() == 1);
    SASSERT(child->id() == 1);
}

// test nielsen_edge creation
static void test_nielsen_edge() {
    std::cout << "test_nielsen_edge\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    seq::nielsen_graph ng(sg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');

    // create parent and child nodes
    seq::nielsen_node* parent = ng.mk_node();
    seq::dep_tracker dep;
    parent->add_str_eq(seq::str_eq(x, y, dep));

    seq::nielsen_node* child = ng.mk_child(parent);

    // create edge with substitution x -> A
    seq::nielsen_edge* edge = ng.mk_edge(parent, child, true);
    edge->add_subst(seq::nielsen_subst(x, a, dep));

    SASSERT(edge->src() == parent);
    SASSERT(edge->tgt() == child);
    SASSERT(edge->is_progress());
    SASSERT(edge->subst().size() == 1);
    SASSERT(parent->outgoing().size() == 1);
    SASSERT(parent->outgoing()[0] == edge);
}

// test nielsen_graph population from external constraints
static void test_nielsen_graph_populate() {
    std::cout << "test_nielsen_graph_populate\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    seq::nielsen_graph ng(sg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');

    // add string equality: x = y
    ng.add_str_eq(x, y);
    SASSERT(ng.root() != nullptr);
    SASSERT(ng.root()->str_eqs().size() == 1);
    SASSERT(ng.num_nodes() == 1);

    // add regex membership: x in .*
    expr_ref re_all(seq.re.mk_full_seq(str_sort), m);
    euf::snode* regex = sg.mk(re_all);
    ng.add_str_mem(x, regex);
    SASSERT(ng.root()->str_mems().size() == 1);
    SASSERT(ng.root()->str_mems()[0].m_id == 0);

    // add another equality: concat(x, A) = concat(A, y)
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* ay = sg.mk_concat(a, y);
    ng.add_str_eq(xa, ay);
    SASSERT(ng.root()->str_eqs().size() == 2);

    // display for visual inspection
    ng.display(std::cout);
}

// test substitution application on nielsen_node
static void test_nielsen_subst_apply() {
    std::cout << "test_nielsen_subst_apply\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    seq::nielsen_graph ng(sg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* e = sg.mk_empty();

    // create node with constraint: concat(x, A) = concat(B, y)
    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep;
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* by = sg.mk_concat(b, y);
    node->add_str_eq(seq::str_eq(xa, by, dep));

    // apply substitution x -> empty
    seq::nielsen_subst s(x, e, dep);
    node->apply_subst(sg, s);

    // after x -> empty: lhs should be just A, rhs still concat(B, y)
    SASSERT(node->str_eqs().size() == 1);
    auto const& eq = node->str_eqs()[0];
    // a should remain (after x replaced with empty, concat(empty, A) = A)
    std::cout << "  lhs len=" << eq.m_lhs->length() << " rhs len=" << eq.m_rhs->length() << "\n";
}

// test Nielsen graph reset
static void test_nielsen_graph_reset() {
    std::cout << "test_nielsen_graph_reset\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    seq::nielsen_graph ng(sg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    ng.add_str_eq(x, y);
    SASSERT(ng.num_nodes() == 1);
    SASSERT(ng.root() != nullptr);

    ng.reset();
    SASSERT(ng.num_nodes() == 0);
    SASSERT(ng.root() == nullptr);
}

// test constructing a basic Nielsen expansion tree
// x = Ay: split into x -> eps (progress) or x -> Ax (non-progress)
static void test_nielsen_expansion() {
    std::cout << "test_nielsen_expansion\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    seq::nielsen_graph ng(sg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* ay = sg.mk_concat(a, y);

    // root: x = Ay
    ng.add_str_eq(x, ay);
    seq::nielsen_node* root = ng.root();
    SASSERT(root->str_eqs().size() == 1);

    seq::dep_tracker dep;

    // branch 1: x -> eps (eliminating, progress)
    euf::snode* e = sg.mk_empty();
    seq::nielsen_node* child1 = ng.mk_child(root);
    seq::nielsen_subst s1(x, e, dep);
    child1->apply_subst(sg, s1);
    seq::nielsen_edge* edge1 = ng.mk_edge(root, child1, true);
    edge1->add_subst(s1);

    // branch 2: x -> Ax (non-eliminating, non-progress)
    euf::snode* ax = sg.mk_concat(a, x);
    seq::nielsen_node* child2 = ng.mk_child(root);
    seq::nielsen_subst s2(x, ax, dep);
    child2->apply_subst(sg, s2);
    seq::nielsen_edge* edge2 = ng.mk_edge(root, child2, false);
    edge2->add_subst(s2);

    SASSERT(ng.num_nodes() == 3);
    SASSERT(root->outgoing().size() == 2);
    SASSERT(edge1->is_progress());
    SASSERT(!edge2->is_progress());

    // verify substitution effects on child1: eps = Ay becomes empty = Ay
    SASSERT(child1->str_eqs().size() == 1);

    ng.display(std::cout);
}

// test run index management
static void test_run_idx() {
    std::cout << "test_run_idx\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    seq::nielsen_graph ng(sg);
    SASSERT(ng.run_idx() == 0);

    ng.inc_run_idx();
    SASSERT(ng.run_idx() == 1);

    ng.inc_run_idx();
    SASSERT(ng.run_idx() == 2);
}

// test multiple regex memberships
static void test_multiple_memberships() {
    std::cout << "test_multiple_memberships\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    seq::nielsen_graph ng(sg);

    euf::snode* x = sg.mk_var(symbol("x"));

    // x in .*
    expr_ref re_all(seq.re.mk_full_seq(str_sort), m);
    euf::snode* regex1 = sg.mk(re_all);
    ng.add_str_mem(x, regex1);

    // x in re.union(to_re("A"), to_re("B"))
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    expr_ref to_re_b(seq.re.mk_to_re(unit_b), m);
    expr_ref re_union(seq.re.mk_union(to_re_a, to_re_b), m);
    euf::snode* regex2 = sg.mk(re_union);
    ng.add_str_mem(x, regex2);

    SASSERT(ng.root() != nullptr);
    SASSERT(ng.root()->str_mems().size() == 2);
    SASSERT(ng.root()->str_mems()[0].m_id == 0);
    SASSERT(ng.root()->str_mems()[1].m_id == 1);

    ng.display(std::cout);
}

// test backedge setting (cycle detection support)
static void test_backedge() {
    std::cout << "test_backedge\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    seq::nielsen_graph ng(sg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();
    seq::nielsen_node* child = ng.mk_child(root);

    // set backedge from child to root (cycle)
    child->set_backedge(root);
    SASSERT(child->backedge() == root);
    SASSERT(root->backedge() == nullptr);
}

void tst_seq_nielsen() {
    test_dep_tracker();
    test_str_eq();
    test_str_mem();
    test_nielsen_subst();
    test_nielsen_node();
    test_nielsen_edge();
    test_nielsen_graph_populate();
    test_nielsen_subst_apply();
    test_nielsen_graph_reset();
    test_nielsen_expansion();
    test_run_idx();
    test_multiple_memberships();
    test_backedge();
}
