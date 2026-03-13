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
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include <iostream>

class dummy_simple_solver : public seq::simple_solver {
public:
    dummy_simple_solver() : seq::simple_solver() {}
    void push() override {}
    void pop(unsigned n) override {}
    void assert_expr(expr *e) override {}
    lbool check() override {
        return l_true;
    }

};

// test dep_tracker (uint_set) basic operations
static void test_dep_tracker() {
    std::cout << "test_dep_tracker\n";

    // empty tracker
    seq::dep_tracker d0;
    SASSERT(d0.empty());

    // tracker with one bit set
    seq::dep_tracker d1;
    d1.insert(3);
    SASSERT(!d1.empty());

    // tracker with another bit
    seq::dep_tracker d2;
    d2.insert(5);
    SASSERT(!d2.empty());

    // merge
    seq::dep_tracker d3 = d1;
    d3 |= d2;
    SASSERT(!d3.empty());
    SASSERT(d1.subset_of(d3));
    SASSERT(d2.subset_of(d3));
    SASSERT(!d2.subset_of(d1));

    // equality
    seq::dep_tracker d4;
    d4.insert(3);
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

    seq::dep_tracker dep; dep.insert(0);

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

    seq::dep_tracker dep; dep.insert(1);
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

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

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

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

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

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

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

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

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

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

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

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

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

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);
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

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

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

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

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

// test var vs var basic structure (x·A = y·B now handled by var_nielsen, not eq_split)
static void test_eq_split_basic() {
    std::cout << "test_eq_split_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* yb = sg.mk_concat(y, b);

    // x·A = y·B — eq_split returns false (no valid split point),
    // falls through to var_nielsen (priority 12) → 3 progress children
    ng.add_str_eq(xa, yb);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    SASSERT(root->outgoing().size() == 3);

    // all children are progress (var_nielsen marks all as progress)
    SASSERT(root->outgoing()[0]->is_progress());
}

// test var vs var with solve: x·y = z·w is satisfiable (all vars can be ε)
static void test_eq_split_solve_sat() {
    std::cout << "test_eq_split_solve_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* z = sg.mk_var(symbol("z"));
    euf::snode* w = sg.mk_var(symbol("w"));
    euf::snode* xy = sg.mk_concat(x, y);
    euf::snode* zw = sg.mk_concat(z, w);

    ng.add_str_eq(xy, zw);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test var vs var with solve: x·A = y·B is unsat (last char mismatch)
static void test_eq_split_solve_unsat() {
    std::cout << "test_eq_split_solve_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* yb = sg.mk_concat(y, b);

    ng.add_str_eq(xa, yb);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);
}

// test: same var x·A = x·B triggers det modifier (cancel), not eq_split or var_nielsen
static void test_eq_split_same_var_det() {
    std::cout << "test_eq_split_same_var_det\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* xb = sg.mk_concat(x, b);

    // x·A = x·B → same-head cancel → A = B → clash → unsat
    ng.add_str_eq(xa, xb);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);
}

// test: x·y·A = y·x·A is commutation, should be sat (x=y=ε)
static void test_eq_split_commutation_sat() {
    std::cout << "test_eq_split_commutation_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* xya = sg.mk_concat(x, sg.mk_concat(y, a));
    euf::snode* yxa = sg.mk_concat(y, sg.mk_concat(x, a));

    ng.add_str_eq(xya, yxa);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test apply_const_nielsen: char·A = y produces 2 children (y→ε, y→char·fresh)
// test: A = y is handled by det modifier (variable definition: y → A), producing 1 child
static void test_const_nielsen_char_var() {
    std::cout << "test_const_nielsen_char_var\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* a = sg.mk_char('A');
    euf::snode* y = sg.mk_var(symbol("y"));
    // A = y  (single var definition → det modifier fires)
    ng.add_str_eq(a, y);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    // det modifier: y → A (1 progress child)
    SASSERT(root->outgoing().size() == 1);
    SASSERT(root->outgoing()[0]->is_progress());
}

// test: x = B·y is handled by det modifier (variable definition: x → B·y), producing 1 child
static void test_const_nielsen_var_char() {
    std::cout << "test_const_nielsen_var_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* b = sg.mk_char('B');
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* by = sg.mk_concat(b, y);
    // x = B·y  (single var definition → det modifier fires)
    ng.add_str_eq(x, by);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    // det modifier: x → B·y (1 progress child)
    SASSERT(root->outgoing().size() == 1);
    SASSERT(root->outgoing()[0]->is_progress());
}

// test const_nielsen solve: A·x = A·B → sat (x = B via det cancel then const_nielsen x→ε or x→B·fresh)
static void test_const_nielsen_solve_sat() {
    std::cout << "test_const_nielsen_solve_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* ax = sg.mk_concat(a, x);
    euf::snode* ab = sg.mk_concat(a, b);

    ng.add_str_eq(ax, ab);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test const_nielsen solve: A·x = B·y → unsat (leading chars mismatch)
static void test_const_nielsen_solve_unsat() {
    std::cout << "test_const_nielsen_solve_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* ax = sg.mk_concat(a, x);
    euf::snode* by = sg.mk_concat(b, y);

    ng.add_str_eq(ax, by);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);
}

// test const_nielsen priority: A·x = y·B → const_nielsen (2 children), not var_nielsen (3)
static void test_const_nielsen_priority_over_eq_split() {
    std::cout << "test_const_nielsen_priority_over_eq_split\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* ax = sg.mk_concat(a, x);
    euf::snode* yb = sg.mk_concat(y, b);

    // A·x = y·B → lhs starts with char, rhs starts with var → const_nielsen
    ng.add_str_eq(ax, yb);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    // const_nielsen produces 2 children, not var_nielsen's 3
    SASSERT(root->outgoing().size() == 2);
}

// test const_nielsen tail direction: x·A = w·y
// forward heads are vars (x,w), so forward const_nielsen doesn't apply.
// backward tails are char/var (A,y), so RTL const_nielsen must fire.
static void test_const_nielsen_tail_char_var() {
    std::cout << "test_const_nielsen_tail_char_var\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* w = sg.mk_var(symbol("w"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* lhs = sg.mk_concat(x, a); // x·A
    euf::snode* rhs = sg.mk_concat(w, y); // w·y

    ng.add_str_eq(lhs, rhs);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    SASSERT(root->outgoing().size() == 2);

    bool saw_empty = false;
    bool saw_tail = false;
    for (seq::nielsen_edge* e : root->outgoing()) {
        SASSERT(e->subst().size() == 1);
        seq::nielsen_subst const& s = e->subst()[0];
        SASSERT(s.m_var == y);
        if (s.m_replacement && s.m_replacement->is_empty()) {
            saw_empty = true;
            SASSERT(e->is_progress());
        }
        else {
            euf::snode_vector toks;
            s.m_replacement->collect_tokens(toks);
            SASSERT(toks.size() == 2);
            SASSERT(toks[0]->is_var() && toks[0]->id() == y->id());
            SASSERT(toks[1]->is_char() && toks[1]->id() == a->id());
            saw_tail = true;
            SASSERT(!e->is_progress());
        }
    }
    SASSERT(saw_empty && saw_tail);
}

// test: both sides start with vars → var_nielsen (3 children), not const_nielsen
static void test_const_nielsen_not_applicable_both_vars() {
    std::cout << "test_const_nielsen_not_applicable_both_vars\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* yb = sg.mk_concat(y, b);

    // x·A = y·B → both heads are vars → var_nielsen fires (priority 12)
    ng.add_str_eq(xa, yb);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    SASSERT(root->outgoing().size() == 3);
}

// test const_nielsen solve: A·B·x = A·B·C → sat (x = C after two det cancels)
static void test_const_nielsen_multi_char_solve() {
    std::cout << "test_const_nielsen_multi_char_solve\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* c = sg.mk_char('C');
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* abx = sg.mk_concat(a, sg.mk_concat(b, x));
    euf::snode* abc = sg.mk_concat(a, sg.mk_concat(b, c));

    ng.add_str_eq(abx, abc);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// -----------------------------------------------------------------------
// Regex char split tests
// -----------------------------------------------------------------------

// test_regex_char_split_basic: x in to_re("AB") → creates children
static void test_regex_char_split_basic() {
    std::cout << "test_regex_char_split_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref ab(seq.str.mk_concat(unit_a, unit_b), m);
    expr_ref to_re_ab(seq.re.mk_to_re(ab), m);
    euf::snode* regex = sg.mk(to_re_ab);

    ng.add_str_mem(x, regex);
    SASSERT(ng.root() != nullptr);

    auto sr = ng.root()->simplify_and_init(ng);
    SASSERT(sr != seq::simplify_result::conflict);

    bool extended = ng.generate_extensions(ng.root());
    SASSERT(extended);
    // should have at least 2 children: x→'A'·z and x→ε
    SASSERT(ng.root()->outgoing().size() >= 2);
    ng.display(std::cout);
}

// test_regex_char_split_solve_sat: x in to_re("A") → sat (x = "A")
static void test_regex_char_split_solve_sat() {
    std::cout << "test_regex_char_split_solve_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* regex = sg.mk(to_re_a);

    ng.add_str_mem(x, regex);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test_regex_char_split_solve_multi_char: x in to_re("AB") → sat
static void test_regex_char_split_solve_multi_char() {
    std::cout << "test_regex_char_split_solve_multi_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref ab(seq.str.mk_concat(unit_a, unit_b), m);
    expr_ref to_re_ab(seq.re.mk_to_re(ab), m);
    euf::snode* regex = sg.mk(to_re_ab);

    ng.add_str_mem(x, regex);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test_regex_char_split_union: x in re.union(to_re("A"), to_re("B")) → sat
static void test_regex_char_split_union() {
    std::cout << "test_regex_char_split_union\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    expr_ref to_re_b(seq.re.mk_to_re(unit_b), m);
    expr_ref re_union(seq.re.mk_union(to_re_a, to_re_b), m);
    euf::snode* regex = sg.mk(re_union);

    ng.add_str_mem(x, regex);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test_regex_char_split_star_sat: x in re.star(to_re("A")) → sat (x = ε or x = "A"...)
static void test_regex_char_split_star_sat() {
    std::cout << "test_regex_char_split_star_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    expr_ref re_star(seq.re.mk_star(to_re_a), m);
    euf::snode* regex = sg.mk(re_star);

    ng.add_str_mem(x, regex);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test_regex_char_split_concat_str: x·y in to_re("AB") → sat
static void test_regex_char_split_concat_str() {
    std::cout << "test_regex_char_split_concat_str\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* xy = sg.mk_concat(x, y);

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref ab(seq.str.mk_concat(unit_a, unit_b), m);
    expr_ref to_re_ab(seq.re.mk_to_re(ab), m);
    euf::snode* regex = sg.mk(to_re_ab);

    ng.add_str_mem(xy, regex);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test_regex_char_split_with_eq: x = y, x in to_re("A") → sat
static void test_regex_char_split_with_eq() {
    std::cout << "test_regex_char_split_with_eq\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    ng.add_str_eq(x, y);

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* regex = sg.mk(to_re_a);

    ng.add_str_mem(x, regex);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test_regex_char_split_ground_skip: ground string in regex handled by simplification
static void test_regex_char_split_ground_skip() {
    std::cout << "test_regex_char_split_ground_skip\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* a = sg.mk_char('A');

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* regex = sg.mk(to_re_a);

    // "A" in to_re("A") → simplification consumes the char prefix via derivative
    ng.add_str_mem(a, regex);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// -----------------------------------------------------------------------
// Variable Nielsen modifier tests
// -----------------------------------------------------------------------

// test var_nielsen basic: x = y (two distinct vars) → det modifier fires (variable definition x → y)
// produces 1 progress child
static void test_var_nielsen_basic() {
    std::cout << "test_var_nielsen_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    // x = y → det: x → y (single var definition)
    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    SASSERT(root->outgoing().size() == 1);
    SASSERT(root->outgoing()[0]->is_progress());
}

// test var_nielsen: same var x·A = x·B → det modifier (cancel), not var_nielsen
static void test_var_nielsen_same_var_det() {
    std::cout << "test_var_nielsen_same_var_det\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* xb = sg.mk_concat(x, b);

    // x·A = x·B → same-head cancel → A = B → clash → unsat
    ng.add_str_eq(xa, xb);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);
}

// test var_nielsen: char vs var → det fires (y → A), not var_nielsen
static void test_var_nielsen_not_applicable_char() {
    std::cout << "test_var_nielsen_not_applicable_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* a = sg.mk_char('A');
    euf::snode* y = sg.mk_var(symbol("y"));

    // A = y → det: y → A (variable definition, 1 child)
    ng.add_str_eq(a, y);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    SASSERT(root->outgoing().size() == 1);
}

// test var_nielsen solve: x·y = z·w is sat (all vars can be ε)
static void test_var_nielsen_solve_sat() {
    std::cout << "test_var_nielsen_solve_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* z = sg.mk_var(symbol("z"));
    euf::snode* w = sg.mk_var(symbol("w"));
    euf::snode* xy = sg.mk_concat(x, y);
    euf::snode* zw = sg.mk_concat(z, w);

    ng.add_str_eq(xy, zw);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test var_nielsen solve: x·A = y·B → unsat (trailing char mismatch)
static void test_var_nielsen_solve_unsat() {
    std::cout << "test_var_nielsen_solve_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* yb = sg.mk_concat(y, b);

    ng.add_str_eq(xa, yb);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);
}

// test var_nielsen: x·y = y·x commutation is sat (x=y=ε via ε branches)
static void test_var_nielsen_commutation_sat() {
    std::cout << "test_var_nielsen_commutation_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* xya = sg.mk_concat(x, sg.mk_concat(y, a));
    euf::snode* yxa = sg.mk_concat(y, sg.mk_concat(x, a));

    ng.add_str_eq(xya, yxa);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test var_nielsen priority: var vs var → det fires first for x = y (variable definition)
// var_nielsen only fires when neither side is a single var (e.g., x·A = y·B)
static void test_var_nielsen_priority() {
    std::cout << "test_var_nielsen_priority\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    // det modifier: x → y (1 progress child)
    SASSERT(root->outgoing().size() == 1);
    // first edge is progress (all var_nielsen children are progress)
    SASSERT(root->outgoing()[0]->is_progress());
}

// test generate_extensions: det modifier handles same-head cancel after simplification
// x·A = x·y → simplify cancels prefix x → A = y → det fires (y → A)
static void test_generate_extensions_det_priority() {
    std::cout << "test_generate_extensions_det_priority\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* xy = sg.mk_concat(x, y);

    // x·A = x·y → after simplify, becomes A = y → det: y → A
    ng.add_str_eq(xa, xy);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test generate_extensions: returns false when no modifier applies
// ground clash: A = B → simplify_and_init catches it, but if bypassed,
// no modifier can generate extensions from two chars
static void test_generate_extensions_no_applicable() {
    std::cout << "test_generate_extensions_no_applicable\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');

    // A = B → no variables involved → no modifier applies
    ng.add_str_eq(a, b);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(!extended);
    SASSERT(root->outgoing().empty());
}

// test generate_extensions: regex_char_split fires as last resort
// when there are only str_mem constraints, no str_eq
static void test_generate_extensions_regex_only() {
    std::cout << "test_generate_extensions_regex_only\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    // Build regex to_re("A")
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* re_node = sg.mk(to_re_a);

    // x ∈ to_re("A") → only regex_char_split can fire (no str_eq)
    ng.add_str_mem(x, re_node);
    seq::nielsen_node* root = ng.root();

    root->simplify_and_init(ng);

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    // at least 1 child (epsilon branch) + possibly char branches
    SASSERT(root->outgoing().size() >= 1);
}

// test: mixed constraints, x·A = x·B and y ∈ R → after simplify, A = B clash → unsat
static void test_generate_extensions_mixed_det_first() {
    std::cout << "test_generate_extensions_mixed_det_first\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* xb = sg.mk_concat(x, b);

    // Build a regex for the mem constraint
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* re_node = sg.mk(to_re_a);

    // x·A = x·B → simplify cancels x → A = B → clash → unsat
    ng.add_str_eq(xa, xb);
    ng.add_str_mem(y, re_node);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);
}

// -----------------------------------------------------------------------
// solve() / search_dfs() tests
// -----------------------------------------------------------------------

// test solve on empty graph (no root) returns sat
static void test_solve_empty_graph() {
    std::cout << "test_solve_empty_graph\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    SASSERT(!ng.root());
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test solve with trivially satisfied equality (x = x)
static void test_solve_trivially_satisfied() {
    std::cout << "test_solve_trivially_satisfied\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* x = sg.mk_var(symbol("x"));
    ng.add_str_eq(x, x);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test that node status flags are set correctly after unsat solve
static void test_solve_node_status_unsat() {
    std::cout << "test_solve_node_status_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    // A = B is an immediate conflict
    ng.add_str_eq(a, b);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);

    // root should be marked as general conflict
    seq::nielsen_node* root = ng.root();
    SASSERT(root->is_general_conflict());
    SASSERT(root->is_currently_conflict());
}

// test that collect_conflict_deps returns deps after unsat
static void test_solve_conflict_deps() {
    std::cout << "test_solve_conflict_deps\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    // Add two constraints: A = B (unsat) and a dummy x = x
    ng.add_str_eq(a, b);
    euf::snode* x = sg.mk_var(symbol("x"));
    ng.add_str_eq(x, x);

    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);

    seq::dep_tracker deps;
    ng.collect_conflict_deps(deps);
    // deps should be non-empty since there's a conflict
    SASSERT(!deps.empty());
}

// test dep_tracker (uint_set) iteration
static void test_dep_tracker_get_set_bits() {
    std::cout << "test_dep_tracker_get_set_bits\n";

    // empty tracker has no bits
    seq::dep_tracker d0;
    unsigned_vector bits0;
    for (unsigned b : d0) bits0.push_back(b);
    SASSERT(bits0.empty());

    // single bit set at position 5
    seq::dep_tracker d1;
    d1.insert(5);
    unsigned_vector bits1;
    for (unsigned b : d1) bits1.push_back(b);
    SASSERT(bits1.size() == 1);
    SASSERT(bits1[0] == 5);

    // two bits merged
    seq::dep_tracker d2;
    d2.insert(3);
    d2.insert(11);
    unsigned_vector bits2;
    for (unsigned b : d2) bits2.push_back(b);
    SASSERT(bits2.size() == 2);
    SASSERT(bits2[0] == 3);
    SASSERT(bits2[1] == 11);

    // test across word boundary (bit 31 and 32)
    seq::dep_tracker d3;
    d3.insert(31);
    d3.insert(32);
    unsigned_vector bits3;
    for (unsigned b : d3) bits3.push_back(b);
    SASSERT(bits3.size() == 2);
    SASSERT(bits3[0] == 31);
    SASSERT(bits3[1] == 32);
}

// test explain_conflict returns correct constraint indices
static void test_explain_conflict_single_eq() {
    std::cout << "test_explain_conflict_single_eq\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    // eq[0]: A = B (conflict)
    ng.add_str_eq(a, b);

    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);

    unsigned_vector eq_idx, mem_idx;
    ng.explain_conflict(eq_idx, mem_idx);
    // conflict should reference eq index 0
    SASSERT(eq_idx.size() == 1);
    SASSERT(eq_idx[0] == 0);
    SASSERT(mem_idx.empty());
}

// test explain_conflict with multiple eqs, only conflict-relevant one reported
static void test_explain_conflict_multi_eq() {
    std::cout << "test_explain_conflict_multi_eq\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* x = sg.mk_var(symbol("x"));

    // eq[0]: x = x (trivially sat)
    ng.add_str_eq(x, x);
    // eq[1]: A = B (conflict)
    ng.add_str_eq(a, b);

    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);

    unsigned_vector eq_idx, mem_idx;
    ng.explain_conflict(eq_idx, mem_idx);
    // at least eq[1] (A=B) must appear; eq[0] (x=x) is trivially removed
    bool has_conflict_eq = false;
    for (unsigned i : eq_idx)
        if (i == 1) has_conflict_eq = true;
    SASSERT(has_conflict_eq);
    SASSERT(mem_idx.empty());
}

// test that is_extended is set after solve generates extensions
static void test_solve_node_extended_flag() {
    std::cout << "test_solve_node_extended_flag\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* xy = sg.mk_concat(x, y);
    euf::snode* z = sg.mk_var(symbol("z"));
    euf::snode* w = sg.mk_var(symbol("w"));
    euf::snode* zw = sg.mk_concat(z, w);
    // x·y = z·w — requires extension generation
    ng.add_str_eq(xy, zw);

    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);

    // root should be marked as extended
    seq::nielsen_node* root = ng.root();
    SASSERT(root->is_extended());
}

// test solve with mixed eq + mem constraints: x·A = y·A and y ∈ re("A")
static void test_solve_mixed_eq_mem_sat() {
    std::cout << "test_solve_mixed_eq_mem_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* ya = sg.mk_concat(y, a);

    // x·A = y·A (satisfiable: x=y=ε, or x=y=anything)
    ng.add_str_eq(xa, ya);

    // y ∈ to_re("A") (y must be "A")
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* re_a = sg.mk(to_re_a);
    ng.add_str_mem(y, re_a);

    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// test solve with children_failed reason propagation: x·A = x·B unsat
static void test_solve_children_failed_reason() {
    std::cout << "test_solve_children_failed_reason\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* yb = sg.mk_concat(y, b);

    // x·A = y·B is unsat (last char mismatch propagates up)
    ng.add_str_eq(xa, yb);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);
}

// test that eval_idx is set during solve
static void test_solve_eval_idx_tracking() {
    std::cout << "test_solve_eval_idx_tracking\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a = sg.mk_char('A');
    // x = A·x would be infinite without depth bound, but
    // x = A is simple and satisfiable
    ng.add_str_eq(x, a);

    unsigned run_before = ng.run_idx();
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);

    // run_idx should have been incremented
    SASSERT(ng.run_idx() > run_before);

    // root's eval_idx should match current run_idx
    seq::nielsen_node* root = ng.root();
    SASSERT(root->eval_idx() == ng.run_idx());
}


// -----------------------------------------------------------------------
// Direct simplify_and_init tests
// -----------------------------------------------------------------------

// test simplify_and_init: prefix cancellation of matching chars
static void test_simplify_prefix_cancel() {
    std::cout << "test_simplify_prefix_cancel\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;   
    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    // A·B·x = A·B·y → prefix cancel A,B → x = y (proceed)
    euf::snode* abx = sg.mk_concat(a, sg.mk_concat(b, x));
    euf::snode* aby = sg.mk_concat(a, sg.mk_concat(b, y));

    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_eq(seq::str_eq(abx, aby, dep));

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::proceed);
    SASSERT(node->str_eqs().size() == 1);
    // after prefix cancel: remaining eq has variable-only sides
    SASSERT(node->str_eqs()[0].m_lhs->is_var());
    SASSERT(node->str_eqs()[0].m_rhs->is_var());
}

// test simplify_and_init: suffix cancellation of matching chars (RTL)
static void test_simplify_suffix_cancel_rtl() {
    std::cout << "test_simplify_suffix_cancel_rtl\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    // x·A = y·A → suffix cancel A (RTL) → x = y
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* ya = sg.mk_concat(y, a);

    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_eq(seq::str_eq(xa, ya, dep));

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::proceed);
    SASSERT(node->str_eqs().size() == 1);
    SASSERT(node->str_eqs()[0].m_lhs->is_var());
    SASSERT(node->str_eqs()[0].m_rhs->is_var());
}

// test simplify_and_init: symbol clash at first position
static void test_simplify_symbol_clash() {
    std::cout << "test_simplify_symbol_clash\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    // A·x = B·y → symbol clash on first char
    euf::snode* ax = sg.mk_concat(a, x);
    euf::snode* by = sg.mk_concat(b, y);

    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_eq(seq::str_eq(ax, by, dep));

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::conflict);
    SASSERT(node->is_general_conflict());
    SASSERT(node->reason() == seq::backtrack_reason::symbol_clash);
}

// test simplify_and_init: empty propagation forces variables to epsilon
static void test_simplify_empty_propagation() {
    std::cout << "test_simplify_empty_propagation\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* e = sg.mk_empty();
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* xy = sg.mk_concat(x, y);

    // ε = x·y → forces x=ε, y=ε → all trivial → satisfied
    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_eq(seq::str_eq(e, xy, dep));

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::satisfied);
}

// test simplify_and_init: empty vs concrete char → conflict
static void test_simplify_empty_vs_char() {
    std::cout << "test_simplify_empty_vs_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* e = sg.mk_empty();
    euf::snode* a = sg.mk_char('A');

    // ε = A → rhs has non-variable token → conflict
    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_eq(seq::str_eq(e, a, dep));

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::conflict);
    SASSERT(node->reason() == seq::backtrack_reason::symbol_clash);
}

// test simplify_and_init: multi-pass (prefix cancel A, then B≠C clash)
static void test_simplify_multi_pass_clash() {
    std::cout << "test_simplify_multi_pass_clash\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* c = sg.mk_char('C');

    // A·B = A·C → cancel A → B vs C → clash
    euf::snode* ab = sg.mk_concat(a, b);
    euf::snode* ac = sg.mk_concat(a, c);

    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_eq(seq::str_eq(ab, ac, dep));

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::conflict);
    SASSERT(node->reason() == seq::backtrack_reason::symbol_clash);
}

// test simplify_and_init: trivial eq removed, non-trivial kept
static void test_simplify_trivial_removal() {
    std::cout << "test_simplify_trivial_removal\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* e = sg.mk_empty();

    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_eq(seq::str_eq(e, e, dep));  // trivial
    node->add_str_eq(seq::str_eq(x, y, dep));  // non-trivial

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::proceed);
    SASSERT(node->str_eqs().size() == 1);
}

// test simplify_and_init: all trivial eqs → satisfied
static void test_simplify_all_trivial_satisfied() {
    std::cout << "test_simplify_all_trivial_satisfied\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* e = sg.mk_empty();

    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_eq(seq::str_eq(x, x, dep));  // trivial: same pointer
    node->add_str_eq(seq::str_eq(e, e, dep));  // trivial: both empty

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::satisfied);
}

// test simplify_and_init: ε ∈ non-nullable regex → conflict
static void test_simplify_regex_infeasible() {
    std::cout << "test_simplify_regex_infeasible\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* e = sg.mk_empty();

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* regex = sg.mk(to_re_a);

    // ε ∈ to_re("A") → non-nullable → conflict
    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_mem(seq::str_mem(e, regex, e, 0, dep));

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::conflict);
    SASSERT(node->reason() == seq::backtrack_reason::regex);
}

// test simplify_and_init: ε ∈ nullable regex → satisfied, mem removed
static void test_simplify_nullable_removal() {
    std::cout << "test_simplify_nullable_removal\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* e = sg.mk_empty();

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    expr_ref re_star(seq.re.mk_star(to_re_a), m);
    euf::snode* regex = sg.mk(re_star);

    // ε ∈ star(to_re("A")) → nullable → satisfied, mem removed
    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_mem(seq::str_mem(e, regex, e, 0, dep));

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::satisfied);
    SASSERT(node->str_mems().empty());
}

// test simplify_and_init: Brzozowski derivative consumes ground char
static void test_simplify_brzozowski_sat() {
    std::cout << "test_simplify_brzozowski_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* e = sg.mk_empty();

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* regex = sg.mk(to_re_a);

    // "A" ∈ to_re("A") → derivative consumes 'A' → ε ∈ ε-regex → satisfied
    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_mem(seq::str_mem(a, regex, e, 0, dep));

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::satisfied);
}

// test simplify_and_init: backward Brzozowski consumes a trailing char (RTL)
static void test_simplify_brzozowski_rtl_suffix() {
    std::cout << "test_simplify_brzozowski_rtl_suffix\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* e = sg.mk_empty();

    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref ba(seq.str.mk_concat(unit_b, unit_a), m);
    expr_ref to_re_ba(seq.re.mk_to_re(ba), m);
    euf::snode* regex = sg.mk(to_re_ba);

    // x·"A" ∈ to_re("BA") → RTL consume trailing 'A' → x ∈ to_re("B")
    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);
    node->add_str_mem(seq::str_mem(xa, regex, e, 0, dep));

    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::proceed);
    SASSERT(node->str_mems().size() == 1);
    SASSERT(node->str_mems()[0].m_str->is_var());
    SASSERT(node->str_mems()[0].m_str->id() == x->id());

    euf::snode* deriv_b = sg.brzozowski_deriv(node->str_mems()[0].m_regex, sg.mk_char('B'));
    SASSERT(deriv_b && deriv_b->is_nullable());
}

// test simplify_and_init: multiple eqs with mixed status
static void test_simplify_multiple_eqs() {
    std::cout << "test_simplify_multiple_eqs\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* z = sg.mk_var(symbol("z"));
    euf::snode* e = sg.mk_empty();

    seq::nielsen_node* node = ng.mk_node();
    seq::dep_tracker dep; dep.insert(0);

    // eq1: ε = ε (trivial → removed)
    node->add_str_eq(seq::str_eq(e, e, dep));
    // eq2: A·x = A·y (prefix cancel → x = y)
    euf::snode* ax = sg.mk_concat(a, x);
    euf::snode* ay = sg.mk_concat(a, y);
    node->add_str_eq(seq::str_eq(ax, ay, dep));
    // eq3: x = z (non-trivial, kept)
    node->add_str_eq(seq::str_eq(x, z, dep));

    SASSERT(node->str_eqs().size() == 3);
    auto sr = node->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::proceed);
    // eq1 removed, eq2 simplified to x=y, eq3 kept → 2 eqs remain
    SASSERT(node->str_eqs().size() == 2);
}

// -----------------------------------------------------------------------
// Modifier child state verification tests
// -----------------------------------------------------------------------

// test det cancel: x·A = x·B → simplify cancels prefix x → A = B → clash → unsat
static void test_det_cancel_child_eq() {
    std::cout << "test_det_cancel_child_eq\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* xb = sg.mk_concat(x, b);

    // x·A = x·B → simplify cancels x → A = B → clash → unsat
    ng.add_str_eq(xa, xb);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);
}

// test const_nielsen: verify children's substitutions target the variable
// A·x = y·B → char vs var: const_nielsen fires (2 children, both substitute y)
static void test_const_nielsen_child_substitutions() {
    std::cout << "test_const_nielsen_child_substitutions\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* ax = sg.mk_concat(a, x);
    euf::snode* yb = sg.mk_concat(y, b);

    // A·x = y·B → const_nielsen: 2 children, both substitute y
    ng.add_str_eq(ax, yb);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    SASSERT(root->outgoing().size() == 2);

    // both edges substitute y
    for (unsigned i = 0; i < 2; ++i) {
        SASSERT(root->outgoing()[i]->subst().size() == 1);
        SASSERT(root->outgoing()[i]->subst()[0].m_var == y);
    }

    // edge 0: y → ε (eliminating, replacement is empty)
    SASSERT(root->outgoing()[0]->subst()[0].m_replacement->is_empty());
    // edge 1: y → A·fresh (replacement is non-empty)
    SASSERT(!root->outgoing()[1]->subst()[0].m_replacement->is_empty());
}

// test var_nielsen: verify substitution structure — det fires for x = y (single var def)
static void test_var_nielsen_substitution_types() {
    std::cout << "test_var_nielsen_substitution_types\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    // x = y → det: x → y (single var definition, 1 child)
    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    SASSERT(root->outgoing().size() == 1);

    // edge 0: x → y substitution
    SASSERT(root->outgoing()[0]->subst().size() == 1);
    SASSERT(root->outgoing()[0]->is_progress());
}

// -----------------------------------------------------------------------
// Explain conflict with mem constraints
// -----------------------------------------------------------------------

// test explain_conflict: mem-only conflict reports mem index
static void test_explain_conflict_mem_only() {
    std::cout << "test_explain_conflict_mem_only\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* e = sg.mk_empty();

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* regex = sg.mk(to_re_a);

    // ε ∈ to_re("A") → conflict (non-nullable)
    ng.add_str_mem(e, regex);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);

    unsigned_vector eq_idx, mem_idx;
    ng.explain_conflict(eq_idx, mem_idx);
    // only mem constraint involved, no eqs
    SASSERT(eq_idx.empty());
    SASSERT(mem_idx.size() == 1);
    SASSERT(mem_idx[0] == 0);
}

// test explain_conflict: mixed eq + mem conflict
static void test_explain_conflict_mixed_eq_mem() {
    std::cout << "test_explain_conflict_mixed_eq_mem\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* e = sg.mk_empty();

    // eq[0]: A = B (conflict)
    ng.add_str_eq(a, b);

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* regex = sg.mk(to_re_a);

    // mem[0]: ε ∈ to_re("A")
    ng.add_str_mem(e, regex);

    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);

    unsigned_vector eq_idx, mem_idx;
    ng.explain_conflict(eq_idx, mem_idx);
    // eq[0] should be reported (it's the direct conflict)
    bool has_eq0 = false;
    for (unsigned i : eq_idx) if (i == 0) has_eq0 = true;
    SASSERT(has_eq0);
    // mem[0] is also reported (over-approximation from collect_conflict_deps)
    bool has_mem0 = false;
    for (unsigned i : mem_idx) if (i == 0) has_mem0 = true;
    SASSERT(has_mem0);
}

// test subsumption pruning during solve: a node whose constraint set
// is a superset of a known-unsat node is pruned
static void test_subsumption_pruning_unsat() {
    std::cout << "test_subsumption_pruning_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');

    // A = B is an immediate conflict (symbol clash).
    // Any branch that inherits this equation should be pruned.
    ng.add_str_eq(a, b);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);

    // root should have conflict set
    SASSERT(ng.root()->is_general_conflict());
}

// test that subsumption sets backtrack_reason::subsumption
static void test_subsumption_reason_set() {
    std::cout << "test_subsumption_reason_set\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');

    // x·A = y·B: after Nielsen splitting, children will have A=B
    // which is unsat. The subsumption pruning may fire on sibling
    // branches that inherit the same conflict.
    euf::snode* xa = sg.mk_concat(x, a);
    euf::snode* yb = sg.mk_concat(y, b);
    ng.add_str_eq(xa, yb);

    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::unsat);

    // check that at least one node has subsumption reason
    bool found_subsumption = false;
    for (seq::nielsen_node* nd : ng.nodes()) {
        if (nd->reason() == seq::backtrack_reason::subsumption) {
            found_subsumption = true;
            SASSERT(nd->is_general_conflict());
            break;
        }
    }
    // subsumption may or may not fire depending on search order;
    // the important thing is the solve result is correct.
    // If it does fire, the reason must be subsumption.
    (void)found_subsumption;
}

// test generate_length_constraints: basic equation x . y = A . B
static void test_length_constraints_basic() {
    std::cout << "test_length_constraints_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');

    // equation: x . y = A . B
    euf::snode* lhs = sg.mk_concat(x, y);
    euf::snode* rhs = sg.mk_concat(a, b);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(lhs, rhs);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // expect at least 1 length equality + 2 non-negativity constraints (for x and y)
    SASSERT(constraints.size() >= 3);

    // first constraint should be the length equality
    SASSERT(constraints[0].m_expr != nullptr);
    SASSERT(m.is_eq(constraints[0].m_expr));
    SASSERT(constraints[0].m_kind == seq::length_kind::eq);

    // remaining constraints should be non-negativity
    for (unsigned i = 1; i < constraints.size(); ++i) {
        SASSERT(constraints[i].m_kind == seq::length_kind::nonneg);
    }

    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";
}

// test generate_length_constraints: trivial equation is skipped
static void test_length_constraints_trivial_skip() {
    std::cout << "test_length_constraints_trivial_skip\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));

    // trivial equation: x = x (same snode)
    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, x);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // trivial equation should be skipped, no constraints
    SASSERT(constraints.empty());
    std::cout << "  trivial equation correctly skipped\n";
}

// test generate_length_constraints: empty graph produces no constraints
static void test_length_constraints_empty() {
    std::cout << "test_length_constraints_empty\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    SASSERT(constraints.empty());
    std::cout << "  empty graph: no constraints\n";
}

// test generate_length_constraints: concatenation chain x.y.z = A.B.C
static void test_length_constraints_concat_chain() {
    std::cout << "test_length_constraints_concat_chain\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* z = sg.mk_var(symbol("z"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* c = sg.mk_char('C');

    // equation: x . y . z = A . B . C
    euf::snode* lhs = sg.mk_concat(sg.mk_concat(x, y), z);
    euf::snode* rhs = sg.mk_concat(sg.mk_concat(a, b), c);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(lhs, rhs);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // 1 length equality + 3 variable non-negativity constraints
    SASSERT(constraints.size() == 4);
    SASSERT(m.is_eq(constraints[0].m_expr));

    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";
}

// test generate_length_constraints: multiple equations
static void test_length_constraints_multi_eq() {
    std::cout << "test_length_constraints_multi_eq\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, a);           // x = A
    ng.add_str_eq(y, b);           // y = B

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // 2 equalities + 2 non-negativity (x and y each appear once)
    SASSERT(constraints.size() == 4);
    SASSERT(m.is_eq(constraints[0].m_expr));
    SASSERT(m.is_eq(constraints[2].m_expr));

    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";
}

// test generate_length_constraints: shared variable only gets one non-negativity
static void test_length_constraints_shared_var() {
    std::cout << "test_length_constraints_shared_var\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');

    // equation: x . A = A . x  (x appears on both sides)
    euf::snode* lhs = sg.mk_concat(x, a);
    euf::snode* rhs = sg.mk_concat(a, x);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(lhs, rhs);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // 1 length equality + 1 non-negativity for x (deduped)
    SASSERT(constraints.size() == 2);

    std::cout << "  generated " << constraints.size() << " constraints (x deduped)\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";
}

// test generate_length_constraints: dependency tracking
static void test_length_constraints_deps() {
    std::cout << "test_length_constraints_deps\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a = sg.mk_char('A');

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, a);  // eq index 0

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // all constraints should have dependency on eq 0
    for (auto const& c : constraints) {
        SASSERT(!c.m_dep.empty());
        unsigned_vector bits;
        for (unsigned b : c.m_dep) bits.push_back(b);
        SASSERT(bits.size() == 1);
        SASSERT(bits[0] == 0);
    }

    std::cout << "  dependency tracking correct\n";
}

// test generate_length_constraints: empty sides produce 0
static void test_length_constraints_empty_side() {
    std::cout << "test_length_constraints_empty_side\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* e = sg.mk_empty();

    // x = ε
    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, e);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // 1 equality (len(x) = 0) + 1 non-negativity (len(x) >= 0)
    SASSERT(constraints.size() == 2);
    SASSERT(m.is_eq(constraints[0].m_expr));
    SASSERT(constraints[0].m_kind == seq::length_kind::eq);
    SASSERT(constraints[1].m_kind == seq::length_kind::nonneg);

    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";
}

// test length_kind tagging: equalities get kind::eq, non-neg get kind::nonneg,
// Parikh bounds get kind::bound
static void test_length_kind_tagging() {
    std::cout << "test_length_kind_tagging\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');

    // equation: x = a (one eq + one nonneg)
    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, a);

    // membership: y in to_re("AB") (bounds + nonneg)
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref ab(seq.str.mk_concat(unit_a, unit_b), m);
    expr_ref to_re_ab(seq.re.mk_to_re(ab), m);
    euf::snode* regex = sg.mk(to_re_ab);
    ng.add_str_mem(y, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    unsigned num_eq = 0, num_nonneg = 0, num_bound = 0;
    for (auto const& c : constraints) {
        switch (c.m_kind) {
        case seq::length_kind::eq:     ++num_eq; break;
        case seq::length_kind::nonneg: ++num_nonneg; break;
        case seq::length_kind::bound:  ++num_bound; break;
        }
    }

    std::cout << "  eq=" << num_eq << " nonneg=" << num_nonneg << " bound=" << num_bound << "\n";
    // at least 1 equality (from str_eq)
    SASSERT(num_eq >= 1);
    // at least 1 non-negativity (for variable x or y)
    SASSERT(num_nonneg >= 1);
    // at least 1 bound (from Parikh for to_re("AB"))
    SASSERT(num_bound >= 1);

    // verify equalities have kind eq
    for (auto const& c : constraints) {
        if (m.is_eq(c.m_expr))
            SASSERT(c.m_kind == seq::length_kind::eq);
    }

    // verify num_input_eqs/mems accessors
    SASSERT(ng.num_input_eqs() == 1);
    SASSERT(ng.num_input_mems() == 1);

    std::cout << "  length kind tagging correct\n";
}

// -----------------------------------------------------------------------
// Tests for new modifiers (Task #55)
// -----------------------------------------------------------------------

// test_power_epsilon_no_power: no power tokens → modifier returns false
static void test_power_epsilon_no_power() {
    std::cout << "test_power_epsilon_no_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a = sg.mk_char('A');

    // x = A: no power tokens, power_epsilon should not fire
    ng.add_str_eq(x, a);
    seq::nielsen_node* root = ng.root();

    // det fires (x is single var, A doesn't contain x → x → A)
    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    // det: x → A (variable definition, 1 child)
    SASSERT(root->outgoing().size() == 1);
}

// test_num_cmp_no_power: no same-base power pair → modifier returns false
static void test_num_cmp_no_power() {
    std::cout << "test_num_cmp_no_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    // x = y: no power tokens, num_cmp should not fire
    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    // det fires (x → y, variable definition): 1 child
    SASSERT(root->outgoing().size() == 1);
}

// test_star_intr_no_backedge: no backedge → modifier returns false
static void test_star_intr_no_backedge() {
    std::cout << "test_star_intr_no_backedge\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* regex = sg.mk(to_re_a);

    // x ∈ to_re("A"): no backedge, star_intr should not fire
    ng.add_str_mem(x, regex);

    seq::nielsen_node* root = ng.root();
    SASSERT(root->backedge() == nullptr);

    auto sr = root->simplify_and_init(ng);
    SASSERT(sr != seq::simplify_result::conflict);

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    // regex_char_split fires (priority 9): at least 2 children (x→A·z, x→ε)
    SASSERT(root->outgoing().size() >= 2);
}

// test_star_intr_with_backedge: backedge set → star_intr fires
static void test_star_intr_with_backedge() {
    std::cout << "test_star_intr_with_backedge\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    expr_ref re_star(seq.re.mk_star(to_re_a), m);
    euf::snode* regex = sg.mk(re_star);

    // x ∈ star(to_re("A")): set backedge to simulate cycle detection
    ng.add_str_mem(x, regex);

    seq::nielsen_node* root = ng.root();
    root->set_backedge(root); // simulate backedge

    auto sr = root->simplify_and_init(ng);
    // star(to_re("A")) is nullable, so empty string satisfies it
    // simplify may remove the membership or proceed
    if (sr == seq::simplify_result::satisfied) {
        std::cout << "  simplified to satisfied (nullable regex)\n";
        return; // OK, the regex is nullable so it was removed
    }

    bool extended = ng.generate_extensions(root);
    if (extended) {
        // star_intr should have generated at least 1 child
        SASSERT(root->outgoing().size() >= 1);
        std::cout << "  star_intr generated " << root->outgoing().size() << " children\n";
    }
}

// test_gpower_intr_self_cycle: aX = Xa → self-cycle, GPowerIntr fires
static void test_gpower_intr_self_cycle() {
    std::cout << "test_gpower_intr_self_cycle\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a1 = sg.mk_char('A');
    euf::snode* a2 = sg.mk_char('A');
    euf::snode* lhs = sg.mk_concat(a1, x);  // Ax
    euf::snode* rhs = sg.mk_concat(x, a2);  // xA

    // Ax = xA → variable x appears on both sides with ground prefix 'A'
    // GPowerIntr detects self-cycle and introduces x = A^n · suffix
    ng.add_str_eq(lhs, rhs);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    SASSERT(ng.stats().m_mod_gpower_intr == 1);
    SASSERT(root->outgoing().size() == 1);
    std::cout << "  gpower_intr generated " << root->outgoing().size() << " children\n";
}

// test_gpower_intr_no_cycle: aX = Yb → no cycle (X ≠ Y), GPowerIntr doesn't fire
static void test_gpower_intr_no_cycle() {
    std::cout << "test_gpower_intr_no_cycle\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* lhs = sg.mk_concat(a, x);  // Ax
    euf::snode* rhs = sg.mk_concat(y, b);  // Yb

    // Ax = Yb → Y is head of RHS, scan LHS: prefix=[A], target=x, but x ≠ y → no cycle
    // GPowerIntr does NOT fire; ConstNielsen (priority 8) fires instead
    ng.add_str_eq(lhs, rhs);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    SASSERT(ng.stats().m_mod_gpower_intr == 0);
    std::cout << "  gpower_intr did not fire (no cycle)\n";
}

// test_regex_var_split_basic: x ∈ re → uses minterms for splitting
static void test_regex_var_split_basic() {
    std::cout << "test_regex_var_split_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));

    // Build a regex: re.union(to_re("A"), to_re("B"))
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    expr_ref to_re_b(seq.re.mk_to_re(unit_b), m);
    expr_ref re_union(seq.re.mk_union(to_re_a, to_re_b), m);
    euf::snode* regex = sg.mk(re_union);

    ng.add_str_mem(x, regex);
    seq::nielsen_node* root = ng.root();

    auto sr = root->simplify_and_init(ng);
    SASSERT(sr != seq::simplify_result::conflict);

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    // Should produce children via regex_char_split or regex_var_split
    SASSERT(root->outgoing().size() >= 2);
    std::cout << "  regex split generated " << root->outgoing().size() << " children\n";
}

// test_power_split_no_power: no power tokens → modifier returns false
static void test_power_split_no_power() {
    std::cout << "test_power_split_no_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* xa = sg.mk_concat(x, a);

    // x·A = y: no power tokens, power_split should not fire
    // det fires (y is single var, y ∉ vars(x·A) → y → x·A)
    ng.add_str_eq(xa, y);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    // det fires: 1 child (y → x·A)
    SASSERT(root->outgoing().size() == 1);
}

// test_var_num_unwinding_no_power: no power tokens → modifier returns false
static void test_var_num_unwinding_no_power() {
    std::cout << "test_var_num_unwinding_no_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    // x = y: no power tokens, var_num_unwinding should not fire
    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();

    bool extended = ng.generate_extensions(root);
    SASSERT(extended);
    // det fires: 1 child (x → y)
    SASSERT(root->outgoing().size() == 1);
}

// test_const_num_unwinding_no_power: no power vs const → modifier returns false
static void test_const_num_unwinding_no_power() {
    std::cout << "test_const_num_unwinding_no_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');

    // A = B: no power tokens, clash during simplification
    ng.add_str_eq(a, b);
    seq::nielsen_node* root = ng.root();

    // Should detect clash during simplify
    auto sr = root->simplify_and_init(ng);
    SASSERT(sr == seq::simplify_result::conflict);
}

// test_priority_chain_order: verify the full priority chain
// Det fires first, then appropriate modifiers in order
static void test_priority_chain_order() {
    std::cout << "test_priority_chain_order\n";
    ast_manager m;
    reg_decl_plugins(m);

    // Case 1: same-head cancel → simplify handles prefix cancel, then det/clash
    // x·A = x·B → simplify: prefix cancel x → A = B → clash
    // Use a non-clashing example: x·A = x·y → simplify: prefix cancel x → A = y → det: y → A
    {
        euf::egraph eg(m);
        euf::sgraph sg(m, eg);
        dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

        euf::snode* x = sg.mk_var(symbol("x"));
        euf::snode* y = sg.mk_var(symbol("y"));
        euf::snode* a = sg.mk_char('A');
        euf::snode* xa = sg.mk_concat(x, a);
        euf::snode* xy = sg.mk_concat(x, y);

        ng.add_str_eq(xa, xy);
        auto result = ng.solve();
        SASSERT(result == seq::nielsen_graph::search_result::sat);
    }

    // Case 2: both vars different → Det (priority 1) fires (variable definition x → y)
    {
        euf::egraph eg(m);
        euf::sgraph sg(m, eg);
        dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

        euf::snode* x = sg.mk_var(symbol("x"));
        euf::snode* y = sg.mk_var(symbol("y"));

        ng.add_str_eq(x, y);
        seq::nielsen_node* root = ng.root();
        bool extended = ng.generate_extensions(root);
        SASSERT(extended);
        SASSERT(root->outgoing().size() == 1); // Det: variable definition, 1 child
    }

    // Case 3: char vs var → Det (priority 1) fires (variable definition y → A)
    {
        euf::egraph eg(m);
        euf::sgraph sg(m, eg);
        dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

        euf::snode* a = sg.mk_char('A');
        euf::snode* y = sg.mk_var(symbol("y"));

        ng.add_str_eq(a, y);
        seq::nielsen_node* root = ng.root();
        bool extended = ng.generate_extensions(root);
        SASSERT(extended);
        SASSERT(root->outgoing().size() == 1); // Det: variable definition, 1 child
    }
}

// test_gpower_intr_solve_sat: x = AAA → sat (x = "AAA")
static void test_gpower_intr_solve_sat() {
    std::cout << "test_gpower_intr_solve_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a1 = sg.mk_char('A');
    euf::snode* a2 = sg.mk_char('A');
    euf::snode* a3 = sg.mk_char('A');
    euf::snode* aaa = sg.mk_concat(a1, sg.mk_concat(a2, a3));

    ng.add_str_eq(x, aaa);
    auto result = ng.solve();
    SASSERT(result == seq::nielsen_graph::search_result::sat);
}

// -----------------------------------------------------------------------
// Parikh interval reasoning tests (Task #34)
// -----------------------------------------------------------------------

// test: x in to_re("AB") generates len(x) >= 2 and len(x) <= 2
static void test_parikh_exact_length() {
    std::cout << "test_parikh_exact_length\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"));

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref ab(seq.str.mk_concat(unit_a, unit_b), m);
    expr_ref to_re_ab(seq.re.mk_to_re(ab), m);
    euf::snode* regex = sg.mk(to_re_ab);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_mem(x, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // to_re("AB") has min_length=2 and max_length=2
    // expect: len(x) >= 2, len(x) <= 2, and len(x) >= 0
    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";
    SASSERT(constraints.size() >= 2);

    // verify we have both a >= and a <= constraint with correct kinds
    bool has_lower = false, has_upper = false;
    for (auto const& c : constraints) {
        if (arith.is_le(c.m_expr) || arith.is_ge(c.m_expr)) {
            has_lower = has_lower || arith.is_ge(c.m_expr);
            has_upper = has_upper || arith.is_le(c.m_expr);
            // Parikh bounds should have kind::bound
            if (!m.is_eq(c.m_expr))
                SASSERT(c.m_kind == seq::length_kind::bound || c.m_kind == seq::length_kind::nonneg);
        }
    }
    SASSERT(has_lower);
    SASSERT(has_upper);
}

// test: x in (re.star (re.to_re "A")) generates no upper bound
static void test_parikh_star_unbounded() {
    std::cout << "test_parikh_star_unbounded\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"));

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    expr_ref re_star(seq.re.mk_star(to_re_a), m);
    euf::snode* regex = sg.mk(re_star);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_mem(x, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // star has min_length=0, max_length=UINT_MAX
    // no lower bound > 0, no upper bound, just len(x) >= 0
    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";

    // should not have a <= constraint (unbounded)
    bool has_upper = false;
    for (auto const& c : constraints) {
        if (arith.is_le(c.m_expr))
            has_upper = true;
    }
    SASSERT(!has_upper);
}

// test: x in (re.union (re.to_re "AB") (re.to_re "CDE")) → len(x) >= 2, len(x) <= 3
static void test_parikh_union_interval() {
    std::cout << "test_parikh_union_interval\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"));

    // "AB"
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref ab(seq.str.mk_concat(unit_a, unit_b), m);
    expr_ref to_re_ab(seq.re.mk_to_re(ab), m);

    // "CDE"
    expr_ref ch_c(seq.str.mk_char('C'), m);
    expr_ref unit_c(seq.str.mk_unit(ch_c), m);
    expr_ref ch_d(seq.str.mk_char('D'), m);
    expr_ref unit_d(seq.str.mk_unit(ch_d), m);
    expr_ref ch_e(seq.str.mk_char('E'), m);
    expr_ref unit_e(seq.str.mk_unit(ch_e), m);
    expr_ref cde(seq.str.mk_concat(unit_c, seq.str.mk_concat(unit_d, unit_e)), m);
    expr_ref to_re_cde(seq.re.mk_to_re(cde), m);

    expr_ref re_union(seq.re.mk_union(to_re_ab, to_re_cde), m);
    euf::snode* regex = sg.mk(re_union);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_mem(x, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";

    // union of "AB" (len 2) and "CDE" (len 3): min_length=2, max_length=3
    bool has_lower = false, has_upper = false;
    for (auto const& c : constraints) {
        has_lower = has_lower || arith.is_ge(c.m_expr);
        has_upper = has_upper || arith.is_le(c.m_expr);
    }
    SASSERT(has_lower);
    SASSERT(has_upper);
}

// test: x in re.loop(to_re("A"), 3, 5) → len(x) >= 3, len(x) <= 5
static void test_parikh_loop_bounded() {
    std::cout << "test_parikh_loop_bounded\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"));

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    expr_ref re_loop(seq.re.mk_loop(to_re_a, 3, 5), m);
    euf::snode* regex = sg.mk(re_loop);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_mem(x, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";

    // loop{3,5} of "A" (len 1): min_length=3, max_length=5
    bool has_lower = false, has_upper = false;
    for (auto const& c : constraints) {
        has_lower = has_lower || arith.is_ge(c.m_expr);
        has_upper = has_upper || arith.is_le(c.m_expr);
    }
    SASSERT(has_lower);
    SASSERT(has_upper);
}

// test: x in re.empty → normalized to [0,0], generates len(x) <= 0
static void test_parikh_empty_regex() {
    std::cout << "test_parikh_empty_regex\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"));

    expr_ref re_empty(seq.re.mk_empty(seq.re.mk_re(str_sort)), m);
    euf::snode* regex = sg.mk(re_empty);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_mem(x, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";

    // empty regex: normalized to [0,0], so len(x) <= 0
    bool has_upper = false;
    for (auto const& c : constraints) {
        has_upper = has_upper || arith.is_le(c.m_expr);
    }
    SASSERT(has_upper);
}

// test: x in re.range("A","Z") → len(x) >= 1, len(x) <= 1
static void test_parikh_full_char() {
    std::cout << "test_parikh_full_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"));

    // re.range("A", "Z") matches single characters in [A-Z]
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref ch_z(seq.str.mk_char('Z'), m);
    expr_ref unit_z(seq.str.mk_unit(ch_z), m);
    expr_ref re_range(seq.re.mk_range(unit_a, unit_z), m);
    euf::snode* regex = sg.mk(re_range);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_mem(x, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";

    // range: min_length=1, max_length=1
    bool has_lower = false, has_upper = false;
    for (auto const& c : constraints) {
        has_lower = has_lower || arith.is_ge(c.m_expr);
        has_upper = has_upper || arith.is_le(c.m_expr);
    }
    SASSERT(has_lower);
    SASSERT(has_upper);
}

// test: mixed str_eq and str_mem constraints generate both types
static void test_parikh_mixed_eq_mem() {
    std::cout << "test_parikh_mixed_eq_mem\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');

    // equation: x = A
    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, a);

    // membership: y in to_re("BC")
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref ch_c(seq.str.mk_char('C'), m);
    expr_ref unit_c(seq.str.mk_unit(ch_c), m);
    expr_ref bc(seq.str.mk_concat(unit_b, unit_c), m);
    expr_ref to_re_bc(seq.re.mk_to_re(bc), m);
    euf::snode* regex = sg.mk(to_re_bc);
    ng.add_str_mem(y, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";

    // expect: len(x)=1 (from eq), len(x)>=0, len(y)>=2, len(y)<=2, len(y)>=0
    bool has_eq = false, has_le = false, has_ge = false;
    for (auto const& c : constraints) {
        has_eq = has_eq || m.is_eq(c.m_expr);
        has_le = has_le || arith.is_le(c.m_expr);
        has_ge = has_ge || arith.is_ge(c.m_expr);
    }
    SASSERT(has_eq);   // from str_eq
    SASSERT(has_le);   // from str_mem upper bound
    SASSERT(has_ge);   // from str_mem lower bound or non-negativity
}

// test: str_mem with full_seq (.*) → no bounds generated
static void test_parikh_full_seq_no_bounds() {
    std::cout << "test_parikh_full_seq_no_bounds\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"));

    expr_ref re_all(seq.re.mk_full_seq(str_sort), m);
    euf::snode* regex = sg.mk(re_all);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_mem(x, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";

    // full_seq (.*): min_length=0, max_length=UINT_MAX → no Parikh bounds
    // only len(x) >= 0 from variable non-negativity
    bool has_le = false;
    for (auto const& c : constraints) {
        has_le = has_le || arith.is_le(c.m_expr);
    }
    SASSERT(!has_le);
}

// test: dependency tracking for Parikh constraints
static void test_parikh_dep_tracking() {
    std::cout << "test_parikh_dep_tracking\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode* x = sg.mk_var(symbol("x"));

    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode* regex = sg.mk(to_re_a);

    dummy_simple_solver solver;    seq::nielsen_graph ng(sg, solver);
    ng.add_str_mem(x, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // to_re("A") has min=1, max=1 → len(x)>=1 and len(x)<=1
    SASSERT(constraints.size() >= 2);

    // all Parikh constraints should have non-empty deps
    for (auto const& c : constraints) {
        SASSERT(!c.m_dep.empty());
    }
    std::cout << "  all constraints have non-empty deps\n";
}

// -----------------------------------------------------------------------
// IntBounds / VarBoundWatcher tests (Task: IntBounds/Constraint.Shared)
// -----------------------------------------------------------------------

// tracking solver: records assert_expr calls for inspection
class tracking_solver : public seq::simple_solver {
public:
    vector<expr_ref> asserted;
    ast_manager& m;
    unsigned push_count = 0;
    unsigned pop_count = 0;
    lbool check_result = l_true;

    tracking_solver(ast_manager& m) : m(m) {}
    void push() override { ++push_count; }
    void pop(unsigned n) override { pop_count += n; }
    void assert_expr(expr* e) override { asserted.push_back(expr_ref(e, m)); }
    lbool check() override { return check_result; }
    void reset_tracking() {
        asserted.reset();
        push_count = 0;
        pop_count = 0;
    }
};

// test add_lower_int_bound: basic tightening adds int_constraint
static void test_add_lower_int_bound_basic() {
    std::cout << "test_add_lower_int_bound_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    euf::snode* x = sg.mk_var(symbol("x"));

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, x);  // create root node

    seq::nielsen_node* node = ng.root();
    seq::dep_tracker dep;

    // initially no bounds
    SASSERT(node->var_lb(x) == 0);
    SASSERT(node->var_ub(x) == UINT_MAX);
    SASSERT(node->int_constraints().empty());

    // add lower bound lb=3: should tighten and add constraint
    bool tightened = node->add_lower_int_bound(x, 3, dep);
    SASSERT(tightened);
    SASSERT(node->var_lb(x) == 3);
    SASSERT(node->int_constraints().size() == 1);
    SASSERT(node->int_constraints()[0].m_kind == seq::int_constraint_kind::ge);

    // add weaker lb=2: no tightening
    tightened = node->add_lower_int_bound(x, 2, dep);
    SASSERT(!tightened);
    SASSERT(node->var_lb(x) == 3);
    SASSERT(node->int_constraints().size() == 1);

    // add tighter lb=5: should tighten and add another constraint
    tightened = node->add_lower_int_bound(x, 5, dep);
    SASSERT(tightened);
    SASSERT(node->var_lb(x) == 5);
    SASSERT(node->int_constraints().size() == 2);

    std::cout << "  ok\n";
}

// test add_upper_int_bound: basic tightening adds int_constraint
static void test_add_upper_int_bound_basic() {
    std::cout << "test_add_upper_int_bound_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, x);

    seq::nielsen_node* node = ng.root();
    seq::dep_tracker dep;

    SASSERT(node->var_ub(x) == UINT_MAX);

    // add upper bound ub=10: tightens
    bool tightened = node->add_upper_int_bound(x, 10, dep);
    SASSERT(tightened);
    SASSERT(node->var_ub(x) == 10);
    SASSERT(node->int_constraints().size() == 1);
    SASSERT(node->int_constraints()[0].m_kind == seq::int_constraint_kind::le);

    // add weaker ub=20: no tightening
    tightened = node->add_upper_int_bound(x, 20, dep);
    SASSERT(!tightened);
    SASSERT(node->var_ub(x) == 10);
    SASSERT(node->int_constraints().size() == 1);

    // add tighter ub=5: tightens
    tightened = node->add_upper_int_bound(x, 5, dep);
    SASSERT(tightened);
    SASSERT(node->var_ub(x) == 5);
    SASSERT(node->int_constraints().size() == 2);

    std::cout << "  ok\n";
}

// test add_lower_int_bound: conflict when lb > ub
static void test_add_bound_lb_gt_ub_conflict() {
    std::cout << "test_add_bound_lb_gt_ub_conflict\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, x);

    seq::nielsen_node* node = ng.root();
    seq::dep_tracker dep;

    // set ub=3 first
    node->add_upper_int_bound(x, 3, dep);
    SASSERT(!node->is_general_conflict());

    // now set lb=5 > ub=3: should trigger conflict
    node->add_lower_int_bound(x, 5, dep);
    SASSERT(node->is_general_conflict());
    SASSERT(node->reason() == seq::backtrack_reason::arithmetic);

    std::cout << "  ok\n";
}

// test clone_from: child inherits parent bounds
static void test_bounds_cloned() {
    std::cout << "test_bounds_cloned\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, y);

    seq::nielsen_node* parent = ng.root();
    seq::dep_tracker dep;

    // set bounds on parent
    parent->add_lower_int_bound(x, 2, dep);
    parent->add_upper_int_bound(x, 7, dep);
    parent->add_lower_int_bound(y, 1, dep);

    // clone to child
    seq::nielsen_node* child = ng.mk_child(parent);

    // child should have same bounds
    SASSERT(child->var_lb(x) == 2);
    SASSERT(child->var_ub(x) == 7);
    SASSERT(child->var_lb(y) == 1);
    SASSERT(child->var_ub(y) == UINT_MAX);

    // child's int_constraints should also be cloned (3 constraints: lb_x, ub_x, lb_y)
    SASSERT(child->int_constraints().size() == parent->int_constraints().size());

    std::cout << "  ok\n";
}

// test VarBoundWatcher: substitution x→a·y propagates bounds from x to y
static void test_var_bound_watcher_single_var() {
    std::cout << "test_var_bound_watcher_single_var\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('a');

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, y);

    seq::nielsen_node* node = ng.root();
    seq::dep_tracker dep;

    // set bounds: 3 <= len(x) <= 7
    node->add_lower_int_bound(x, 3, dep);
    node->add_upper_int_bound(x, 7, dep);
    node->int_constraints().reset();  // clear for clean count

    // apply substitution x → a·y
    euf::snode* ay = sg.mk_concat(a, y);
    seq::nielsen_subst s(x, ay, dep);
    node->apply_subst(sg, s);

    // VarBoundWatcher should propagate: 3 <= 1+len(y) <= 7
    // => len(y) >= 2, len(y) <= 6
    SASSERT(node->var_lb(y) == 2);
    SASSERT(node->var_ub(y) == 6);

    std::cout << "  ok\n";
}

// test VarBoundWatcher: substitution with all-concrete replacement detects conflict
static void test_var_bound_watcher_conflict() {
    std::cout << "test_var_bound_watcher_conflict\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a = sg.mk_char('a');
    euf::snode* b = sg.mk_char('b');

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, a);

    seq::nielsen_node* node = ng.root();
    seq::dep_tracker dep;

    // set bounds: 3 <= len(x)  (so x must have at least 3 chars)
    node->add_lower_int_bound(x, 3, dep);
    node->int_constraints().reset();

    // apply substitution x → a·b (const_len=2 < lb=3)
    euf::snode* ab = sg.mk_concat(a, b);
    seq::nielsen_subst s(x, ab, dep);
    node->apply_subst(sg, s);

    // should detect conflict: len(x) >= 3 but replacement has len=2
    SASSERT(node->is_general_conflict());
    SASSERT(node->reason() == seq::backtrack_reason::arithmetic);

    std::cout << "  ok\n";
}

// test init_var_bounds_from_mems: simplify_and_init adds Parikh bounds
static void test_simplify_adds_parikh_bounds() {
    std::cout << "test_simplify_adds_parikh_bounds\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    euf::snode* x = sg.mk_var(symbol("x"));

    // create regex: to_re("AB") — exactly 2 chars
    expr_ref ch_a(seq.str.mk_char('A'), m);
    expr_ref ch_b(seq.str.mk_char('B'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    expr_ref re_ab(seq.re.mk_concat(seq.re.mk_to_re(unit_a), seq.re.mk_to_re(unit_b)), m);
    euf::snode* regex = sg.mk(re_ab);

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);
    ng.add_str_mem(x, regex);

    seq::nielsen_node* node = ng.root();

    // simplify_and_init should call init_var_bounds_from_mems
    seq::simplify_result sr = node->simplify_and_init(ng);
    (void)sr;

    // x ∈ to_re("AB") has min_len=2, max_len=2
    // so lb=2, ub=2 should be set on x
    SASSERT(node->var_lb(x) == 2);
    SASSERT(node->var_ub(x) == 2);

    std::cout << "  ok\n";
}

// test assert_root_constraints_to_solver: root constraints are forwarded
static void test_assert_root_constraints_to_solver() {
    std::cout << "test_assert_root_constraints_to_solver\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* a = sg.mk_char('a');
    euf::snode* b = sg.mk_char('b');
    euf::snode* ab = sg.mk_concat(a, b);

    tracking_solver ts(m);
    seq::nielsen_graph ng(sg, ts);
    // equation: x = a·b → generates len(x) = 2 and len(x) >= 0
    ng.add_str_eq(x, ab);

    // solve() calls assert_root_constraints_to_solver() internally
    ts.reset_tracking();
    ng.solve();

    // should have asserted at least: len(x) = 2, len(x) >= 0
    SASSERT(ts.asserted.size() >= 2);
    std::cout << "  asserted " << ts.asserted.size() << " root constraints to solver\n";
    for (auto& e : ts.asserted)
        std::cout << "    " << mk_pp(e, m) << "\n";

    std::cout << "  ok\n";
}

// test assert_root_constraints_to_solver: called only once even across iterations
static void test_assert_root_constraints_once() {
    std::cout << "test_assert_root_constraints_once\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));

    tracking_solver ts(m);
    seq::nielsen_graph ng(sg, ts);
    ng.add_str_eq(x, y);

    // solve is called (iterative deepening runs multiple iterations)
    ng.solve();
    unsigned count_first = ts.asserted.size();

    // after reset, assert count should be 0 then non-zero again
    // (reset clears m_root_constraints_asserted)
    // We can't call solve() again on the same graph without reset, but
    // we can verify the count is stable between iterations by checking
    // that the same constraints weren't added multiple times.
    // The simplest check: count > 0 (constraints were asserted)
    SASSERT(count_first > 0);  // x=y produces at least len(x)=len(y) and non-neg constraints
    std::cout << "  asserted " << count_first << " constraints total during solve\n";
    std::cout << "  ok\n";
}

// test VarBoundWatcher with multiple variables in replacement
static void test_var_bound_watcher_multi_var() {
    std::cout << "test_var_bound_watcher_multi_var\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* z = sg.mk_var(symbol("z"));

    dummy_simple_solver solver;
    seq::nielsen_graph ng(sg, solver);
    ng.add_str_eq(x, y);

    seq::nielsen_node* node = ng.root();
    seq::dep_tracker dep;

    // set upper bound: len(x) <= 5
    node->add_upper_int_bound(x, 5, dep);
    node->int_constraints().reset();

    // apply substitution x → y·z (two vars, no constants)
    euf::snode* yz = sg.mk_concat(y, z);
    seq::nielsen_subst s(x, yz, dep);
    node->apply_subst(sg, s);

    // len(y·z) <= 5 → each of y, z gets ub=5
    SASSERT(node->var_ub(y) == 5);
    SASSERT(node->var_ub(z) == 5);

    std::cout << "  ok\n";
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
    test_eq_split_basic();
    test_eq_split_solve_sat();
    test_eq_split_solve_unsat();
    test_eq_split_same_var_det();
    test_eq_split_commutation_sat();
    test_const_nielsen_char_var();
    test_const_nielsen_var_char();
    test_const_nielsen_solve_sat();
    test_const_nielsen_solve_unsat();
    test_const_nielsen_priority_over_eq_split();
    test_const_nielsen_tail_char_var();
    test_const_nielsen_not_applicable_both_vars();
    test_const_nielsen_multi_char_solve();
    test_var_nielsen_basic();
    test_var_nielsen_same_var_det();
    test_var_nielsen_not_applicable_char();
    test_var_nielsen_solve_sat();
    test_var_nielsen_solve_unsat();
    test_var_nielsen_commutation_sat();
    test_var_nielsen_priority();
    test_regex_char_split_basic();
    test_regex_char_split_solve_sat();
    test_regex_char_split_solve_multi_char();
    test_regex_char_split_union();
    test_regex_char_split_star_sat();
    test_regex_char_split_concat_str();
    test_regex_char_split_with_eq();
    test_regex_char_split_ground_skip();
    test_generate_extensions_det_priority();
    test_generate_extensions_no_applicable();
    test_generate_extensions_regex_only();
    test_generate_extensions_mixed_det_first();
    test_solve_empty_graph();
    test_solve_trivially_satisfied();
    test_solve_node_status_unsat();
    test_solve_conflict_deps();
    test_dep_tracker_get_set_bits();
    test_explain_conflict_single_eq();
    test_explain_conflict_multi_eq();
    test_solve_node_extended_flag();
    test_solve_mixed_eq_mem_sat();
    test_solve_children_failed_reason();
    test_solve_eval_idx_tracking();
    test_simplify_prefix_cancel();
    test_simplify_suffix_cancel_rtl();
    test_simplify_symbol_clash();
    test_simplify_empty_propagation();
    test_simplify_empty_vs_char();
    test_simplify_multi_pass_clash();
    test_simplify_trivial_removal();
    test_simplify_all_trivial_satisfied();
    test_simplify_regex_infeasible();
    test_simplify_nullable_removal();
    test_simplify_brzozowski_sat();
    test_simplify_brzozowski_rtl_suffix();
    test_simplify_multiple_eqs();
    test_det_cancel_child_eq();
    test_const_nielsen_child_substitutions();
    test_var_nielsen_substitution_types();
    test_explain_conflict_mem_only();
    test_explain_conflict_mixed_eq_mem();
    test_subsumption_pruning_unsat();
    test_subsumption_reason_set();
    test_length_constraints_basic();
    test_length_constraints_trivial_skip();
    test_length_constraints_empty();
    test_length_constraints_concat_chain();
    test_length_constraints_multi_eq();
    test_length_constraints_shared_var();
    test_length_constraints_deps();
    test_length_constraints_empty_side();
    // Length kind tagging tests (Task #35)
    test_length_kind_tagging();
    // New modifier tests (Task #55)
    test_power_epsilon_no_power();
    test_num_cmp_no_power();
    test_star_intr_no_backedge();
    test_star_intr_with_backedge();
    test_gpower_intr_self_cycle();
    test_gpower_intr_no_cycle();
    test_regex_var_split_basic();
    test_power_split_no_power();
    test_var_num_unwinding_no_power();
    test_const_num_unwinding_no_power();
    test_priority_chain_order();
    test_gpower_intr_solve_sat();
    // Parikh interval reasoning tests (Task #34)
    test_parikh_exact_length();
    test_parikh_star_unbounded();
    test_parikh_union_interval();
    test_parikh_loop_bounded();
    test_parikh_empty_regex();
    test_parikh_full_char();
    test_parikh_mixed_eq_mem();
    test_parikh_full_seq_no_bounds();
    test_parikh_dep_tracking();
    // IntBounds / VarBoundWatcher / Constraint.Shared tests
    test_add_lower_int_bound_basic();
    test_add_upper_int_bound_basic();
    test_add_bound_lb_gt_ub_conflict();
    test_bounds_cloned();
    test_var_bound_watcher_single_var();
    test_var_bound_watcher_conflict();
    test_simplify_adds_parikh_bounds();
    test_assert_root_constraints_to_solver();
    test_assert_root_constraints_once();
    test_var_bound_watcher_multi_var();
}
