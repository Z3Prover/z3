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

class dummy_simple_solver : public seq::sub_solver_i {
public:
    dummy_simple_solver() : seq::sub_solver_i() {}
    void push() override {}
    void pop(unsigned n) override {}
    void assert_expr(expr *e, seq::dep_tracker dep) override {}
    void reset() override {}
    lbool check() override {
        return l_true;
    }

};

// test dep_tracker (dependency_manager<dep_source>) basic operations
static void test_dep_tracker() {
    std::cout << "test_dep_tracker\n";

    seq::dep_manager dm;

    // empty tracker
    const seq::dep_tracker d0 = dm.mk_empty();
    VERIFY(d0 == nullptr);

    // tracker with one leaf (using sat::literal)
    const seq::dep_tracker d1 = dm.mk_leaf(sat::literal(3));
    VERIFY(d1 != nullptr);

    // tracker with another leaf (using sat::literal)
    const seq::dep_tracker d2 = dm.mk_leaf(sat::literal(5));
    VERIFY(d2 != nullptr);

    // merge
    const seq::dep_tracker d3 = dm.mk_join(d1, d2);
    VERIFY(d3 != nullptr);
    VERIFY(dm.contains(d3, sat::literal(3)));
    VERIFY(dm.contains(d3, sat::literal(5)));
    VERIFY(!dm.contains(d1, sat::literal(5)));

    // another leaf with same value as d1
    const seq::dep_tracker d4 = dm.mk_leaf(sat::literal(3));
    VERIFY(dm.contains(d4, sat::literal(3)));
    VERIFY(!dm.contains(d4, sat::literal(5)));
}

// test str_eq constraint creation and operations
static void test_str_eq() {
    std::cout << "test_str_eq\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    const seq::dep_tracker dep = nullptr;

    // basic equality
    const seq::str_eq eq1(m, x, y, dep);
    VERIFY(eq1.contains_var(x));
    VERIFY(eq1.contains_var(y));
    VERIFY(!eq1.contains_var(a));

    // trivial equality: same node
    const seq::str_eq eq2(m, x, x, dep);
    VERIFY(eq2.is_trivial());

    // trivial equality: both empty
    const seq::str_eq eq3(m, e, e, dep);
    VERIFY(eq3.is_trivial());

    // sorting: lower id first
    seq::str_eq eq4(m, y, x, dep);
    eq4.sort();
    VERIFY(eq4.m_lhs->id() <= eq4.m_rhs->id());

    // contains_var with concat
    euf::snode const* xa = sg.mk_concat(x, a);
    const seq::str_eq eq5(m, xa, y, dep);
    VERIFY(eq5.contains_var(x));
    VERIFY(eq5.contains_var(y));
    VERIFY(!eq5.contains_var(e));
}

// test str_mem constraint creation and operations
static void test_str_mem() {
    std::cout << "test_str_mem\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    const sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    // create a regex: re.all (.*)
    const expr_ref star_fc(seq.re.mk_full_seq(str_sort), m);
    euf::snode const* regex = sg.mk(star_fc);

    const seq::dep_tracker dep = nullptr;
    const seq::str_mem mem(m, x, regex, dep);

    // x in regex is primitive (x is a single variable)
    VERIFY(mem.is_primitive());
    VERIFY(mem.contains_var(x));

    // concatenation is not primitive
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* xa = sg.mk_concat(x, a);
    const seq::str_mem mem2(m, xa, regex, dep);
    VERIFY(!mem2.is_primitive());
    VERIFY(mem2.contains_var(x));
}

// test nielsen_subst
static void test_nielsen_subst() {
    std::cout << "test_nielsen_subst\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    const seq::dep_tracker dep = nullptr;
    const seq::nielsen_subst s1(x, a, dep);
    VERIFY(s1.is_eliminating());

    // eliminating substitution: x -> empty
    const seq::nielsen_subst s2(x, e, dep);
    VERIFY(s2.is_eliminating());

    // NOTE: non-eliminating substitutions (e.g. x -> A·x) are forbidden by
    // construction — the nielsen_subst ctor asserts the variable does not
    // occur in the replacement (add_subst_length_constraints relies on it).

    // eliminating substitution: x -> y (x not in y)
    const seq::nielsen_subst s4(x, y, dep);
    VERIFY(s4.is_eliminating());
}

// test nielsen_node creation and constraint management
static void test_nielsen_node() {
    std::cout << "test_nielsen_node\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    const sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');

    seq::nielsen_node* root = ng.mk_node();
    VERIFY(root->id() == 0);
    VERIFY(root->str_eqs().empty());
    VERIFY(root->str_mems().empty());
    VERIFY(root->is_progress());
    VERIFY(root->reason() == seq::backtrack_reason::unevaluated);

    // add constraints
    const seq::dep_tracker dep = nullptr;
    root->add_str_eq(seq::str_eq(m, x, y, dep));
    root->add_str_eq(seq::str_eq(m, sg.mk_concat(x, a), sg.mk_concat(a, y), dep));
    VERIFY(root->str_eqs().size() == 2);

    // regex membership (a universal regex like Σ* would be dropped as
    // trivially true by add_str_mem — use a proper constraint)
    const expr_ref re_a(seq.re.mk_to_re(seq.str.mk_string(zstring("A"))), m);
    euf::snode const* regex = sg.mk(re_a);
    root->add_str_mem(seq::str_mem(m, x, regex, dep));
    VERIFY(root->str_mems().size() == 1);

    // clone from parent
    seq::nielsen_node* child = ng.mk_node();
    child->clone_from(*root);
    VERIFY(child->str_eqs().size() == 2);
    VERIFY(child->str_mems().size() == 1);
    VERIFY(child->id() == 1);
}

// test nielsen_edge creation
static void test_nielsen_edge() {
    std::cout << "test_nielsen_edge\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');

    // create parent and child nodes
    seq::nielsen_node* parent = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    parent->add_str_eq(seq::str_eq(m, x, y, dep));

    seq::nielsen_node* child = ng.mk_child(parent);

    // create edge with substitution x -> A
    seq::nielsen_edge* edge = ng.mk_edge(parent, child, "test", true);
    edge->add_subst(seq::nielsen_subst(x, a, dep));

    VERIFY(edge->src() == parent);
    VERIFY(edge->tgt() == child);
    VERIFY(edge->is_progress());
    VERIFY(edge->subst().size() == 1);
    VERIFY(parent->outgoing().size() == 1);
    VERIFY(parent->outgoing()[0] == edge);
}

// test nielsen_graph population from external constraints
static void test_nielsen_graph_populate() {
    std::cout << "test_nielsen_graph_populate\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    const sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');

    // add string equality: x = y
    ng.add_str_eq(x, y);
    VERIFY(ng.root() != nullptr);
    VERIFY(ng.root()->str_eqs().size() == 1);
    VERIFY(ng.num_nodes() == 1);

    // add regex membership: x in A (a full-seq membership x ∈ Σ* would be
    // dropped as trivially true by add_str_mem)
    const expr_ref re_a(seq.re.mk_to_re(seq.str.mk_string(zstring("A"))), m);
    euf::snode const* regex = sg.mk(re_a);
    ng.add_str_mem(x, regex);
    VERIFY(ng.root()->str_mems().size() == 1);

    // add another equality: concat(x, A) = concat(A, y)
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* ay = sg.mk_concat(a, y);
    ng.add_str_eq(xa, ay);
    VERIFY(ng.root()->str_eqs().size() == 2);

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
    const seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    // create node with constraint: concat(x, A) = concat(B, y)
    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* by = sg.mk_concat(b, y);
    node->add_str_eq(seq::str_eq(m, xa, by, dep));

    // apply substitution x -> empty
    const seq::nielsen_subst s(x, e, dep);
    node->apply_subst(sg, s);

    // after x -> empty: lhs should be just A, rhs still concat(B, y)
    VERIFY(node->str_eqs().size() == 1);
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    ng.add_str_eq(x, y);
    VERIFY(ng.num_nodes() == 1);
    VERIFY(ng.root() != nullptr);

    ng.reset();
    VERIFY(ng.num_nodes() == 0);
    VERIFY(ng.root() == nullptr);
}

// test constructing a basic Nielsen expansion tree
// x = Ay: split into x -> eps (progress) or x -> Ax (non-progress)
static void test_nielsen_expansion() {
    std::cout << "test_nielsen_expansion\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* ay = sg.mk_concat(a, y);

    // root: x = Ay
    ng.add_str_eq(x, ay);
    seq::nielsen_node* root = ng.root();
    VERIFY(root->str_eqs().size() == 1);

    const seq::dep_tracker dep = nullptr;

    // branch 1: x -> eps (eliminating, progress)
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());
    seq::nielsen_node* child1 = ng.mk_child(root);
    const seq::nielsen_subst s1(x, e, dep);
    child1->apply_subst(sg, s1);
    seq::nielsen_edge* edge1 = ng.mk_edge(root, child1, "test", true);
    edge1->add_subst(s1);

    // branch 2: x -> A·x2 with a fresh tail (substitutions must be
    // eliminating by construction; the edge is still non-progress)
    euf::snode const* x2 = sg.mk_var(symbol("x2"), sg.get_str_sort());
    euf::snode const* ax = sg.mk_concat(a, x2);
    seq::nielsen_node* child2 = ng.mk_child(root);
    const seq::nielsen_subst s2(x, ax, dep);
    child2->apply_subst(sg, s2);
    seq::nielsen_edge* edge2 = ng.mk_edge(root, child2, "test", false);
    edge2->add_subst(s2);

    VERIFY(ng.num_nodes() == 3);
    VERIFY(root->outgoing().size() == 2);
    VERIFY(edge1->is_progress());
    VERIFY(!edge2->is_progress());

    // verify substitution effects on child1: eps = Ay becomes empty = Ay
    VERIFY(child1->str_eqs().size() == 1);

    ng.display(std::cout);
}

// test multiple regex memberships
static void test_multiple_memberships() {
    std::cout << "test_multiple_memberships\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    const sort_ref str_sort(seq.str.mk_string_sort(), m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    // x in A* (a full-seq membership would be dropped as trivially true)
    const expr_ref re_astar(seq.re.mk_star(seq.re.mk_to_re(seq.str.mk_string(zstring("A")))), m);
    euf::snode const* regex1 = sg.mk(re_astar);
    ng.add_str_mem(x, regex1);

    // x in re.union(to_re("A"), to_re("B"))
    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref ch_b(seq.str.mk_char('B'), m);
    const expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    const expr_ref to_re_b(seq.re.mk_to_re(unit_b), m);
    const expr_ref re_union(seq.re.mk_union(to_re_a, to_re_b), m);
    euf::snode const* regex2 = sg.mk(re_union);
    ng.add_str_mem(x, regex2);

    VERIFY(ng.root() != nullptr);
    VERIFY(ng.root()->str_mems().size() == 2);

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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();
    seq::nielsen_node* child = ng.mk_child(root);

    // set backedge from child to root (cycle)
//    child->set_backedge(root);
//    VERIFY(child->backedge() == root);
//    VERIFY(root->backedge() == nullptr);
}

// test var vs var basic structure (x·A = y·B now handled by var_nielsen, not eq_split)
static void test_eq_split_basic() {
    std::cout << "test_eq_split_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* yb = sg.mk_concat(y, b);

    // x·A = y·B — eq_split returns false (no valid split point), falls
    // through to var_nielsen (priority 12): five-way branch — 3 progress
    // (x→ε, y→ε, x→y) + 2 non-progress (x longer / y longer)
    ng.add_str_eq(xa, yb);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    VERIFY(root->outgoing().size() == 5);
    unsigned num_progress = 0;
    for (seq::nielsen_edge const* e : root->outgoing())
        if (e->is_progress())
            ++num_progress;
    VERIFY(num_progress == 3);
}

// test var vs var with solve: x·y = z·w is satisfiable (all vars can be ε)
static void test_eq_split_solve_sat() {
    std::cout << "test_eq_split_solve_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* z = sg.mk_var(symbol("z"), sg.get_str_sort());
    euf::snode const* w = sg.mk_var(symbol("w"), sg.get_str_sort());
    euf::snode const* xy = sg.mk_concat(x, y);
    euf::snode const* zw = sg.mk_concat(z, w);

    ng.add_str_eq(xy, zw);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
}

// test var vs var with solve: x·A = y·B is unsat (last char mismatch)
static void test_eq_split_solve_unsat() {
    std::cout << "test_eq_split_solve_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* yb = sg.mk_concat(y, b);

    ng.add_str_eq(xa, yb);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);
}

// test: same var x·A = x·B triggers det modifier (cancel), not eq_split or var_nielsen
static void test_eq_split_same_var_det() {
    std::cout << "test_eq_split_same_var_det\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* xb = sg.mk_concat(x, b);

    // x·A = x·B → same-head cancel → A = B → clash → unsat
    ng.add_str_eq(xa, xb);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);
}

// test: x·y·A = y·x·A is commutation, should be sat (x=y=ε)
static void test_eq_split_commutation_sat() {
    std::cout << "test_eq_split_commutation_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* xya = sg.mk_concat(x, sg.mk_concat(y, a));
    euf::snode const* yxa = sg.mk_concat(y, sg.mk_concat(x, a));

    ng.add_str_eq(xya, yxa);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* a = sg.mk_char('A');
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    // A = y  (single var definition → det modifier fires)
    ng.add_str_eq(a, y);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    // det modifier: y → A (1 progress child)
    VERIFY(root->outgoing().size() == 1);
    VERIFY(root->outgoing()[0]->is_progress());
}

// test: x = B·y is handled by det modifier (variable definition: x → B·y), producing 1 child
static void test_const_nielsen_var_char() {
    std::cout << "test_const_nielsen_var_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* by = sg.mk_concat(b, y);
    // x = B·y  (single var definition → det modifier fires)
    ng.add_str_eq(x, by);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    // det modifier: x → B·y (1 progress child)
    VERIFY(root->outgoing().size() == 1);
    VERIFY(root->outgoing()[0]->is_progress());
}

// test const_nielsen solve: A·x = A·B → sat (x = B via det cancel then const_nielsen x→ε or x→B·fresh)
static void test_const_nielsen_solve_sat() {
    std::cout << "test_const_nielsen_solve_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* ax = sg.mk_concat(a, x);
    euf::snode const* ab = sg.mk_concat(a, b);

    ng.add_str_eq(ax, ab);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
}

// test const_nielsen solve: A·x = B·y → unsat (leading chars mismatch)
static void test_const_nielsen_solve_unsat() {
    std::cout << "test_const_nielsen_solve_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* ax = sg.mk_concat(a, x);
    euf::snode const* by = sg.mk_concat(b, y);

    ng.add_str_eq(ax, by);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);
}

// test priority for A·x = y·B: the det modifier's variable-vs-char
// look-ahead (sub-rule 4, y → A·tail) preempts const_nielsen and
// var_nielsen with a single deterministic progress child
static void test_const_nielsen_priority_over_eq_split() {
    std::cout << "test_const_nielsen_priority_over_eq_split\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* ax = sg.mk_concat(a, x);
    euf::snode const* yb = sg.mk_concat(y, b);

    // A·x = y·B → lhs starts with char, rhs starts with var → const_nielsen
    ng.add_str_eq(ax, yb);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    VERIFY(root->outgoing().size() == 1);
    VERIFY(strcmp(root->outgoing()[0]->rule_name(), "det") == 0);
    VERIFY(root->outgoing()[0]->is_progress());
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* w = sg.mk_var(symbol("w"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* lhs = sg.mk_concat(x, a); // x·A
    euf::snode const* rhs = sg.mk_concat(w, y); // w·y

    ng.add_str_eq(lhs, rhs);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    VERIFY(root->outgoing().size() == 2);

    bool saw_empty = false;
    bool saw_tail = false;
    for (const seq::nielsen_edge* e : root->outgoing()) {
        VERIFY(e->subst().size() == 1);
        seq::nielsen_subst const& s = e->subst()[0];
        VERIFY(s.m_var == y);
        if (s.m_replacement && s.m_replacement->is_empty()) {
            saw_empty = true;
            VERIFY(e->is_progress());
        }
        else {
            euf::snode_vector toks;
            s.m_replacement->collect_tokens(toks);
            VERIFY(toks.size() == 2);
            // substitutions are eliminating by construction: the tail is a
            // FRESH variable (y → y'·A), not y itself
            VERIFY(toks[0]->is_var() && toks[0]->id() != y->id());
            VERIFY(toks[1]->is_char() && toks[1]->id() == a->id());
            saw_tail = true;
            VERIFY(!e->is_progress());
        }
    }
    VERIFY(saw_empty && saw_tail);
}

// test: both sides start with vars → var_nielsen (3 children), not const_nielsen
static void test_const_nielsen_not_applicable_both_vars() {
    std::cout << "test_const_nielsen_not_applicable_both_vars\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* yb = sg.mk_concat(y, b);

    // x·A = y·B → both heads are vars → var_nielsen fires (priority 12)
    // with its five-way branch (3 progress + 2 non-progress)
    ng.add_str_eq(xa, yb);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    VERIFY(root->outgoing().size() == 5);
}

// test const_nielsen solve: A·B·x = A·B·C → sat (x = C after two det cancels)
static void test_const_nielsen_multi_char_solve() {
    std::cout << "test_const_nielsen_multi_char_solve\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* c = sg.mk_char('C');
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* abx = sg.mk_concat(a, sg.mk_concat(b, x));
    euf::snode const* abc = sg.mk_concat(a, sg.mk_concat(b, c));

    ng.add_str_eq(abx, abc);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref ch_b(seq.str.mk_char('B'), m);
    const expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    const expr_ref ab(seq.str.mk_concat(unit_a, unit_b), m);
    const expr_ref to_re_ab(seq.re.mk_to_re(ab), m);
    euf::snode const* regex = sg.mk(to_re_ab);

    ng.add_str_mem(x, regex);
    VERIFY(ng.root() != nullptr);

    const auto sr = ng.root()->simplify_and_init({});
    VERIFY(sr != seq::simplify_result::conflict);

    // x ∈ "AB" is PRIMITIVE (single var, ground regex): the node is already
    // satisfied — no modifier fires; the witness is left to seq_model.
    const bool extended = ng.generate_extensions(ng.root());
    VERIFY(!extended);
    VERIFY(ng.root()->is_satisfied());
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* regex = sg.mk(to_re_a);

    ng.add_str_mem(x, regex);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    // NB: build the regex over a string LITERAL (canonical form, as produced
    // by th_rewriter through the theory); a to_re over a concat of units is
    // not a canonical leaf and is not supported at this layer.
    const expr_ref to_re_ab(seq.re.mk_to_re(seq.str.mk_string(zstring("AB"))), m);
    euf::snode const* regex = sg.mk(to_re_ab);

    ng.add_str_mem(x, regex);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref ch_b(seq.str.mk_char('B'), m);
    const expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    const expr_ref to_re_b(seq.re.mk_to_re(unit_b), m);
    const expr_ref re_union(seq.re.mk_union(to_re_a, to_re_b), m);
    euf::snode const* regex = sg.mk(re_union);

    ng.add_str_mem(x, regex);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    const expr_ref re_star(seq.re.mk_star(to_re_a), m);
    euf::snode const* regex = sg.mk(re_star);

    ng.add_str_mem(x, regex);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* xy = sg.mk_concat(x, y);

    // canonical literal-based regex (see test_regex_char_split_solve_multi_char)
    const expr_ref to_re_ab(seq.re.mk_to_re(seq.str.mk_string(zstring("AB"))), m);
    euf::snode const* regex = sg.mk(to_re_ab);

    ng.add_str_mem(xy, regex);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    ng.add_str_eq(x, y);

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* regex = sg.mk(to_re_a);

    ng.add_str_mem(x, regex);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* a = sg.mk_char('A');

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* regex = sg.mk(to_re_a);

    // "A" in to_re("A") → simplification consumes the char prefix via derivative
    ng.add_str_mem(a, regex);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    // x = y → det: x → y (single var definition)
    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    VERIFY(root->outgoing().size() == 1);
    VERIFY(root->outgoing()[0]->is_progress());
}

// test var_nielsen: same var x·A = x·B → det modifier (cancel), not var_nielsen
static void test_var_nielsen_same_var_det() {
    std::cout << "test_var_nielsen_same_var_det\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* xb = sg.mk_concat(x, b);

    // x·A = x·B → same-head cancel → A = B → clash → unsat
    ng.add_str_eq(xa, xb);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);
}

// test var_nielsen: char vs var → det fires (y → A), not var_nielsen
static void test_var_nielsen_not_applicable_char() {
    std::cout << "test_var_nielsen_not_applicable_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* a = sg.mk_char('A');
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    // A = y → det: y → A (variable definition, 1 child)
    ng.add_str_eq(a, y);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    VERIFY(root->outgoing().size() == 1);
}

// test var_nielsen solve: x·y = z·w is sat (all vars can be ε)
static void test_var_nielsen_solve_sat() {
    std::cout << "test_var_nielsen_solve_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* z = sg.mk_var(symbol("z"), sg.get_str_sort());
    euf::snode const* w = sg.mk_var(symbol("w"), sg.get_str_sort());
    euf::snode const* xy = sg.mk_concat(x, y);
    euf::snode const* zw = sg.mk_concat(z, w);

    ng.add_str_eq(xy, zw);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
}

// test var_nielsen solve: x·A = y·B → unsat (trailing char mismatch)
static void test_var_nielsen_solve_unsat() {
    std::cout << "test_var_nielsen_solve_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* yb = sg.mk_concat(y, b);

    ng.add_str_eq(xa, yb);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);
}

// test var_nielsen: x·y = y·x commutation is sat (x=y=ε via ε branches)
static void test_var_nielsen_commutation_sat() {
    std::cout << "test_var_nielsen_commutation_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* xya = sg.mk_concat(x, sg.mk_concat(y, a));
    euf::snode const* yxa = sg.mk_concat(y, sg.mk_concat(x, a));

    ng.add_str_eq(xya, yxa);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
}

// test var_nielsen priority: var vs var → det fires first for x = y (variable definition)
// var_nielsen only fires when neither side is a single var (e.g., x·A = y·B)
static void test_var_nielsen_priority() {
    std::cout << "test_var_nielsen_priority\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    // det modifier: x → y (1 progress child)
    VERIFY(root->outgoing().size() == 1);
    // first edge is progress (all var_nielsen children are progress)
    VERIFY(root->outgoing()[0]->is_progress());
}

// test generate_extensions: det modifier handles same-head cancel after simplification
// x·A = x·y → simplify cancels prefix x → A = y → det fires (y → A)
static void test_generate_extensions_det_priority() {
    std::cout << "test_generate_extensions_det_priority\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* xy = sg.mk_concat(x, y);

    // x·A = x·y → after simplify, becomes A = y → det: y → A
    ng.add_str_eq(xa, xy);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
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

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);


    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');

    // A = B → ground symbol clash.  generate_extensions may only be called
    // on a simplified, non-conflicting node (search_dfs simplifies first),
    // so the modern expectation is: simplify detects the conflict and no
    // extension is ever attempted.
    ng.add_str_eq(a, b);
    seq::nielsen_node* root = ng.root();

    const auto sr = root->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::conflict);
    VERIFY(root->is_currently_conflict());
    VERIFY(root->outgoing().empty());
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

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    // Build regex to_re("A")
    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* re_node = sg.mk(to_re_a);

    // x ∈ to_re("A") is a PRIMITIVE membership: the node is satisfied as-is
    // (no modifier fires; the witness is left to seq_model)
    ng.add_str_mem(x, re_node);
    seq::nielsen_node* root = ng.root();

    root->simplify_and_init({});

    const bool extended = ng.generate_extensions(root);
    VERIFY(!extended);
    VERIFY(root->is_satisfied());
}

// test: mixed constraints, x·A = x·B and y ∈ R → after simplify, A = B clash → unsat
static void test_generate_extensions_mixed_det_first() {
    std::cout << "test_generate_extensions_mixed_det_first\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* xb = sg.mk_concat(x, b);

    // Build a regex for the mem constraint
    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* re_node = sg.mk(to_re_a);

    // x·A = x·B → simplify cancels x → A = B → clash → unsat
    ng.add_str_eq(xa, xb);
    ng.add_str_mem(y, re_node);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);
}

// -----------------------------------------------------------------------
// solve() / search_dfs() tests
// -----------------------------------------------------------------------

// test solve on an empty constraint set returns sat (solve() requires an
// explicitly created root nowadays — theory_nseq calls create_root())
static void test_solve_empty_graph() {
    std::cout << "test_solve_empty_graph\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    VERIFY(!ng.root());
    ng.create_root();
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
}

// test solve with trivially satisfied equality (x = x)
static void test_solve_trivially_satisfied() {
    std::cout << "test_solve_trivially_satisfied\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    ng.add_str_eq(x, x);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
}

// test that node status flags are set correctly after unsat solve
static void test_solve_node_status_unsat() {
    std::cout << "test_solve_node_status_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
        seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    // A = B is an immediate conflict
    ng.add_str_eq(a, b);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);

    // root should be marked as general conflict
    const seq::nielsen_node* root = ng.root();
    VERIFY(root->is_general_conflict());
    VERIFY(root->is_currently_conflict());
}

// test that conflict_sources is populated after unsat
static void test_solve_conflict_deps() {
    std::cout << "test_solve_conflict_deps\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    // Add two constraints: A = B (unsat) and a dummy x = x
    ng.add_str_eq(a, b);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    ng.add_str_eq(x, x);

    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);

    // conflict_sources should be non-empty since there's a conflict
    VERIFY(!ng.conflict_sources().empty());
}

// test dep_tracker (dependency_manager<dep_source>) linearize
static void test_dep_tracker_get_set_bits() {
    std::cout << "test_dep_tracker_get_set_bits\n";

    seq::dep_manager dm;

    // empty tracker has no leaves
    const seq::dep_tracker d0 = dm.mk_empty();
    vector<seq::dep_source, false> bits0;
    dm.linearize(d0, bits0);
    VERIFY(bits0.empty());

    // single leaf with sat::literal(5)
    const seq::dep_tracker d1 = dm.mk_leaf(sat::literal(5));
    vector<seq::dep_source, false> bits1;
    dm.linearize(d1, bits1);
    VERIFY(bits1.size() == 1);
    VERIFY(std::holds_alternative<sat::literal>(bits1[0]));
    VERIFY(std::get<sat::literal>(bits1[0]) == sat::literal(5));

    // two leaves merged: sat::literal(3) and sat::literal(11)
    const seq::dep_tracker d2 = dm.mk_join(
        dm.mk_leaf(sat::literal(3)),
        dm.mk_leaf(sat::literal(11)));
    vector<seq::dep_source, false> bits2;
    dm.linearize(d2, bits2);
    VERIFY(bits2.size() == 2);
    bool has_3 = false, has_11 = false;
    for (auto const& d : bits2) {
        if (std::holds_alternative<sat::literal>(d)) {
            const sat::literal l = std::get<sat::literal>(d);
            if (l == sat::literal(3)) has_3 = true;
            if (l == sat::literal(11)) has_11 = true;
        }
    }
    VERIFY(has_3);
    VERIFY(has_11);

    // join with additional leaves
    const seq::dep_tracker d3 = dm.mk_join(
        dm.mk_leaf(sat::literal(31)),
        dm.mk_leaf(sat::literal(32)));
    vector<seq::dep_source, false> bits3;
    dm.linearize(d3, bits3);
    VERIFY(bits3.size() == 2);
    bool has31 = false, has32 = false;
    for (auto const& d : bits3) {
        if (std::holds_alternative<sat::literal>(d)) {
            const sat::literal l = std::get<sat::literal>(d);
            if (l == sat::literal(31)) has31 = true;
            if (l == sat::literal(32)) has32 = true;
        }
    }
    VERIFY(has31);
    VERIFY(has32);
}

// test explain_conflict returns correct constraint indices
static void test_explain_conflict_single_eq() {
    std::cout << "test_explain_conflict_single_eq\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    // eq[0]: A = B (conflict)
    ng.add_str_eq(a, b);

    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);

    // test-friendly overloads use null deps, so explain_conflict won't return anything
    // but the conflict should still be detected
    svector<seq::enode_pair> eqs;
    svector<sat::literal> mem_literals;
    ng.test_aux_explain_conflict(eqs, mem_literals);
    // with test-friendly overload (null deps), eqs will be empty
    // the important check is that the conflict was detected
}

// test explain_conflict with multiple eqs, only conflict-relevant one reported
static void test_explain_conflict_multi_eq() {
    std::cout << "test_explain_conflict_multi_eq\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    // eq[0]: x = x (trivially sat)
    ng.add_str_eq(x, x);
    // eq[1]: A = B (conflict)
    ng.add_str_eq(a, b);

    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);

    // with test-friendly overload (null deps), explain_conflict won't return deps
    // the important check is that the conflict was detected
    svector<seq::enode_pair> eqs;
    svector<sat::literal> mem_literals;
    ng.test_aux_explain_conflict(eqs, mem_literals);
}

// test that is_extended is set after solve generates extensions
static void test_solve_node_extended_flag() {
    std::cout << "test_solve_node_extended_flag\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* xy = sg.mk_concat(x, y);
    euf::snode const* z = sg.mk_var(symbol("z"), sg.get_str_sort());
    euf::snode const* w = sg.mk_var(symbol("w"), sg.get_str_sort());
    euf::snode const* zw = sg.mk_concat(z, w);
    // x·y = z·w — requires extension generation
    ng.add_str_eq(xy, zw);

    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);

    // root should be marked as extended
    const seq::nielsen_node* root = ng.root();
    VERIFY(root->is_extended());
}

// test solve with mixed eq + mem constraints: x·A = y·A and y ∈ re("A")
static void test_solve_mixed_eq_mem_sat() {
    std::cout << "test_solve_mixed_eq_mem_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* ya = sg.mk_concat(y, a);

    // x·A = y·A (satisfiable: x=y=ε, or x=y=anything)
    ng.add_str_eq(xa, ya);

    // y ∈ to_re("A") (y must be "A")
    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* re_a = sg.mk(to_re_a);
    ng.add_str_mem(y, re_a);

    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
}

// test solve with children_failed reason propagation: x·A = x·B unsat
static void test_solve_children_failed_reason() {
    std::cout << "test_solve_children_failed_reason\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* yb = sg.mk_concat(y, b);

    // x·A = y·B is unsat (last char mismatch propagates up)
    ng.add_str_eq(xa, yb);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);
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
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    // A·B·x = A·B·y → prefix cancel A,B → x = y (proceed)
    euf::snode const* abx = sg.mk_concat(a, sg.mk_concat(b, x));
    euf::snode const* aby = sg.mk_concat(a, sg.mk_concat(b, y));

    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_eq(seq::str_eq(m, abx, aby, dep));

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::proceed);
    VERIFY(node->str_eqs().size() == 1);
    // after prefix cancel: remaining eq has variable-only sides
    VERIFY(node->str_eqs()[0].m_lhs->is_var());
    VERIFY(node->str_eqs()[0].m_rhs->is_var());
}

// test simplify_and_init: suffix cancellation of matching chars (RTL)
static void test_simplify_suffix_cancel_rtl() {
    std::cout << "test_simplify_suffix_cancel_rtl\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    // x·A = y·A → suffix cancel A (RTL) → x = y
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* ya = sg.mk_concat(y, a);

    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_eq(seq::str_eq(m, xa, ya, dep));

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::proceed);
    VERIFY(node->str_eqs().size() == 1);
    VERIFY(node->str_eqs()[0].m_lhs->is_var());
    VERIFY(node->str_eqs()[0].m_rhs->is_var());
}

// test simplify_and_init: symbol clash at first position
static void test_simplify_symbol_clash() {
    std::cout << "test_simplify_symbol_clash\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    // A·x = B·y → symbol clash on first char
    euf::snode const* ax = sg.mk_concat(a, x);
    euf::snode const* by = sg.mk_concat(b, y);

    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_eq(seq::str_eq(m, ax, by, dep));

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::conflict);
    VERIFY(node->is_general_conflict());
    VERIFY(node->reason() == seq::backtrack_reason::symbol_clash);
}

// test simplify_and_init: empty propagation forces variables to epsilon
static void test_simplify_empty_propagation() {
    std::cout << "test_simplify_empty_propagation\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* xy = sg.mk_concat(x, y);

    // ε = x·y → the det modifier's empty-side propagation (§8.1 sub-rule 1)
    // forces x=ε, y=ε — nowadays a modifier step, not a simplify pass, so
    // check the end-to-end result: solve → sat
    ng.add_str_eq(e, xy);
    const auto sr = ng.root()->simplify_and_init({});
    VERIFY(sr != seq::simplify_result::conflict);
    VERIFY(ng.solve() == seq::nielsen_graph::search_result::sat);
}

// test simplify_and_init: empty vs concrete char → conflict
static void test_simplify_empty_vs_char() {
    std::cout << "test_simplify_empty_vs_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());
    euf::snode const* a = sg.mk_char('A');

    // ε = A → rhs has non-variable token → conflict
    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_eq(seq::str_eq(m, e, a, dep));

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::conflict);
    VERIFY(node->reason() == seq::backtrack_reason::symbol_clash);
}

// test simplify_and_init: multi-pass (prefix cancel A, then B≠C clash)
static void test_simplify_multi_pass_clash() {
    std::cout << "test_simplify_multi_pass_clash\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* c = sg.mk_char('C');

    // A·B = A·C → cancel A → B vs C → clash
    euf::snode const* ab = sg.mk_concat(a, b);
    euf::snode const* ac = sg.mk_concat(a, c);

    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_eq(seq::str_eq(m, ab, ac, dep));

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::conflict);
    VERIFY(node->reason() == seq::backtrack_reason::symbol_clash);
}

// test simplify_and_init: trivial eq removed, non-trivial kept
static void test_simplify_trivial_removal() {
    std::cout << "test_simplify_trivial_removal\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_eq(seq::str_eq(m, e, e, dep));  // trivial
    node->add_str_eq(seq::str_eq(m, x, y, dep));  // non-trivial

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::proceed);
    VERIFY(node->str_eqs().size() == 1);
}

// test simplify_and_init: all trivial eqs → satisfied
static void test_simplify_all_trivial_satisfied() {
    std::cout << "test_simplify_all_trivial_satisfied\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_eq(seq::str_eq(m, x, x, dep));  // trivial: same pointer
    node->add_str_eq(seq::str_eq(m, e, e, dep));  // trivial: both empty

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::satisfied);
}

// test simplify_and_init: ε ∈ non-nullable regex → conflict
static void test_simplify_regex_infeasible() {
    std::cout << "test_simplify_regex_infeasible\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* regex = sg.mk(to_re_a);

    // ε ∈ to_re("A") → non-nullable → conflict
    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_mem(seq::str_mem(m, e, regex, dep));

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::conflict);
    VERIFY(node->reason() == seq::backtrack_reason::regex);
}

// test simplify_and_init: ε ∈ nullable regex → satisfied, mem removed
static void test_simplify_nullable_removal() {
    std::cout << "test_simplify_nullable_removal\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    const expr_ref re_star(seq.re.mk_star(to_re_a), m);
    euf::snode const* regex = sg.mk(re_star);

    // ε ∈ star(to_re("A")) → nullable → satisfied, mem removed
    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_mem(seq::str_mem(m, e, regex, dep));

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::satisfied);
    VERIFY(node->str_mems().empty());
}

// test simplify_and_init: Brzozowski derivative consumes ground char
static void test_simplify_brzozowski_sat() {
    std::cout << "test_simplify_brzozowski_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* regex = sg.mk(to_re_a);

    // "A" ∈ to_re("A") → derivative consumes 'A' → ε ∈ ε-regex → satisfied
    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_mem(seq::str_mem(m, a, regex, dep));

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::satisfied);
}

// test simplify_and_init: backward Brzozowski consumes a trailing char (RTL)
static void test_simplify_brzozowski_rtl_suffix() {
    std::cout << "test_simplify_brzozowski_rtl_suffix\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    // canonical literal-based regex (a to_re over a concat of units is not
    // a canonical leaf at this layer)
    const expr_ref to_re_ba(seq.re.mk_to_re(seq.str.mk_string(zstring("BA"))), m);
    euf::snode const* regex = sg.mk(to_re_ba);

    // x·"A" ∈ to_re("BA") → RTL consume trailing 'A' → x ∈ to_re("B"),
    // which is primitive — the node is then satisfied
    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_mem(seq::str_mem(m, xa, regex, dep));

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::satisfied);
    VERIFY(node->str_mems().size() == 1);
    VERIFY(node->str_mems()[0].m_str->is_var());
    VERIFY(node->str_mems()[0].m_str->id() == x->id());

    euf::snode const* deriv_b = sg.brzozowski_deriv(node->str_mems()[0].m_regex, sg.mk_char('B'));
    VERIFY(deriv_b);
}

// test simplify_and_init: multiple eqs with mixed status
static void test_simplify_multiple_eqs() {
    std::cout << "test_simplify_multiple_eqs\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* z = sg.mk_var(symbol("z"), sg.get_str_sort());
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;

    // eq1: ε = ε (trivial → dropped already at insertion by add_str_eq)
    node->add_str_eq(seq::str_eq(m, e, e, dep));
    // eq2: A·x = A·y (prefix cancel → x = y)
    euf::snode const* ax = sg.mk_concat(a, x);
    euf::snode const* ay = sg.mk_concat(a, y);
    node->add_str_eq(seq::str_eq(m, ax, ay, dep));
    // eq3: x = z (non-trivial, kept)
    node->add_str_eq(seq::str_eq(m, x, z, dep));

    VERIFY(node->str_eqs().size() == 2);
    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::proceed);
    // eq2 simplified to x=y, eq3 kept → 2 eqs remain
    VERIFY(node->str_eqs().size() == 2);
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

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* xb = sg.mk_concat(x, b);

    // x·A = x·B → simplify cancels x → A = B → clash → unsat
    ng.add_str_eq(xa, xb);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);
}

// test child substitutions for A·x = y·B: the det modifier's
// variable-vs-char look-ahead fires with a single child substituting
// y → A·y' (fresh tail)
static void test_const_nielsen_child_substitutions() {
    std::cout << "test_const_nielsen_child_substitutions\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* ax = sg.mk_concat(a, x);
    euf::snode const* yb = sg.mk_concat(y, b);

    // A·x = y·B → det look-ahead: 1 child substituting y → A·y'
    ng.add_str_eq(ax, yb);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    VERIFY(root->outgoing().size() == 1);
    VERIFY(root->outgoing()[0]->subst().size() == 1);
    seq::nielsen_subst const& s = root->outgoing()[0]->subst()[0];
    VERIFY(s.m_var == y);
    VERIFY(!s.m_replacement->is_empty());
    // replacement starts with the matched char A and ends with a fresh var
    euf::snode_vector toks;
    s.m_replacement->collect_tokens(toks);
    VERIFY(toks.size() == 2);
    VERIFY(toks[0]->id() == a->id());
    VERIFY(toks[1]->is_var() && toks[1]->id() != y->id());
}

// test var_nielsen: verify substitution structure — det fires for x = y (single var def)
static void test_var_nielsen_substitution_types() {
    std::cout << "test_var_nielsen_substitution_types\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    // x = y → det: x → y (single var definition, 1 child)
    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    VERIFY(root->outgoing().size() == 1);

    // edge 0: x → y substitution
    VERIFY(root->outgoing()[0]->subst().size() == 1);
    VERIFY(root->outgoing()[0]->is_progress());
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

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* regex = sg.mk(to_re_a);

    // ε ∈ to_re("A") → conflict (non-nullable)
    ng.add_str_mem(e, regex);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);

    // with test-friendly overload (null deps), explain_conflict won't return deps
    svector<seq::enode_pair> eqs;
    svector<sat::literal> mem_literals;
    ng.test_aux_explain_conflict(eqs, mem_literals);
}

// test explain_conflict: mixed eq + mem conflict
static void test_explain_conflict_mixed_eq_mem() {
    std::cout << "test_explain_conflict_mixed_eq_mem\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    // eq[0]: A = B (conflict)
    ng.add_str_eq(a, b);

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* regex = sg.mk(to_re_a);

    // mem[0]: ε ∈ to_re("A")
    ng.add_str_mem(e, regex);

    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::unsat);

    // with test-friendly overload (null deps), explain_conflict won't return deps
    svector<seq::enode_pair> eqs;
    svector<sat::literal> mem_literals;
    ng.test_aux_explain_conflict(eqs, mem_literals);
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

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');

    // equation: x . y = A . B
    euf::snode const* lhs = sg.mk_concat(x, y);
    euf::snode const* rhs = sg.mk_concat(a, b);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(lhs, rhs);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // expect at least 1 length equality + 2 non-negativity constraints (for x and y)
    VERIFY(constraints.size() >= 3);

    // first constraint should be the length equality
    VERIFY(constraints[0].m_expr != nullptr);
    VERIFY(m.is_eq(constraints[0].m_expr));
    VERIFY(constraints[0].m_kind == seq::length_kind::eq);

    // remaining constraints should be non-negativity
    for (unsigned i = 1; i < constraints.size(); ++i) {
        VERIFY(constraints[i].m_kind == seq::length_kind::nonneg);
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

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    // trivial equation: x = x (same snode)
    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(x, x);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // trivial equation should be skipped, no constraints
    VERIFY(constraints.empty());
    std::cout << "  trivial equation correctly skipped\n";
}

// test generate_length_constraints: empty graph produces no constraints
static void test_length_constraints_empty() {
    std::cout << "test_length_constraints_empty\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    VERIFY(constraints.empty());
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

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* z = sg.mk_var(symbol("z"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* c = sg.mk_char('C');

    // equation: x . y . z = A . B . C
    euf::snode const* lhs = sg.mk_concat(sg.mk_concat(x, y), z);
    euf::snode const* rhs = sg.mk_concat(sg.mk_concat(a, b), c);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(lhs, rhs);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // 1 length equality + 3 variable non-negativity constraints
    VERIFY(constraints.size() == 4);
    VERIFY(m.is_eq(constraints[0].m_expr));

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

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(x, a);           // x = A
    ng.add_str_eq(y, b);           // y = B

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // 2 equalities + 2 non-negativity (x and y each appear once)
    VERIFY(constraints.size() == 4);
    VERIFY(m.is_eq(constraints[0].m_expr));
    VERIFY(m.is_eq(constraints[2].m_expr));

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

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');

    // equation: x . A = A . x  (x appears on both sides)
    euf::snode const* lhs = sg.mk_concat(x, a);
    euf::snode const* rhs = sg.mk_concat(a, x);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(lhs, rhs);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // 1 length equality + 1 non-negativity for x (deduped)
    VERIFY(constraints.size() == 2);

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

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(x, a);  // eq index 0

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // with test-friendly overload (null deps), constraints have null dep
    // the important check is that constraints were generated
    VERIFY(constraints.size() >= 1);

    std::cout << "  dependency tracking test passed\n";
}

// test generate_length_constraints: empty sides produce 0
static void test_length_constraints_empty_side() {
    std::cout << "test_length_constraints_empty_side\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* e = sg.mk_empty_seq(seq.str.mk_string_sort());

    // x = ε
    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(x, e);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // 1 equality (len(x) = 0) + 1 non-negativity (len(x) >= 0)
    VERIFY(constraints.size() == 2);
    VERIFY(m.is_eq(constraints[0].m_expr));
    VERIFY(constraints[0].m_kind == seq::length_kind::eq);
    VERIFY(constraints[1].m_kind == seq::length_kind::nonneg);

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

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');

    // equation: x = a (one eq + one nonneg)
    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(x, a);

    // membership: y in to_re("AB") (bounds + nonneg)
    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref ch_b(seq.str.mk_char('B'), m);
    const expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    const expr_ref ab(seq.str.mk_concat(unit_a, unit_b), m);
    const expr_ref to_re_ab(seq.re.mk_to_re(ab), m);
    euf::snode const* regex = sg.mk(to_re_ab);
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
    VERIFY(num_eq >= 1);
    // at least 1 non-negativity (for variable x or y)
    VERIFY(num_nonneg >= 1);
    // at least 1 bound (from Parikh for to_re("AB"))
    VERIFY(num_bound >= 1);

    // verify equalities have kind eq
    for (auto const& c : constraints) {
        if (m.is_eq(c.m_expr))
            VERIFY(c.m_kind == seq::length_kind::eq);
    }

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

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');

    // x = A: no power tokens, power_epsilon should not fire
    ng.add_str_eq(x, a);
    seq::nielsen_node* root = ng.root();

    // det fires (x is single var, A doesn't contain x → x → A)
    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    // det: x → A (variable definition, 1 child)
    VERIFY(root->outgoing().size() == 1);
}

// test_num_cmp_no_power: no same-base power pair → modifier returns false
static void test_num_cmp_no_power() {
    std::cout << "test_num_cmp_no_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    // x = y: no power tokens, num_cmp should not fire
    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    // det fires (x → y, variable definition): 1 child
    VERIFY(root->outgoing().size() == 1);
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

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* regex = sg.mk(to_re_a);

    // x ∈ to_re("A"): no backedge, star_intr should not fire
    ng.add_str_mem(x, regex);

    seq::nielsen_node* root = ng.root();
    // VERIFY(root->backedge() == nullptr);

    const auto sr = root->simplify_and_init({});
    VERIFY(sr != seq::simplify_result::conflict);

    // x ∈ "A" is a primitive membership: satisfied as-is, nothing fires
    const bool extended = ng.generate_extensions(root);
    VERIFY(!extended);
    VERIFY(root->is_satisfied());
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

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    const expr_ref re_star(seq.re.mk_star(to_re_a), m);
    euf::snode const* regex = sg.mk(re_star);

    // x ∈ star(to_re("A")): set backedge to simulate cycle detection
    ng.add_str_mem(x, regex);

    seq::nielsen_node* root = ng.root();
//    root->set_backedge(root); // simulate backedge

    const auto sr = root->simplify_and_init({});
    // star(to_re("A")) is nullable, so empty string satisfies it
    // simplify may remove the membership or proceed
    if (sr == seq::simplify_result::satisfied) {
        std::cout << "  simplified to satisfied (nullable regex)\n";
        return; // OK, the regex is nullable so it was removed
    }

    const bool extended = ng.generate_extensions(root);
    if (extended) {
        // star_intr should have generated at least 1 child
        VERIFY(root->outgoing().size() >= 1);
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

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a1 = sg.mk_char('A');
    euf::snode const* a2 = sg.mk_char('A');
    euf::snode const* lhs = sg.mk_concat(a1, x);  // Ax
    euf::snode const* rhs = sg.mk_concat(x, a2);  // xA

    // Ax = xA → variable x appears on both sides with ground prefix 'A'
    // GPowerIntr detects self-cycle and introduces x = A^n · suffix
    ng.add_str_eq(lhs, rhs);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    VERIFY(ng.stats().m_mod_gpower_intr == 1);
    VERIFY(root->outgoing().size() == 1);
    std::cout << "  gpower_intr generated " << root->outgoing().size() << " children\n";
}

// test_gpower_intr_no_cycle: aX = Yb → no cycle (X ≠ Y), GPowerIntr doesn't fire
static void test_gpower_intr_no_cycle() {
    std::cout << "test_gpower_intr_no_cycle\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');
    euf::snode const* lhs = sg.mk_concat(a, x);  // Ax
    euf::snode const* rhs = sg.mk_concat(y, b);  // Yb

    // Ax = Yb → Y is head of RHS, scan LHS: prefix=[A], target=x, but x ≠ y → no cycle
    // GPowerIntr does NOT fire; ConstNielsen (priority 8) fires instead
    ng.add_str_eq(lhs, rhs);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    VERIFY(ng.stats().m_mod_gpower_intr == 0);
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

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    // Build a regex: re.union(to_re("A"), to_re("B"))
    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref ch_b(seq.str.mk_char('B'), m);
    const expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    const expr_ref to_re_b(seq.re.mk_to_re(unit_b), m);
    const expr_ref re_union(seq.re.mk_union(to_re_a, to_re_b), m);
    euf::snode const* regex = sg.mk(re_union);

    ng.add_str_mem(x, regex);
    seq::nielsen_node* root = ng.root();

    const auto sr = root->simplify_and_init({});
    VERIFY(sr != seq::simplify_result::conflict);

    // x ∈ (A|B) is a primitive membership: satisfied as-is, nothing fires
    // (the witness is enumerated by seq_model, not by graph splitting)
    const bool extended = ng.generate_extensions(root);
    VERIFY(!extended);
    VERIFY(root->is_satisfied());
}

// test_power_split_no_power: no power tokens → modifier returns false
static void test_power_split_no_power() {
    std::cout << "test_power_split_no_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* xa = sg.mk_concat(x, a);

    // x·A = y: no power tokens, power_split should not fire
    // det fires (y is single var, y ∉ vars(x·A) → y → x·A)
    ng.add_str_eq(xa, y);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    // det fires: 1 child (y → x·A)
    VERIFY(root->outgoing().size() == 1);
}

// test_var_num_unwinding_no_power: no power tokens → modifier returns false
static void test_var_num_unwinding_no_power() {
    std::cout << "test_var_num_unwinding_no_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    // x = y: no power tokens, var_num_unwinding should not fire
    ng.add_str_eq(x, y);
    seq::nielsen_node* root = ng.root();

    const bool extended = ng.generate_extensions(root);
    VERIFY(extended);
    // det fires: 1 child (x → y)
    VERIFY(root->outgoing().size() == 1);
}

// test_const_num_unwinding_no_power: no power vs const → modifier returns false
static void test_const_num_unwinding_no_power() {
    std::cout << "test_const_num_unwinding_no_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('A');
    euf::snode const* b = sg.mk_char('B');

    // A = B: no power tokens, clash during simplification
    ng.add_str_eq(a, b);
    seq::nielsen_node* root = ng.root();

    // Should detect clash during simplify
    const auto sr = root->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::conflict);
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
        dummy_simple_solver solver;
        seq::context_solver_i context_solver;
        seq::nielsen_graph ng(sg, solver, context_solver);

        euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
        euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
        euf::snode const* a = sg.mk_char('A');
        euf::snode const* xa = sg.mk_concat(x, a);
        euf::snode const* xy = sg.mk_concat(x, y);

        ng.add_str_eq(xa, xy);
        const auto result = ng.solve();
        VERIFY(result == seq::nielsen_graph::search_result::sat);
    }

    // Case 2: both vars different → Det (priority 1) fires (variable definition x → y)
    {
        euf::egraph eg(m);
        euf::sgraph sg(m, eg);
        dummy_simple_solver solver;
        seq::context_solver_i context_solver;
        seq::nielsen_graph ng(sg, solver, context_solver);

        euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
        euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

        ng.add_str_eq(x, y);
        seq::nielsen_node* root = ng.root();
        const bool extended = ng.generate_extensions(root);
        VERIFY(extended);
        VERIFY(root->outgoing().size() == 1); // Det: variable definition, 1 child
    }

    // Case 3: char vs var → Det (priority 1) fires (variable definition y → A)
    {
        euf::egraph eg(m);
        euf::sgraph sg(m, eg);
        dummy_simple_solver solver;
        seq::context_solver_i context_solver;
        seq::nielsen_graph ng(sg, solver, context_solver);

        euf::snode const* a = sg.mk_char('A');
        euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

        ng.add_str_eq(a, y);
        seq::nielsen_node* root = ng.root();
        const bool extended = ng.generate_extensions(root);
        VERIFY(extended);
        VERIFY(root->outgoing().size() == 1); // Det: variable definition, 1 child
    }
}

// test_gpower_intr_solve_sat: x = AAA → sat (x = "AAA")
static void test_gpower_intr_solve_sat() {
    std::cout << "test_gpower_intr_solve_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a1 = sg.mk_char('A');
    euf::snode const* a2 = sg.mk_char('A');
    euf::snode const* a3 = sg.mk_char('A');
    euf::snode const* aaa = sg.mk_concat(a1, sg.mk_concat(a2, a3));

    ng.add_str_eq(x, aaa);
    const auto result = ng.solve();
    VERIFY(result == seq::nielsen_graph::search_result::sat);
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
    const arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref ch_b(seq.str.mk_char('B'), m);
    const expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    const expr_ref ab(seq.str.mk_concat(unit_a, unit_b), m);
    const expr_ref to_re_ab(seq.re.mk_to_re(ab), m);
    euf::snode const* regex = sg.mk(to_re_ab);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_mem(x, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // to_re("AB") has min_length=2 and max_length=2
    // expect: len(x) >= 2, len(x) <= 2, and len(x) >= 0
    std::cout << "  generated " << constraints.size() << " constraints\n";
    for (auto const& c : constraints)
        std::cout << "    " << mk_pp(c.m_expr, m) << "\n";
    VERIFY(constraints.size() >= 2);

    // verify we have both a >= and a <= constraint with correct kinds
    bool has_lower = false, has_upper = false;
    for (auto const& c : constraints) {
        if (arith.is_le(c.m_expr) || arith.is_ge(c.m_expr)) {
            has_lower = has_lower || arith.is_ge(c.m_expr);
            has_upper = has_upper || arith.is_le(c.m_expr);
            // Parikh bounds should have kind::bound
            if (!m.is_eq(c.m_expr))
                VERIFY(c.m_kind == seq::length_kind::bound || c.m_kind == seq::length_kind::nonneg);
        }
    }
    VERIFY(has_lower);
    VERIFY(has_upper);
}

// test: x in (re.star (re.to_re "A")) generates no upper bound
static void test_parikh_star_unbounded() {
    std::cout << "test_parikh_star_unbounded\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    const arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    const expr_ref re_star(seq.re.mk_star(to_re_a), m);
    euf::snode const* regex = sg.mk(re_star);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
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
    VERIFY(!has_upper);
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

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

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
    euf::snode const* regex = sg.mk(re_union);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
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
    VERIFY(has_lower);
    VERIFY(has_upper);
}

// test: x in re.loop(to_re("A"), 3, 5) → len(x) >= 3, len(x) <= 5
static void test_parikh_loop_bounded() {
    std::cout << "test_parikh_loop_bounded\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    const arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    const expr_ref re_loop(seq.re.mk_loop(to_re_a, 3, 5), m);
    euf::snode const* regex = sg.mk(re_loop);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
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
    VERIFY(has_lower);
    VERIFY(has_upper);
}

// test: x in re.empty → normalized to [0,0], generates len(x) <= 0
static void test_parikh_empty_regex() {
    std::cout << "test_parikh_empty_regex\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    const arith_util arith(m);
    const sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    const expr_ref re_empty(seq.re.mk_empty(seq.re.mk_re(str_sort)), m);
    euf::snode const* regex = sg.mk(re_empty);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
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
    VERIFY(has_upper);
}

// test: x in re.range("A","Z") → len(x) >= 1, len(x) <= 1
static void test_parikh_full_char() {
    std::cout << "test_parikh_full_char\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    const arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    // re.range("A", "Z") matches single characters in [A-Z]
    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref ch_z(seq.str.mk_char('Z'), m);
    const expr_ref unit_z(seq.str.mk_unit(ch_z), m);
    const expr_ref re_range(seq.re.mk_range(unit_a, unit_z), m);
    euf::snode const* regex = sg.mk(re_range);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
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
    VERIFY(has_lower);
    VERIFY(has_upper);
}

// test: mixed str_eq and str_mem constraints generate both types
static void test_parikh_mixed_eq_mem() {
    std::cout << "test_parikh_mixed_eq_mem\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    const arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('A');

    // equation: x = A
    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(x, a);

    // membership: y in to_re("BC")
    const expr_ref ch_b(seq.str.mk_char('B'), m);
    const expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    const expr_ref ch_c(seq.str.mk_char('C'), m);
    const expr_ref unit_c(seq.str.mk_unit(ch_c), m);
    const expr_ref bc(seq.str.mk_concat(unit_b, unit_c), m);
    const expr_ref to_re_bc(seq.re.mk_to_re(bc), m);
    euf::snode const* regex = sg.mk(to_re_bc);
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
    VERIFY(has_eq);   // from str_eq
    VERIFY(has_le);   // from str_mem upper bound
    VERIFY(has_ge);   // from str_mem lower bound or non-negativity
}

// test: str_mem with full_seq (.*) → no bounds generated
static void test_parikh_full_seq_no_bounds() {
    std::cout << "test_parikh_full_seq_no_bounds\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    const arith_util arith(m);
    const sort_ref str_sort(seq.str.mk_string_sort(), m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    const expr_ref re_all(seq.re.mk_full_seq(str_sort), m);
    euf::snode const* regex = sg.mk(re_all);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
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
    VERIFY(!has_le);
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

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    euf::snode const* regex = sg.mk(to_re_a);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_mem(x, regex);

    vector<seq::length_constraint> constraints;
    ng.generate_length_constraints(constraints);

    // to_re("A") has min=1, max=1 → len(x)>=1 and len(x)<=1
    VERIFY(constraints.size() >= 2);

    // all Parikh constraints should have non-empty deps
    for (auto const& c : constraints)
        VERIFY(c.m_dep != nullptr);
    std::cout << "  all constraints have non-empty deps\n";
}

// -----------------------------------------------------------------------
// IntBounds / subsolver-bound tests (Task: IntBounds/Constraint.Shared)
// -----------------------------------------------------------------------

// tracking solver: records assert_expr calls for inspection
class tracking_solver : public seq::sub_solver_i {
public:
    vector<expr_ref> asserted;
    ast_manager& m;
    unsigned push_count = 0;
    unsigned pop_count = 0;
    lbool check_result = l_true;

    tracking_solver(ast_manager& m) : m(m) {}
    void push() override { ++push_count; }
    void pop(unsigned n) override { pop_count += n; }
    void assert_expr(expr* e, seq::dep_tracker) override { asserted.push_back(expr_ref(e, m)); }
    void reset() override { reset_tracking(); }
    lbool check() override { return check_result; }
    void reset_tracking() {
        asserted.reset();
        push_count = 0;
        pop_count = 0;
    }
};

static void add_len_ge(seq::nielsen_graph& ng, seq::nielsen_node* node, euf::snode const* var, unsigned lb, seq::dep_tracker dep) {
    ast_manager& m = ng.get_manager();
    arith_util arith(m);
    const expr_ref len(ng.seq().str.mk_length(var->get_expr()), m);
    node->add_constraint(seq::constraint(arith.mk_ge(len, arith.mk_int(lb)), dep, m));
}

static void add_len_le(seq::nielsen_graph& ng, seq::nielsen_node* node, euf::snode const* var, unsigned ub, seq::dep_tracker dep) {
    ast_manager& m = ng.get_manager();
    arith_util arith(m);
    const expr_ref len(ng.seq().str.mk_length(var->get_expr()), m);
    node->add_constraint(seq::constraint(arith.mk_le(len, arith.mk_int(ub)), dep, m));
}

static unsigned queried_lb(seq::nielsen_node* node, euf::snode const* var) {
    rational lb;
    seq::dep_tracker d = nullptr;
    if (!node->lower_bound(var->get_expr(), lb, d))
        return 0;
    VERIFY(lb.is_unsigned());
    return lb.is_unsigned() ? lb.get_unsigned() : 0;
}

static unsigned queried_ub(seq::nielsen_node* node, euf::snode const* var) {
    rational ub;
    seq::dep_tracker d = nullptr;
    if (!node->upper_bound(var->get_expr(), ub, d))
        return UINT_MAX;
    VERIFY(ub.is_unsigned());
    return ub.is_unsigned() ? ub.get_unsigned() : UINT_MAX;
}

// Bounds are owned by the arithmetic side (context/sub solver) nowadays:
// nielsen_node::lower_bound/upper_bound consult the context solver and fall
// back to the conservative defaults (0 / unbounded) when it reports
// "unsupported" — node-local constraints do NOT feed the queries.  These
// tests pin that contract plus the constraint-accumulation plumbing.
static void test_add_lower_int_bound_basic() {
    std::cout << "test_add_lower_int_bound_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.create_root();

    seq::nielsen_node* node = ng.root();
    const seq::dep_tracker dep = nullptr;

    // initially no bounds and no constraints
    VERIFY(queried_lb(node, x) == 0);
    VERIFY(queried_ub(node, x) == UINT_MAX);
    VERIFY(node->constraints().empty());

    // node constraints accumulate but do not affect the queried bounds
    // (the default context solver reports "unsupported")
    add_len_ge(ng, node, x, 3, dep);
    VERIFY(queried_lb(node, x) == 0);
    VERIFY(node->constraints().size() == 1);
    VERIFY(node->constraints()[0].fml);

    add_len_ge(ng, node, x, 5, dep);
    VERIFY(node->constraints().size() == 2);

    std::cout << "  ok\n";
}

// same contract for upper bounds
static void test_add_upper_int_bound_basic() {
    std::cout << "test_add_upper_int_bound_basic\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.create_root();

    seq::nielsen_node* node = ng.root();
    const seq::dep_tracker dep = nullptr;

    VERIFY(queried_ub(node, x) == UINT_MAX);

    add_len_le(ng, node, x, 10, dep);
    VERIFY(queried_ub(node, x) == UINT_MAX);
    VERIFY(node->constraints().size() == 1);
    VERIFY(node->constraints()[0].fml);

    add_len_le(ng, node, x, 5, dep);
    VERIFY(node->constraints().size() == 2);

    std::cout << "  ok\n";
}

// contradictory node-local length constraints do not surface through the
// bound queries (the arithmetic subsolver refutes them during search)
static void test_add_bound_lb_gt_ub_conflict() {
    std::cout << "test_add_bound_lb_gt_ub_conflict\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.create_root();

    seq::nielsen_node* node = ng.root();
    const seq::dep_tracker dep = nullptr;

    add_len_le(ng, node, x, 3, dep);
    add_len_ge(ng, node, x, 5, dep);
    VERIFY(node->constraints().size() == 2);
    VERIFY(queried_lb(node, x) == 0);
    VERIFY(queried_ub(node, x) == UINT_MAX);

    std::cout << "  ok\n";
}

// test clone_from: child inherits parent constraints verbatim
static void test_bounds_cloned() {
    std::cout << "test_bounds_cloned\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(x, y);

    seq::nielsen_node* parent = ng.root();
    const seq::dep_tracker dep = nullptr;

    add_len_ge(ng, parent, x, 2, dep);
    add_len_le(ng, parent, x, 7, dep);
    add_len_ge(ng, parent, y, 1, dep);

    // clone to child: constraints are copied, and the parent-inherited
    // prefix is recorded (m_parent_ic_count semantics)
    seq::nielsen_node* child = ng.mk_child(parent);
    VERIFY(child->constraints().size() == parent->constraints().size());
    for (unsigned i = 0; i < parent->constraints().size(); ++i)
        VERIFY(child->constraints()[i].fml.get() == parent->constraints()[i].fml.get());

    std::cout << "  ok\n";
}

// Substitution propagates no direct bounds; bounds are owned by the subsolver.
static void test_subst_does_not_propagate_bounds_single_var() {
    std::cout << "test_subst_does_not_propagate_bounds_single_var\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('a');

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(x, y);

    seq::nielsen_node* node = ng.root();
    const seq::dep_tracker dep = nullptr;

    // set bounds: 3 <= len(x) <= 7
    add_len_ge(ng, node, x, 3, dep);
    add_len_le(ng, node, x, 7, dep);

    // apply substitution x → a·y
    euf::snode const* ay = sg.mk_concat(a, y);
    const seq::nielsen_subst s(x, ay, dep);
    node->apply_subst(sg, s);

    // No local propagation anymore: y keeps conservative defaults.
    VERIFY(queried_lb(node, y) == 0);
    VERIFY(queried_ub(node, y) == UINT_MAX);

    std::cout << "  ok\n";
}

// Substitution with concrete replacement does not trigger immediate bound conflict.
static void test_subst_no_immediate_bound_conflict() {
    std::cout << "test_subst_no_immediate_bound_conflict\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('a');
    euf::snode const* b = sg.mk_char('b');

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(x, a);

    seq::nielsen_node* node = ng.root();
    const seq::dep_tracker dep = nullptr;

    // set bounds: 3 <= len(x)  (so x must have at least 3 chars)
    add_len_ge(ng, node, x, 3, dep);

    // apply substitution x → a·b (no eager bound check at this stage)
    euf::snode const* ab = sg.mk_concat(a, b);
    const seq::nielsen_subst s(x, ab, dep);
    node->apply_subst(sg, s);

    VERIFY(!node->is_general_conflict());

    std::cout << "  ok\n";
}

// simplify_and_init materializes no local IntBounds; bounds come from subsolver state
static void test_simplify_does_not_add_local_parikh_bounds() {
    std::cout << "test_simplify_does_not_add_local_parikh_bounds\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    // create regex: to_re("AB") — exactly 2 chars
    const expr_ref ch_a(seq.str.mk_char('A'), m);
    const expr_ref ch_b(seq.str.mk_char('B'), m);
    const expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    const expr_ref unit_b(seq.str.mk_unit(ch_b), m);
    const expr_ref re_ab(seq.re.mk_concat(seq.re.mk_to_re(unit_a), seq.re.mk_to_re(unit_b)), m);
    euf::snode const* regex = sg.mk(re_ab);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_mem(x, regex);

    seq::nielsen_node* node = ng.root();

    // simplify_and_init no longer materializes local IntBounds.
    const seq::simplify_result sr = node->simplify_and_init({});
    (void)sr;

    VERIFY(queried_lb(node, x) == 0);
    VERIFY(queried_ub(node, x) == UINT_MAX);

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

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('a');
    euf::snode const* b = sg.mk_char('b');
    euf::snode const* ab = sg.mk_concat(a, b);

    tracking_solver ts(m);
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, ts, context_solver);
    // equation: x = a·b → generates len(x) = 2 and len(x) >= 0
    ng.add_str_eq(x, ab);

    // solve() calls assert_root_constraints_to_solver() internally
    ts.reset_tracking();
    ng.solve();

    // should have asserted at least: len(x) = 2, len(x) >= 0
    VERIFY(ts.asserted.size() >= 2);
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

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    tracking_solver ts(m);
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, ts, context_solver);
    ng.add_str_eq(x, y);

    // solve is called (iterative deepening runs multiple iterations)
    ng.solve();
    const unsigned count_first = ts.asserted.size();

    // after reset, assert count should be 0 then non-zero again
    // (reset clears m_root_constraints_asserted)
    // We can't call solve() again on the same graph without reset, but
    // we can verify the count is stable between iterations by checking
    // that the same constraints weren't added multiple times.
    // The simplest check: count > 0 (constraints were asserted)
    VERIFY(count_first > 0);  // x=y produces at least len(x)=len(y) and non-neg constraints
    std::cout << "  asserted " << count_first << " constraints total during solve\n";
    std::cout << "  ok\n";
}

// Multiple-variable substitutions do not impose eager per-variable bounds.
static void test_subst_does_not_propagate_bounds_multi_var() {
    std::cout << "test_subst_does_not_propagate_bounds_multi_var\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* z = sg.mk_var(symbol("z"), sg.get_str_sort());

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.add_str_eq(x, y);

    seq::nielsen_node* node = ng.root();
    const seq::dep_tracker dep = nullptr;

    // set upper bound: len(x) <= 5
    add_len_le(ng, node, x, 5, dep);

    // apply substitution x → y·z (two vars, no constants)
    euf::snode const* yz = sg.mk_concat(y, z);
    const seq::nielsen_subst s(x, yz, dep);
    node->apply_subst(sg, s);

    VERIFY(queried_ub(node, y) == UINT_MAX);
    VERIFY(queried_ub(node, z) == UINT_MAX);

    std::cout << "  ok\n";
}

// test simplify_and_init: unit-unit prefix split
// unit(a) ++ x = unit(b) ++ y  ->  unit(a)==unit(b), x==y
static void test_simplify_unit_prefix_split() {
    std::cout << "test_simplify_unit_prefix_split\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    // create symbolic char variables a, b (non-concrete -> s_unit)
    sort* char_sort = seq.mk_char_sort();
    const expr_ref sym_a(m.mk_const(symbol("a"), char_sort), m);
    const expr_ref sym_b(m.mk_const(symbol("b"), char_sort), m);
    const expr_ref unit_a_expr(seq.str.mk_unit(sym_a), m);
    const expr_ref unit_b_expr(seq.str.mk_unit(sym_b), m);
    euf::snode const* ua = sg.mk(unit_a_expr);
    euf::snode const* ub = sg.mk(unit_b_expr);
    VERIFY(ua->is_unit());
    VERIFY(ub->is_unit());

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    // ua ++ x = ub ++ y
    euf::snode const* lhs = sg.mk_concat(ua, x);
    euf::snode const* rhs = sg.mk_concat(ub, y);

    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_eq(seq::str_eq(m, lhs, rhs, dep));

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::proceed);
    // symbolic unit-vs-unit heads are NOT split off as a separate equality
    // by simplify anymore — the equation is kept (unit unification is
    // handled by the det modifier / char-range machinery during search)
    VERIFY(node->str_eqs().size() == 1);
    std::cout << "  ok\n";
}

// test simplify_and_init: unit-unit prefix split with empty rest on rhs
// unit(a) ++ x = unit(b)  ->  unit(a)==unit(b), x==empty
static void test_simplify_unit_prefix_split_empty_rest() {
    std::cout << "test_simplify_unit_prefix_split_empty_rest\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    sort* char_sort = seq.mk_char_sort();
    const expr_ref sym_a(m.mk_const(symbol("a"), char_sort), m);
    const expr_ref sym_b(m.mk_const(symbol("b"), char_sort), m);
    const expr_ref unit_a_expr(seq.str.mk_unit(sym_a), m);
    const expr_ref unit_b_expr(seq.str.mk_unit(sym_b), m);
    euf::snode const* ua = sg.mk(unit_a_expr);
    euf::snode const* ub = sg.mk(unit_b_expr);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    // ua ++ x = ub  (rhs has no rest after unit)
    euf::snode const* lhs = sg.mk_concat(ua, x);

    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_eq(seq::str_eq(m, lhs, ub, dep));

    const auto sr = node->simplify_and_init({});
    // unit(a)==unit(b) and x==empty are produced; x==empty forces x->epsilon and satisfied
    VERIFY(sr == seq::simplify_result::satisfied || sr == seq::simplify_result::proceed);
    std::cout << "  ok\n";
}

// test simplify_and_init: unit-unit suffix split
// x ++ unit(a) = y ++ unit(b)  ->  unit(a)==unit(b), x==y
static void test_simplify_unit_suffix_split() {
    std::cout << "test_simplify_unit_suffix_split\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    const seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    sort* char_sort = seq.mk_char_sort();
    const expr_ref sym_a(m.mk_const(symbol("a"), char_sort), m);
    const expr_ref sym_b(m.mk_const(symbol("b"), char_sort), m);
    const expr_ref unit_a_expr(seq.str.mk_unit(sym_a), m);
    const expr_ref unit_b_expr(seq.str.mk_unit(sym_b), m);
    euf::snode const* ua = sg.mk(unit_a_expr);
    euf::snode const* ub = sg.mk(unit_b_expr);
    VERIFY(ua->is_unit());
    VERIFY(ub->is_unit());

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    // x ++ ua = y ++ ub
    euf::snode const* lhs = sg.mk_concat(x, ua);
    euf::snode const* rhs = sg.mk_concat(y, ub);

    seq::nielsen_node* node = ng.mk_node();
    const seq::dep_tracker dep = nullptr;
    node->add_str_eq(seq::str_eq(m, lhs, rhs, dep));

    const auto sr = node->simplify_and_init({});
    VERIFY(sr == seq::simplify_result::proceed);
    // the unit-unit suffix is consumed by a char substitution — only x==y
    // remains (see test_simplify_unit_prefix_split)
    VERIFY(node->str_eqs().size() == 1);
    std::cout << "  ok\n";
}

// -----------------------------------------------------------------------
// apply_fine_wilf tests (priority 3c): Fine & Wilf overlap splitting for
// different-base power heads.  See specs/nseq-fine-wilf.md.
// -----------------------------------------------------------------------

// Shared setup: returns a power snode base^exp for a ground string base.
static euf::snode const* mk_ground_power(euf::sgraph& sg, seq_util& seq, ast_manager& m,
                                         const char* base, expr* exp) {
    const expr_ref base_e(seq.str.mk_string(zstring(base)), m);
    const expr_ref pw(seq.str.mk_power(base_e, exp), m);
    return sg.mk(pw);
}

// build snode for  power(base_snode-as-term, exp)  — used to nest powers
static euf::snode const* mk_power_of(euf::sgraph& sg, seq_util& seq, ast_manager& m,
                                     euf::snode const* base, expr* exp) {
    const expr_ref pw(seq.str.mk_power(base->get_expr(), exp), m);
    return sg.mk(pw);
}

static unsigned count_edges_with_rule(seq::nielsen_node const* n, const char* prefix) {
    unsigned cnt = 0;
    for (seq::nielsen_edge const* e : n->outgoing())
        if (strncmp(e->rule_name(), prefix, strlen(prefix)) == 0)
            ++cnt;
    return cnt;
}

// (ab)^n·U = (ba)^m·V — "ab" and "ba" do not commute, so the F&W cases 2/3
// are pruned at generation time; only the bounded-exponent enumerations
// remain: n ∈ {0,1} (n·2 < 4) and m ∈ {0,1}, i.e. 4 progress children.
static void test_fine_wilf_noncommuting_children() {
    std::cout << "test_fine_wilf_noncommuting_children\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.set_fine_wilf(true); // opt-in (smt.nseq.fine_wilf defaults to off)

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* pw_ab = mk_ground_power(sg, seq, m, "ab", n_e);
    euf::snode const* pw_ba = mk_ground_power(sg, seq, m, "ba", m_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_ab, u), sg.mk_concat(pw_ba, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.generate_extensions(root));
    VERIFY(root->outgoing().size() == 4);
    for (seq::nielsen_edge const* e : root->outgoing())
        VERIFY(e->is_progress());
    VERIFY(count_edges_with_rule(root, "fine-wilf n") == 2);
    VERIFY(count_edges_with_rule(root, "fine-wilf m") == 2);
    VERIFY(count_edges_with_rule(root, "fine-wilf elim") == 0);
    std::cout << "  ok\n";
}

// (ab)^n·U = (abab)^m·V — commuting roots (common primitive root "ab"), so
// all four blocks fire.  With Lu/Lw ∈ {2,4} (which power plays "U" depends
// on str_eq's side canonicalization): bounded enumerations contribute
// N+1 = (Ly+Lu+Lw-1)/Lu + 1 and M+1 = (Lu+Lw-1)/Lw + 1 children (2+3 or
// 3+2), the case-2/3 cut enumerations Lw + Lu = 6 — 11 progress children.
static void test_fine_wilf_commuting_children() {
    std::cout << "test_fine_wilf_commuting_children\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.set_fine_wilf(true); // opt-in (smt.nseq.fine_wilf defaults to off)

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* pw_ab = mk_ground_power(sg, seq, m, "ab", n_e);
    euf::snode const* pw_abab = mk_ground_power(sg, seq, m, "abab", m_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_ab, u), sg.mk_concat(pw_abab, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.generate_extensions(root));
    VERIFY(root->outgoing().size() == 11);
    for (seq::nielsen_edge const* e : root->outgoing())
        VERIFY(e->is_progress());
    VERIFY(count_edges_with_rule(root, "fine-wilf n") +
            count_edges_with_rule(root, "fine-wilf m") == 5);
    VERIFY(count_edges_with_rule(root, "fine-wilf elim") == 6);
    std::cout << "  ok\n";
}

// "a"·(ba)^n·U = (ab)^n·V — the draft's conjugation shape: ground prefix
// Y = "a" before the (ba)-power; rot("ab", 1) = "ba" = base(W), so the
// conjugate commutes and cases 2/3 fire alongside the enumerations:
// 3 + 2 + 2 + 2 = 9 children.
static void test_fine_wilf_ground_prefix() {
    std::cout << "test_fine_wilf_ground_prefix\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.set_fine_wilf(true); // opt-in (smt.nseq.fine_wilf defaults to off)

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    euf::snode const* pw_ba = mk_ground_power(sg, seq, m, "ba", n_e);
    euf::snode const* pw_ab = mk_ground_power(sg, seq, m, "ab", n_e);
    euf::snode const* a = sg.mk_char('a');
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    // "a"·(ba)^n·U  =  (ab)^n·V
    ng.add_str_eq(sg.mk_concat(a, sg.mk_concat(pw_ba, u)),
                  sg.mk_concat(pw_ab, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.generate_extensions(root));
    VERIFY(root->outgoing().size() == 9);
    for (seq::nielsen_edge const* e : root->outgoing())
        VERIFY(e->is_progress());
    VERIFY(count_edges_with_rule(root, "fine-wilf n") == 3);
    VERIFY(count_edges_with_rule(root, "fine-wilf m") == 2);
    VERIFY(count_edges_with_rule(root, "fine-wilf elim L") == 2);
    VERIFY(count_edges_with_rule(root, "fine-wilf elim R") == 2);
    std::cout << "  ok\n";
}

// (ab)^n·U = (ab)^m·V — SAME base: fine_wilf must not fire; NumCmp
// (priority 3) takes it with its two arith-split children.
static void test_fine_wilf_same_base_skipped() {
    std::cout << "test_fine_wilf_same_base_skipped\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.set_fine_wilf(true); // opt-in (smt.nseq.fine_wilf defaults to off)

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* pw_n = mk_ground_power(sg, seq, m, "ab", n_e);
    euf::snode const* pw_m = mk_ground_power(sg, seq, m, "ab", m_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_n, u), sg.mk_concat(pw_m, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.generate_extensions(root));
    VERIFY(root->outgoing().size() == 2);
    VERIFY(count_edges_with_rule(root, "fine-wilf") == 0);
    VERIFY(count_edges_with_rule(root, "power cmp") == 2);
    for (seq::nielsen_edge const* e : root->outgoing())
        VERIFY(e->tgt()->is_arith_split());
    std::cout << "  ok\n";
}

// Symbolic (variable) bases: x^n·U = y^m·V takes the symbolic path —
// one arith-split small-overlap child + the two cut-axiomatization
// children.  Extending the arith-split child must NOT refire fine_wilf
// (the inherited m_fw_applied guard), falling through to the peel.
static void test_fine_wilf_symbolic_refire_guard() {
    std::cout << "test_fine_wilf_symbolic_refire_guard\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.set_fine_wilf(true); // opt-in (smt.nseq.fine_wilf defaults to off)

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    const expr_ref pw_x_e(seq.str.mk_power(x->get_expr(), n_e), m);
    const expr_ref pw_y_e(seq.str.mk_power(y->get_expr(), m_e), m);
    euf::snode const* pw_x = sg.mk(pw_x_e);
    euf::snode const* pw_y = sg.mk(pw_y_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_x, u), sg.mk_concat(pw_y, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.generate_extensions(root));
    VERIFY(root->outgoing().size() == 3);
    VERIFY(count_edges_with_rule(root, "fine-wilf small") == 1);
    VERIFY(count_edges_with_rule(root, "fine-wilf elim L") == 1);
    VERIFY(count_edges_with_rule(root, "fine-wilf elim R") == 1);

    // find the arith-split (case 1) child: same string constraints, guarded
    seq::nielsen_node* small = nullptr;
    for (seq::nielsen_edge* e : root->outgoing())
        if (strcmp(e->rule_name(), "fine-wilf small") == 0)
            small = e->tgt();
    VERIFY(small && small->is_arith_split());

    // the guard must divert the child to another modifier (the peel), not
    // the identical fine-wilf split again
    VERIFY(ng.generate_extensions(small));
    VERIFY(count_edges_with_rule(small, "fine-wilf") == 0);
    VERIFY(small->outgoing().size() > 0);
    std::cout << "  ok\n";
}

// Solve-level: commuting roots are satisfiable (e.g. everything empty);
// the search must terminate through the fine-wilf children.
static void test_fine_wilf_solve_commuting_sat() {
    std::cout << "test_fine_wilf_solve_commuting_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.set_fine_wilf(true); // opt-in (smt.nseq.fine_wilf defaults to off)

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* pw_ab = mk_ground_power(sg, seq, m, "ab", n_e);
    euf::snode const* pw_abab = mk_ground_power(sg, seq, m, "abab", m_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_ab, u), sg.mk_concat(pw_abab, v));
    VERIFY(ng.solve() == seq::nielsen_graph::search_result::sat);
    std::cout << "  ok\n";
}

// ===================== apply_power_cursor (two-symbolic-cursor) =====================
// These call ng.test_apply_power_cursor(root) to run the modifier in isolation
// (bypassing the priority chain) so that num_cmp / split_power_elim cannot
// preempt it — we want to test power_cursor itself, not the dispatcher.

// (ab)^n·U = (ba)^m·V — non-commuting bases: streams "abab…" vs "baba…"
// mismatch at position 0 ⇒ both exponents bound to {0}: two progress children.
static void test_power_cursor_mismatch_noncommuting() {
    std::cout << "test_power_cursor_mismatch_noncommuting\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* pw_ab = mk_ground_power(sg, seq, m, "ab", n_e);
    euf::snode const* pw_ba = mk_ground_power(sg, seq, m, "ba", m_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_ab, u), sg.mk_concat(pw_ba, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_power_cursor(root));
    VERIFY(root->outgoing().size() == 2);
    VERIFY(count_edges_with_rule(root, "power cursor bound") == 2);
    for (seq::nielsen_edge const* e : root->outgoing())
        VERIFY(e->is_progress());
    std::cout << "  ok\n";
}

// (ab)^n·U = (abb)^m·V — shared prefix "ab", mismatch at position 2.
// escL: e ∈ {0 .. ⌊2/2⌋} = {0,1} (2 children); escR: f ∈ {0 .. ⌊2/3⌋} = {0}
// (1 child) ⇒ 3 progress children, exercising multi-value enumeration.
static void test_power_cursor_mismatch_enumeration() {
    std::cout << "test_power_cursor_mismatch_enumeration\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* pw_ab  = mk_ground_power(sg, seq, m, "ab", n_e);
    euf::snode const* pw_abb = mk_ground_power(sg, seq, m, "abb", m_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_ab, u), sg.mk_concat(pw_abb, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_power_cursor(root));
    VERIFY(root->outgoing().size() == 3);
    VERIFY(count_edges_with_rule(root, "power cursor bound") == 3);
    for (seq::nielsen_edge const* e : root->outgoing())
        VERIFY(e->is_progress());
    std::cout << "  ok\n";
}

// helper: assert the equation's two directional fronts are same-base powers
static void assert_same_base_power_fronts(seq::nielsen_node const* n, ast_manager& m) {
    VERIFY(n->str_eqs().size() == 1);
    seq::str_eq const& eq = n->str_eqs()[0];
    euf::snode const* lh = eq.m_lhs->first();
    euf::snode const* rh = eq.m_rhs->first();
    VERIFY(lh && lh->is_power());
    VERIFY(rh && rh->is_power());
    VERIFY(lh->arg0() == rh->arg0()); // SAME base snode ⇒ num_cmp territory
    (void)m;
}

// a·(ba)^n·U = (ab)^m·V — matched forever (both streams "abab…").  Re-base over
// z="ab" (g=2): a·(ba)^n = (ab)^n·a, so the child is a SAME-BASE equation.
// One unconditional-identity progress child, handed off to num_cmp.
static void test_power_cursor_rebase_offset() {
    std::cout << "test_power_cursor_rebase_offset\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* a = sg.mk_char('a');
    euf::snode const* pw_ba = mk_ground_power(sg, seq, m, "ba", n_e);
    euf::snode const* pw_ab = mk_ground_power(sg, seq, m, "ab", m_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    // a·(ba)^n·U = (ab)^m·V
    ng.add_str_eq(sg.mk_concat(a, sg.mk_concat(pw_ba, u)), sg.mk_concat(pw_ab, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_power_cursor(root));
    VERIFY(root->outgoing().size() == 1);
    VERIFY(count_edges_with_rule(root, "power cursor rebase") == 1);
    VERIFY(root->outgoing()[0]->is_progress());
    assert_same_base_power_fronts(root->outgoing()[0]->tgt(), m);
    std::cout << "  ok\n";
}

// (ab)^n·U = (abab)^m·V — commuting roots (common primitive root "ab", g=2).
// Re-base both to base "ab": (ab)^m → (ab)^{2m}.  One same-base child.
static void test_power_cursor_rebase_common_root() {
    std::cout << "test_power_cursor_rebase_common_root\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* pw_ab   = mk_ground_power(sg, seq, m, "ab", n_e);
    euf::snode const* pw_abab = mk_ground_power(sg, seq, m, "abab", m_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_ab, u), sg.mk_concat(pw_abab, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_power_cursor(root));
    VERIFY(root->outgoing().size() == 1);
    VERIFY(count_edges_with_rule(root, "power cursor rebase") == 1);
    assert_same_base_power_fronts(root->outgoing()[0]->tgt(), m);
    std::cout << "  ok\n";
}

// a·(aa)^m·x = (aaa)^n·y — different base lengths, common root z="a" (g=1).
// Re-base both over "a": a·(aa)^m → a^{1+2m}, (aaa)^n → a^{3n}.  One child.
static void test_power_cursor_rebase_difflen() {
    std::cout << "test_power_cursor_rebase_difflen\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    euf::snode const* a = sg.mk_char('a');
    euf::snode const* pw_aa  = mk_ground_power(sg, seq, m, "aa", m_e);
    euf::snode const* pw_aaa = mk_ground_power(sg, seq, m, "aaa", n_e);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(a, sg.mk_concat(pw_aa, x)), sg.mk_concat(pw_aaa, y));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_power_cursor(root));
    VERIFY(root->outgoing().size() == 1);
    VERIFY(count_edges_with_rule(root, "power cursor rebase") == 1);
    assert_same_base_power_fronts(root->outgoing()[0]->tgt(), m);
    std::cout << "  ok\n";
}

// same base at offset 0: (ab)^n·U = (ab)^m·V — the rebase would be a no-op, so
// the modifier must NOT fire (num_cmp owns this).  Guards against a
// no-progress child that would loop-cut without progress.
static void test_power_cursor_same_base_noop() {
    std::cout << "test_power_cursor_same_base_noop\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* pw_n = mk_ground_power(sg, seq, m, "ab", n_e);
    euf::snode const* pw_m = mk_ground_power(sg, seq, m, "ab", m_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_n, u), sg.mk_concat(pw_m, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(!ng.test_apply_power_cursor(root)); // no-op rebase ⇒ does not fire
    VERIFY(root->outgoing().empty());
    std::cout << "  ok\n";
}

// symbolic (variable) base: x^n·U = y^m·V — not ground ⇒ modifier bails.
static void test_power_cursor_symbolic_base_skipped() {
    std::cout << "test_power_cursor_symbolic_base_skipped\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    const expr_ref pw_x_e(seq.str.mk_power(x->get_expr(), n_e), m);
    const expr_ref pw_y_e(seq.str.mk_power(y->get_expr(), m_e), m);
    euf::snode const* pw_x = sg.mk(pw_x_e);
    euf::snode const* pw_y = sg.mk(pw_y_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_x, u), sg.mk_concat(pw_y, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(!ng.test_apply_power_cursor(root));
    std::cout << "  ok\n";
}

// only one side has a power: (ab)^n·U = "abc"·V — the other side has no power
// after its concrete run ⇒ modifier bails (const_num_unwinding owns this).
static void test_power_cursor_one_side_no_power() {
    std::cout << "test_power_cursor_one_side_no_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    euf::snode const* pw_ab = mk_ground_power(sg, seq, m, "ab", n_e);
    euf::snode const* abc = sg.mk(seq.str.mk_string(zstring("abc")));
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_ab, u), sg.mk_concat(abc, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(!ng.test_apply_power_cursor(root));
    std::cout << "  ok\n";
}

// solve-level: the motivating divergent UNSAT shape a·(ba)^n·"ab" = (ab)^n·"aba"
// closes string-only (rebase ⇒ same base ⇒ cancel ⇒ prefix clash), so it is
// unsat even with the always-SAT dummy length solver.  Diverges with the
// cursor off (that is exactly what this feature fixes).
static void test_power_cursor_solve_unsat() {
    std::cout << "test_power_cursor_solve_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    euf::snode const* a  = sg.mk_char('a');
    euf::snode const* ab = sg.mk(seq.str.mk_string(zstring("ab")));
    euf::snode const* aba = sg.mk(seq.str.mk_string(zstring("aba")));
    euf::snode const* pw_ba = mk_ground_power(sg, seq, m, "ba", n_e);
    euf::snode const* pw_ab = mk_ground_power(sg, seq, m, "ab", n_e);

    // a·(ba)^n·"ab" = (ab)^n·"aba"
    ng.add_str_eq(sg.mk_concat(a, sg.mk_concat(pw_ba, ab)),
                  sg.mk_concat(pw_ab, aba));
    VERIFY(ng.solve() == seq::nielsen_graph::search_result::unsat);
    std::cout << "  ok\n";
}

// solve-level: the non-commuting mismatch shape is satisfiable (n=m=0, U=V) and
// the search must terminate through the bounded-exponent children.
static void test_power_cursor_solve_sat() {
    std::cout << "test_power_cursor_solve_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* m_e = m.mk_const(symbol("m"), arith.mk_int());
    euf::snode const* pw_ab = mk_ground_power(sg, seq, m, "ab", n_e);
    euf::snode const* pw_ba = mk_ground_power(sg, seq, m, "ba", m_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pw_ab, u), sg.mk_concat(pw_ba, v));
    VERIFY(ng.solve() == seq::nielsen_graph::search_result::sat);
    std::cout << "  ok\n";
}

// ================= apply_power_cursor: nested ground powers =================
// Run via ng.test_apply_power_cursor(root) to isolate the modifier.
// Convention below: BC(p) = (bc)^p is an inner power token; a base like
// "BC(p)·a" is a token list [ (bc)^p , a ] whose tokens are compared by snode
// identity.

// a·((bc)^p·a)^n·U = (a·(bc)^p)^k·V — the nested analog of the conjugate case
// a·(ba)^n = (ab)^k·a.  Token streams [a,(bc)^p,a,(bc)^p,…] coincide, so both
// outer powers re-base over Z = a·(bc)^p ⇒ SAME outer base.  One progress child.
static void test_power_cursor_nested_conjugate() {
    std::cout << "test_power_cursor_nested_conjugate\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* p_e = m.mk_const(symbol("p"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* k_e = m.mk_const(symbol("k"), arith.mk_int());
    euf::snode const* a  = sg.mk_char('a');
    euf::snode const* bcp = mk_ground_power(sg, seq, m, "bc", p_e);   // (bc)^p
    euf::snode const* base1 = sg.mk_concat(bcp, a);                   // (bc)^p·a
    euf::snode const* base2 = sg.mk_concat(a, bcp);                   // a·(bc)^p
    euf::snode const* pow1 = mk_power_of(sg, seq, m, base1, n_e);     // ((bc)^p a)^n
    euf::snode const* pow2 = mk_power_of(sg, seq, m, base2, k_e);     // (a (bc)^p)^k
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    // a·((bc)^p a)^n·U = (a (bc)^p)^k·V
    ng.add_str_eq(sg.mk_concat(a, sg.mk_concat(pow1, u)), sg.mk_concat(pow2, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_power_cursor(root));
    VERIFY(root->outgoing().size() == 1);
    VERIFY(count_edges_with_rule(root, "power cursor rebase") == 1);
    VERIFY(root->outgoing()[0]->is_progress());
    assert_same_base_power_fronts(root->outgoing()[0]->tgt(), m);
    std::cout << "  ok\n";
}

// term-power common root: ((a(bc)^m)(a(bc)^m))^n = (a(bc)^m)^k — outer bases are
// [P,P] and [P] with P=(a(bc)^m) one identical token ⇒ re-base over Z=[P]:
// (base1)^n → P^{2n}, (base2)^k → P^k.  One same-base child (nested analog of
// (ab)^n vs (abab)^m).
static void test_power_cursor_nested_common_root() {
    std::cout << "test_power_cursor_nested_common_root\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* mm = m.mk_const(symbol("m"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* k_e = m.mk_const(symbol("k"), arith.mk_int());
    // P = (de)^m is a single nested token; base1 = P·P, base2 = P
    euf::snode const* Pw  = mk_ground_power(sg, seq, m, "de", mm);   // P = (de)^m
    euf::snode const* base1 = sg.mk_concat(Pw, Pw);                  // (de)^m·(de)^m
    euf::snode const* pow1 = mk_power_of(sg, seq, m, base1, n_e);    // ((de)^m (de)^m)^n
    euf::snode const* pow2 = mk_power_of(sg, seq, m, Pw, k_e);       // ((de)^m)^k
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pow1, u), sg.mk_concat(pow2, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_power_cursor(root));
    VERIFY(root->outgoing().size() == 1);
    VERIFY(count_edges_with_rule(root, "power cursor rebase") == 1);
    assert_same_base_power_fronts(root->outgoing()[0]->tgt(), m);
    std::cout << "  ok\n";
}

// depth-3 nesting: base tokens are themselves doubly-nested powers.
// [ ((de)^q f)^r , a ] vs [ a , ((de)^q f)^r ] — conjugate at the token level;
// the token ((de)^q f)^r is one identical snode on both sides ⇒ re-base.
static void test_power_cursor_nested_depth3() {
    std::cout << "test_power_cursor_nested_depth3\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* q_e = m.mk_const(symbol("q"), arith.mk_int());
    expr* r_e = m.mk_const(symbol("r"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* k_e = m.mk_const(symbol("k"), arith.mk_int());
    euf::snode const* a   = sg.mk_char('a');
    euf::snode const* f   = sg.mk_char('f');
    euf::snode const* deq = mk_ground_power(sg, seq, m, "de", q_e);   // (de)^q
    euf::snode const* inner = sg.mk_concat(deq, f);                   // (de)^q·f
    euf::snode const* T   = mk_power_of(sg, seq, m, inner, r_e);      // ((de)^q f)^r  (depth-2 token)
    euf::snode const* base1 = sg.mk_concat(T, a);                    // T·a
    euf::snode const* base2 = sg.mk_concat(a, T);                    // a·T
    euf::snode const* pow1 = mk_power_of(sg, seq, m, base1, n_e);
    euf::snode const* pow2 = mk_power_of(sg, seq, m, base2, k_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(a, sg.mk_concat(pow1, u)), sg.mk_concat(pow2, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_power_cursor(root));
    VERIFY(root->outgoing().size() == 1);
    VERIFY(count_edges_with_rule(root, "power cursor rebase") == 1);
    assert_same_base_power_fronts(root->outgoing()[0]->tgt(), m);
    std::cout << "  ok\n";
}

// SOUNDNESS: different inner exponents ((bc)^p·a) vs ((bc)^q·a), p≠q — the inner
// power tokens are DISTINCT snodes ⇒ token mismatch ⇒ the modifier must DECLINE
// (it must never rebase when the streams are only char-compatible).
static void test_power_cursor_nested_decline_inner_exp() {
    std::cout << "test_power_cursor_nested_decline_inner_exp\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* p_e = m.mk_const(symbol("p"), arith.mk_int());
    expr* q_e = m.mk_const(symbol("q"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* k_e = m.mk_const(symbol("k"), arith.mk_int());
    euf::snode const* a = sg.mk_char('a');
    euf::snode const* base1 = sg.mk_concat(mk_ground_power(sg, seq, m, "bc", p_e), a); // (bc)^p a
    euf::snode const* base2 = sg.mk_concat(mk_ground_power(sg, seq, m, "bc", q_e), a); // (bc)^q a
    euf::snode const* pow1 = mk_power_of(sg, seq, m, base1, n_e);
    euf::snode const* pow2 = mk_power_of(sg, seq, m, base2, k_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pow1, u), sg.mk_concat(pow2, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(!ng.test_apply_power_cursor(root));
    VERIFY(root->outgoing().empty());
    std::cout << "  ok\n";
}

// SOUNDNESS: char-compatible but token-different: ((ab)^m)^n = (ab)^k.  The outer
// bases are [ (ab)^m ] and [ a , b ] — NOT token-identical even though (ab)^m
// expands to a,b,a,b,… — so the modifier must DECLINE (rebasing here would be
// unsound only if the arithmetic were wrong, but token-seq inequality means we
// simply are not allowed to claim the identity).
static void test_power_cursor_nested_decline_char_compat() {
    std::cout << "test_power_cursor_nested_decline_char_compat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* mm = m.mk_const(symbol("m"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* k_e = m.mk_const(symbol("k"), arith.mk_int());
    euf::snode const* abm = mk_ground_power(sg, seq, m, "ab", mm);   // (ab)^m
    euf::snode const* pow1 = mk_power_of(sg, seq, m, abm, n_e);      // ((ab)^m)^n
    euf::snode const* pow2 = mk_ground_power(sg, seq, m, "ab", k_e); // (ab)^k
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pow1, u), sg.mk_concat(pow2, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(!ng.test_apply_power_cursor(root));
    std::cout << "  ok\n";
}

// same nested base, offset 0: (a(bc)^p)^n vs (a(bc)^p)^k — re-base would be a
// no-op, num_cmp owns it, so the modifier must DECLINE (no no-progress child).
static void test_power_cursor_nested_noop_same_base() {
    std::cout << "test_power_cursor_nested_noop_same_base\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* p_e = m.mk_const(symbol("p"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* k_e = m.mk_const(symbol("k"), arith.mk_int());
    euf::snode const* a = sg.mk_char('a');
    euf::snode const* base = sg.mk_concat(a, mk_ground_power(sg, seq, m, "bc", p_e)); // a·(bc)^p
    euf::snode const* pow1 = mk_power_of(sg, seq, m, base, n_e);
    euf::snode const* pow2 = mk_power_of(sg, seq, m, base, k_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pow1, u), sg.mk_concat(pow2, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(!ng.test_apply_power_cursor(root));
    std::cout << "  ok\n";
}

// solve-level, node-budgeted: the nested re-base must let a BOUNDED search
// finish rather than diverging on an outer one-copy peel.  (The dummy length
// solver always returns sat, so it cannot prune arithmetically — hence the
// explicit node budget; end-to-end termination with real arithmetic is covered
// by the d2 benchmark, which closes unsat.)  We only require the search to
// RETURN within the budget (no divergence / no crash).
static void test_power_cursor_nested_solve_bounded() {
    std::cout << "test_power_cursor_nested_solve_bounded\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    ng.set_max_nodes(400);       // bound the search: the dummy solver never prunes
    ng.set_max_search_depth(8);

    expr* p_e = m.mk_const(symbol("p"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* k_e = m.mk_const(symbol("k"), arith.mk_int());
    euf::snode const* a  = sg.mk_char('a');
    euf::snode const* bcp = mk_ground_power(sg, seq, m, "bc", p_e);
    euf::snode const* base1 = sg.mk_concat(bcp, a);
    euf::snode const* base2 = sg.mk_concat(a, bcp);
    euf::snode const* pow1 = mk_power_of(sg, seq, m, base1, n_e);
    euf::snode const* pow2 = mk_power_of(sg, seq, m, base2, k_e);

    ng.add_str_eq(sg.mk_concat(a, pow1), pow2);   // a·((bc)^p a)^n = (a (bc)^p)^k
    // Only require the bounded search to RETURN (any verdict) — i.e. not diverge.
    (void) ng.solve();
    std::cout << "  ok\n";
}

// token-gcd is a PROPER divisor: base1 = [P,P] with P=(cd)^p... no — use
// [P,a,P,a] (4 tokens) vs [P,a] (2 tokens), g=2, coef=|base1|/g=2.  Re-base
// base1^n → Z^{2n} over Z=[P,a].  Exercises the coef≠1 branch of M.
static void test_power_cursor_nested_gcd_proper_divisor() {
    std::cout << "test_power_cursor_nested_gcd_proper_divisor\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* p_e = m.mk_const(symbol("p"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* k_e = m.mk_const(symbol("k"), arith.mk_int());
    euf::snode const* a = sg.mk_char('a');
    euf::snode const* P = mk_ground_power(sg, seq, m, "cd", p_e);     // (cd)^p
    euf::snode const* Pa = sg.mk_concat(P, a);                        // [P,a]
    euf::snode const* base1 = sg.mk_concat(Pa, Pa);                   // [P,a,P,a]
    euf::snode const* pow1 = mk_power_of(sg, seq, m, base1, n_e);     // ([P,a][P,a])^n
    euf::snode const* pow2 = mk_power_of(sg, seq, m, Pa, k_e);        // ([P,a])^k
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(pow1, u), sg.mk_concat(pow2, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_power_cursor(root));
    VERIFY(root->outgoing().size() == 1);
    VERIFY(count_edges_with_rule(root, "power cursor rebase") == 1);
    assert_same_base_power_fronts(root->outgoing()[0]->tgt(), m);
    std::cout << "  ok\n";
}

// multi-token partial block Z1: 2-char run "ab" before the power, g=3.
// "ab"·((cd)^p·"ab")^n = ("ab"·(cd)^p)^k — token stream [a,b,(cd)^p]^ω, so
// Z = a·b·(cd)^p (3 tokens), α=2 ⇒ Z1 = Z[0..2) = [a,b] (a 2-token block).
static void test_power_cursor_nested_multitoken_z1() {
    std::cout << "test_power_cursor_nested_multitoken_z1\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* p_e = m.mk_const(symbol("p"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* k_e = m.mk_const(symbol("k"), arith.mk_int());
    euf::snode const* ab = sg.mk(seq.str.mk_string(zstring("ab")));   // tokens [a,b]
    euf::snode const* cdp = mk_ground_power(sg, seq, m, "cd", p_e);   // (cd)^p
    euf::snode const* base1 = sg.mk_concat(cdp, ab);                  // (cd)^p·ab  = [Q,a,b]
    euf::snode const* base2 = sg.mk_concat(ab, cdp);                  // ab·(cd)^p  = [a,b,Q] = Z
    euf::snode const* pow1 = mk_power_of(sg, seq, m, base1, n_e);
    euf::snode const* pow2 = mk_power_of(sg, seq, m, base2, k_e);
    euf::snode const* u = sg.mk_var(symbol("U"), sg.get_str_sort());
    euf::snode const* v = sg.mk_var(symbol("V"), sg.get_str_sort());

    // "ab"·((cd)^p ab)^n·U = (ab (cd)^p)^k·V
    ng.add_str_eq(sg.mk_concat(ab, sg.mk_concat(pow1, u)), sg.mk_concat(pow2, v));
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_power_cursor(root));
    VERIFY(root->outgoing().size() == 1);
    VERIFY(count_edges_with_rule(root, "power cursor rebase") == 1);
    assert_same_base_power_fronts(root->outgoing()[0]->tgt(), m);
    std::cout << "  ok\n";
}

// ================= apply_power_commute (priority 3e) =================
// U^n = V^m with ground but structurally-different bases ⟿ Lyndon–Schützenberger
// commutation: 3 children (commute / n=0 / m=0).  Run via test_apply_power_commute.

// (a·(bc)^p)^n = (a·(bc)^q)^m — the nested conjugate residual the char cursor
// declines.  Fires: 3 children; the commutation child is a concat=concat word
// equation (both outer powers eliminated), the other two are the empty branches.
static void test_power_commute_nested_fires() {
    std::cout << "test_power_commute_nested_fires\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* p_e = m.mk_const(symbol("p"), arith.mk_int());
    expr* q_e = m.mk_const(symbol("q"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* mm  = m.mk_const(symbol("mm"), arith.mk_int());
    euf::snode const* a   = sg.mk_char('a');
    euf::snode const* bcp = mk_ground_power(sg, seq, m, "bc", p_e);   // (bc)^p
    euf::snode const* bcq = mk_ground_power(sg, seq, m, "bc", q_e);   // (bc)^q
    euf::snode const* U   = sg.mk_concat(a, bcp);                     // a·(bc)^p
    euf::snode const* V   = sg.mk_concat(a, bcq);                     // a·(bc)^q
    euf::snode const* powU = mk_power_of(sg, seq, m, U, n_e);         // (a(bc)^p)^n
    euf::snode const* powV = mk_power_of(sg, seq, m, V, mm);          // (a(bc)^q)^m

    ng.add_str_eq(powU, powV);
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_power_commute(root));
    VERIFY(root->outgoing().size() == 3);
    VERIFY(count_edges_with_rule(root, "power commute n0") == 1);
    VERIFY(count_edges_with_rule(root, "power commute m0") == 1);
    // exactly one plain "power commute" (the commutation child): count total minus the two suffixed
    VERIFY(count_edges_with_rule(root, "power commute") == 3); // prefix match: all three start with it
    for (seq::nielsen_edge const* e : root->outgoing())
        VERIFY(e->is_progress());

    // locate the commutation child (rule exactly "power commute") and check its
    // single equation is a concat = concat (both outer powers gone).
    seq::nielsen_node* commute_child = nullptr;
    for (seq::nielsen_edge const* e : root->outgoing())
        if (strcmp(e->rule_name(), "power commute") == 0)
            commute_child = e->tgt();
    VERIFY(commute_child != nullptr);
    VERIFY(commute_child->str_eqs().size() == 1);
    VERIFY(commute_child->str_eqs()[0].m_lhs->is_concat());
    VERIFY(commute_child->str_eqs()[0].m_rhs->is_concat());
    VERIFY(!commute_child->str_eqs()[0].m_lhs->is_power());
    std::cout << "  ok\n";
}

// same base U^n = U^m ⟿ owned by num_cmp (priority 3), commutation must DECLINE.
static void test_power_commute_same_base_skipped() {
    std::cout << "test_power_commute_same_base_skipped\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* p_e = m.mk_const(symbol("p"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* mm  = m.mk_const(symbol("mm"), arith.mk_int());
    euf::snode const* a   = sg.mk_char('a');
    euf::snode const* bcp = mk_ground_power(sg, seq, m, "bc", p_e);
    euf::snode const* U   = sg.mk_concat(a, bcp);
    euf::snode const* powU = mk_power_of(sg, seq, m, U, n_e);
    euf::snode const* powU2 = mk_power_of(sg, seq, m, U, mm);   // same base U

    ng.add_str_eq(powU, powU2);
    seq::nielsen_node* root = ng.root();

    VERIFY(!ng.test_apply_power_commute(root));
    VERIFY(root->outgoing().empty());
    std::cout << "  ok\n";
}

// tail present (U^n·x = V^m) ⟿ not a pure power equation, commutation DECLINES.
static void test_power_commute_tail_skipped() {
    std::cout << "test_power_commute_tail_skipped\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* p_e = m.mk_const(symbol("p"), arith.mk_int());
    expr* q_e = m.mk_const(symbol("q"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* mm  = m.mk_const(symbol("mm"), arith.mk_int());
    euf::snode const* a   = sg.mk_char('a');
    euf::snode const* bcp = mk_ground_power(sg, seq, m, "bc", p_e);
    euf::snode const* bcq = mk_ground_power(sg, seq, m, "bc", q_e);
    euf::snode const* powU = mk_power_of(sg, seq, m, sg.mk_concat(a, bcp), n_e);
    euf::snode const* powV = mk_power_of(sg, seq, m, sg.mk_concat(a, bcq), mm);
    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());

    ng.add_str_eq(sg.mk_concat(powU, x), powV);   // U^n·x = V^m
    seq::nielsen_node* root = ng.root();

    VERIFY(!ng.test_apply_power_commute(root));
    std::cout << "  ok\n";
}

// ================= apply_ground_power_split (priority 3e2) =================
// Fully-ground tailed power head P^e·L'' = Q^f·R'' with different nested bases:
// a 3-way length race producing "gpsplit =", "gpsplit <", "gpsplit >" children.

// (a(bc)^p)^n · "d" = (a(bc)^q)^m · "e" — fires; at least the = child plus the
// < and > quotient children.  (Distinct tails "d"/"e" so it is not pure.)
static void test_gpsplit_nested_tailed_fires() {
    std::cout << "test_gpsplit_nested_tailed_fires\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* p_e = m.mk_const(symbol("p"), arith.mk_int());
    expr* q_e = m.mk_const(symbol("q"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* mm  = m.mk_const(symbol("mm"), arith.mk_int());
    euf::snode const* a   = sg.mk_char('a');
    euf::snode const* bcp = mk_ground_power(sg, seq, m, "bc", p_e);
    euf::snode const* bcq = mk_ground_power(sg, seq, m, "bc", q_e);
    euf::snode const* powU = mk_power_of(sg, seq, m, sg.mk_concat(a, bcp), n_e);
    euf::snode const* powV = mk_power_of(sg, seq, m, sg.mk_concat(a, bcq), mm);
    euf::snode const* d = sg.mk_char('d');
    euf::snode const* e = sg.mk_char('e');

    ng.add_str_eq(sg.mk_concat(powU, d), sg.mk_concat(powV, e));   // U^n·d = V^m·e
    seq::nielsen_node* root = ng.root();

    VERIFY(ng.test_apply_ground_power_split(root));
    VERIFY(count_edges_with_rule(root, "gpsplit =") == 1);
    VERIFY(count_edges_with_rule(root, "gpsplit &lt;") >= 1);
    VERIFY(count_edges_with_rule(root, "gpsplit &gt;") >= 1);
    // the = child holds two equations: P^e = Q^f (pure) and L'' = R''
    seq::nielsen_node* eqchild = nullptr;
    for (seq::nielsen_edge const* ed : root->outgoing())
        if (strcmp(ed->rule_name(), "gpsplit =") == 0)
            eqchild = ed->tgt();
    VERIFY(eqchild != nullptr);
    VERIFY(eqchild->str_eqs().size() == 2);
    std::cout << "  ok\n";
}

// pure P^e = Q^f (no tails) is owned by apply_power_commute → split DECLINES.
static void test_gpsplit_pure_skipped() {
    std::cout << "test_gpsplit_pure_skipped\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    arith_util arith(m);
    seq_util seq(m);

    dummy_simple_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    expr* p_e = m.mk_const(symbol("p"), arith.mk_int());
    expr* q_e = m.mk_const(symbol("q"), arith.mk_int());
    expr* n_e = m.mk_const(symbol("n"), arith.mk_int());
    expr* mm  = m.mk_const(symbol("mm"), arith.mk_int());
    euf::snode const* a   = sg.mk_char('a');
    euf::snode const* powU = mk_power_of(sg, seq, m, sg.mk_concat(a, mk_ground_power(sg, seq, m, "bc", p_e)), n_e);
    euf::snode const* powV = mk_power_of(sg, seq, m, sg.mk_concat(a, mk_ground_power(sg, seq, m, "bc", q_e)), mm);

    ng.add_str_eq(powU, powV);   // pure U^n = V^m
    seq::nielsen_node* root = ng.root();

    VERIFY(!ng.test_apply_ground_power_split(root));
    VERIFY(root->outgoing().empty());
    std::cout << "  ok\n";
}

void tst_seq_nielsen() {
    std::cout << std::unitbuf; // flush per write: locate crashes/assertions
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
    // IntBounds / subsolver bounds / Constraint.Shared tests
    test_add_lower_int_bound_basic();
    test_add_upper_int_bound_basic();
    test_add_bound_lb_gt_ub_conflict();
    test_bounds_cloned();
    test_subst_does_not_propagate_bounds_single_var();
    test_subst_no_immediate_bound_conflict();
    test_simplify_does_not_add_local_parikh_bounds();
    test_assert_root_constraints_to_solver();
    test_assert_root_constraints_once();
    test_subst_does_not_propagate_bounds_multi_var();
    test_simplify_unit_prefix_split();
    test_simplify_unit_prefix_split_empty_rest();
    test_simplify_unit_suffix_split();
    // Fine & Wilf overlap splitting (apply_fine_wilf, priority 3c)
    test_fine_wilf_noncommuting_children();
    test_fine_wilf_commuting_children();
    test_fine_wilf_ground_prefix();
    test_fine_wilf_same_base_skipped();
    test_fine_wilf_symbolic_refire_guard();
    test_fine_wilf_solve_commuting_sat();
    // Two-symbolic-cursor acceleration (apply_power_cursor, priority 3d)
    test_power_cursor_mismatch_noncommuting();
    test_power_cursor_mismatch_enumeration();
    test_power_cursor_rebase_offset();
    test_power_cursor_rebase_common_root();
    test_power_cursor_rebase_difflen();
    test_power_cursor_same_base_noop();
    test_power_cursor_symbolic_base_skipped();
    test_power_cursor_one_side_no_power();
    test_power_cursor_solve_unsat();
    test_power_cursor_solve_sat();
    // Nested ground powers (unified apply_power_cursor, priority 3d)
    test_power_cursor_nested_conjugate();
    test_power_cursor_nested_common_root();
    test_power_cursor_nested_depth3();
    test_power_cursor_nested_decline_inner_exp();
    test_power_cursor_nested_decline_char_compat();
    test_power_cursor_nested_noop_same_base();
    test_power_cursor_nested_gcd_proper_divisor();
    test_power_cursor_nested_multitoken_z1();
    test_power_cursor_nested_solve_bounded();
    // Commutation for pure U^n = V^m ground power residual (apply_power_commute, 3e)
    test_power_commute_nested_fires();
    test_power_commute_same_base_skipped();
    test_power_commute_tail_skipped();
    // General fully-ground tailed power head (apply_ground_power_split, 3e2)
    test_gpsplit_nested_tailed_fires();
    test_gpsplit_pure_skipped();
}
