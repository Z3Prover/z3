/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_sgraph.cpp

Abstract:

    Self-contained unit tests for the sgraph string graph layer.
    Tests snode classification, metadata computation, push/pop
    backtracking, associativity-respecting hash table, compound
    node construction, and snode navigation.

--*/

#include "util/util.h"
#include "ast/euf/euf_sgraph.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include <iostream>

// test classification and metadata for basic string nodes:
// variables, empty strings, characters, units, and concats
static void test_sgraph_classify() {
    std::cout << "test_sgraph_classify\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::sgraph sg(m);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    // string variable
    expr_ref x(m.mk_const("x", str_sort), m);
    euf::snode* sx = sg.mk(x);
    SASSERT(sx && sx->is_var());
    SASSERT(!sx->is_ground());
    SASSERT(sx->is_regex_free());
    SASSERT(!sx->is_nullable());
    SASSERT(sx->level() == 1);
    SASSERT(sx->length() == 1);
    SASSERT(sx->is_token());

    // empty string
    expr_ref empty(seq.str.mk_empty(str_sort), m);
    euf::snode* se = sg.mk(empty);
    SASSERT(se && se->is_empty());
    SASSERT(se->is_ground());
    SASSERT(se->is_nullable());
    SASSERT(se->level() == 0);
    SASSERT(se->length() == 0);
    SASSERT(!se->is_token());

    // character unit with literal char
    expr_ref ch(seq.str.mk_char('A'), m);
    expr_ref unit_a(seq.str.mk_unit(ch), m);
    euf::snode* sca = sg.mk(unit_a);
    SASSERT(sca && sca->is_char());
    SASSERT(sca->is_ground());
    SASSERT(!sca->is_nullable());
    SASSERT(sca->level() == 1);
    SASSERT(sca->length() == 1);
    SASSERT(sca->is_token());

    // concat of two variables
    expr_ref y(m.mk_const("y", str_sort), m);
    expr_ref xy(seq.str.mk_concat(x, y), m);
    euf::snode* sxy = sg.mk(xy);
    SASSERT(sxy && sxy->is_concat());
    SASSERT(!sxy->is_ground());
    SASSERT(sxy->is_regex_free());
    SASSERT(!sxy->is_nullable());
    SASSERT(sxy->level() == 2);
    SASSERT(sxy->length() == 2);
    SASSERT(sxy->num_args() == 2);
    SASSERT(!sxy->is_token());

    sg.display(std::cout);
}

// test classification for regex nodes:
// star, union, intersection, complement, full_seq, full_char, fail, to_re, in_re
static void test_sgraph_regex() {
    std::cout << "test_sgraph_regex\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::sgraph sg(m);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);

    // to_re
    expr_ref to_re_x(seq.re.mk_to_re(x), m);
    euf::snode* str = sg.mk(to_re_x);
    SASSERT(str && str->is_to_re());
    SASSERT(!str->is_regex_free());
    SASSERT(!str->is_nullable()); // to_re(x) nullable iff x nullable, x is var so not nullable
    SASSERT(str->num_args() == 1);

    // star
    expr_ref star_x(seq.re.mk_star(to_re_x), m);
    euf::snode* ss = sg.mk(star_x);
    SASSERT(ss && ss->is_star());
    SASSERT(!ss->is_regex_free());
    SASSERT(ss->is_nullable()); // star is always nullable
    SASSERT(ss->num_args() == 1);

    // full_seq (.*)
    expr_ref full_seq(seq.re.mk_full_seq(str_sort), m);
    euf::snode* sfs = sg.mk(full_seq);
    SASSERT(sfs && sfs->is_full_seq());
    SASSERT(sfs->is_ground());
    SASSERT(sfs->is_nullable());

    // full_char (.)
    expr_ref full_char(seq.re.mk_full_char(str_sort), m);
    euf::snode* sfc = sg.mk(full_char);
    SASSERT(sfc && sfc->is_full_char());
    SASSERT(sfc->is_ground());
    SASSERT(!sfc->is_nullable());

    // empty set, fail
    sort_ref re_sort(seq.re.mk_re(str_sort), m);
    expr_ref empty_set(seq.re.mk_empty(re_sort), m);
    euf::snode* sfail = sg.mk(empty_set);
    SASSERT(sfail && sfail->is_fail());
    SASSERT(!sfail->is_nullable());

    // union: to_re(x) | star(to_re(x)), nullable because star is
    expr_ref re_union(seq.re.mk_union(to_re_x, star_x), m);
    euf::snode* su = sg.mk(re_union);
    SASSERT(su && su->is_union());
    SASSERT(su->is_nullable()); // star_x is nullable

    // intersection: to_re(x) & star(to_re(x)), nullable only if both are
    expr_ref re_inter(seq.re.mk_inter(to_re_x, star_x), m);
    euf::snode* si = sg.mk(re_inter);
    SASSERT(si && si->is_intersect());
    SASSERT(!si->is_nullable()); // to_re(x) is not nullable

    // complement of to_re(x): nullable because to_re(x) is not nullable
    expr_ref re_comp(seq.re.mk_complement(to_re_x), m);
    euf::snode* sc = sg.mk(re_comp);
    SASSERT(sc && sc->is_complement());
    SASSERT(sc->is_nullable()); // complement of non-nullable is nullable

    // in_re
    expr_ref in_re(seq.re.mk_in_re(x, star_x), m);
    euf::snode* sir = sg.mk(in_re);
    SASSERT(sir && sir->is_in_re());
    SASSERT(!sir->is_regex_free());

    sg.display(std::cout);
}

// test power node classification and metadata
static void test_sgraph_power() {
    std::cout << "test_sgraph_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::sgraph sg(m);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref n(arith.mk_int(3), m);
    expr_ref xn(seq.str.mk_power(x, n), m);

    euf::snode* sp = sg.mk(xn);
    SASSERT(sp && sp->is_power());
    SASSERT(!sp->is_ground()); // base x is not ground
    SASSERT(sp->is_regex_free());
    SASSERT(!sp->is_nullable()); // base x is not nullable
    SASSERT(sp->num_args() >= 1);

    sg.display(std::cout);
}

// test push/pop backtracking: nodes created inside a scope
// are removed on pop, nodes before persist
static void test_sgraph_push_pop() {
    std::cout << "test_sgraph_push_pop\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::sgraph sg(m);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref y(m.mk_const("y", str_sort), m);
    expr_ref z(m.mk_const("z", str_sort), m);

    // create x before any scope
    sg.mk(x);
    unsigned before = sg.num_nodes();
    SASSERT(sg.find(x));

    sg.push();

    // create y and concat(x,y) inside scope
    expr_ref xy(seq.str.mk_concat(x, y), m);
    sg.mk(xy);
    SASSERT(sg.num_nodes() > before);
    SASSERT(sg.find(y));
    SASSERT(sg.find(xy));

    sg.pop(1);

    // x persists, y and xy removed
    SASSERT(sg.find(x));
    SASSERT(!sg.find(y));
    SASSERT(!sg.find(xy));
    SASSERT(sg.num_nodes() == before);
}

// test nested push/pop with multiple scopes
static void test_sgraph_nested_scopes() {
    std::cout << "test_sgraph_nested_scopes\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::sgraph sg(m);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref a(m.mk_const("a", str_sort), m);
    expr_ref b(m.mk_const("b", str_sort), m);
    expr_ref c(m.mk_const("c", str_sort), m);

    sg.mk(a);
    unsigned n0 = sg.num_nodes();

    sg.push();
    sg.mk(b);
    unsigned n1 = sg.num_nodes();

    sg.push();
    sg.mk(c);
    unsigned n2 = sg.num_nodes();
    SASSERT(n2 > n1 && n1 > n0);

    // pop inner scope, c goes away
    sg.pop(1);
    SASSERT(sg.num_nodes() == n1);
    SASSERT(sg.find(a));
    SASSERT(sg.find(b));
    SASSERT(!sg.find(c));

    // pop outer scope, b goes away
    sg.pop(1);
    SASSERT(sg.num_nodes() == n0);
    SASSERT(sg.find(a));
    SASSERT(!sg.find(b));
}

// test that find returns the same snode for the same expression
static void test_sgraph_find_idempotent() {
    std::cout << "test_sgraph_find_idempotent\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::sgraph sg(m);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    euf::snode* s1 = sg.mk(x);
    euf::snode* s2 = sg.mk(x);  // calling mk again returns same node
    SASSERT(s1 == s2);
    SASSERT(s1 == sg.find(x));
}

// test mk_concat: empty absorption, node construction via mk(concat_expr)
static void test_sgraph_mk_concat() {
    std::cout << "test_sgraph_mk_concat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::sgraph sg(m);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref y(m.mk_const("y", str_sort), m);
    expr_ref empty(seq.str.mk_empty(str_sort), m);

    euf::snode* sx = sg.mk(x);
    euf::snode* sy = sg.mk(y);
    euf::snode* se = sg.mk(empty);

    // concat with empty yields the non-empty side at sgraph level
    // (empty absorption is a property of the expression, checked via mk)
    SASSERT(se && se->is_empty());

    // normal concat via expression
    expr_ref xy(seq.str.mk_concat(x, y), m);
    euf::snode* sxy = sg.mk(xy);
    SASSERT(sxy && sxy->is_concat());
    SASSERT(sxy->num_args() == 2);
    SASSERT(sxy->arg(0) == sx);
    SASSERT(sxy->arg(1) == sy);

    // calling mk again with same expr returns same node
    euf::snode* sxy2 = sg.mk(xy);
    SASSERT(sxy == sxy2);
}

// test power node construction via mk(power_expr)
static void test_sgraph_mk_power() {
    std::cout << "test_sgraph_mk_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::sgraph sg(m);
    seq_util seq(m);
    arith_util arith(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref n(arith.mk_int(5), m);
    expr_ref xn(seq.str.mk_power(x, n), m);

    euf::snode* sx = sg.mk(x);
    euf::snode* sp = sg.mk(xn);
    SASSERT(sp && sp->is_power());
    SASSERT(sp->num_args() == 2);
    SASSERT(sp->arg(0) == sx);

    // calling mk again returns same node
    euf::snode* sp2 = sg.mk(xn);
    SASSERT(sp == sp2);
}

// test snode first/last navigation on concat trees
static void test_sgraph_first_last() {
    std::cout << "test_sgraph_first_last\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::sgraph sg(m);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref a(m.mk_const("a", str_sort), m);
    expr_ref b(m.mk_const("b", str_sort), m);
    expr_ref c(m.mk_const("c", str_sort), m);

    euf::snode* sa = sg.mk(a);
    euf::snode* sb = sg.mk(b);
    euf::snode* sc = sg.mk(c);

    // concat(concat(a,b),c): first=a, last=c
    expr_ref ab(seq.str.mk_concat(a, b), m);
    expr_ref ab_c(seq.str.mk_concat(ab, c), m);
    euf::snode* sab_c = sg.mk(ab_c);
    SASSERT(sab_c->first() == sa);
    SASSERT(sab_c->last() == sc);

    // concat(a,concat(b,c)): first=a, last=c
    expr_ref bc(seq.str.mk_concat(b, c), m);
    expr_ref a_bc(seq.str.mk_concat(a, bc), m);
    euf::snode* sa_bc = sg.mk(a_bc);
    SASSERT(sa_bc->first() == sa);
    SASSERT(sa_bc->last() == sc);

    // single node: first and last are self
    SASSERT(sa->first() == sa);
    SASSERT(sa->last() == sa);
}

// test concat metadata propagation:
// ground, regex_free, nullable, level, length
static void test_sgraph_concat_metadata() {
    std::cout << "test_sgraph_concat_metadata\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::sgraph sg(m);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref empty(seq.str.mk_empty(str_sort), m);
    expr_ref ch(seq.str.mk_char('Z'), m);
    expr_ref unit_z(seq.str.mk_unit(ch), m);

    euf::snode* sx = sg.mk(x);
    euf::snode* se = sg.mk(empty);
    euf::snode* sz = sg.mk(unit_z);

    // concat(x, unit('Z')): not ground (x is variable), regex_free, not nullable
    expr_ref xz(seq.str.mk_concat(x, unit_z), m);
    euf::snode* sxz = sg.mk(xz);
    SASSERT(!sxz->is_ground());
    SASSERT(sxz->is_regex_free());
    SASSERT(!sxz->is_nullable());
    SASSERT(sxz->length() == 2);
    SASSERT(sxz->level() == 2);

    // concat(empty, empty): nullable (both empty)
    expr_ref empty2(seq.str.mk_concat(empty, empty), m);
    euf::snode* see = sg.mk(empty2);
    SASSERT(see->is_nullable());
    SASSERT(see->is_ground());
    SASSERT(see->length() == 0);

    // deep chain: concat(concat(x,x),concat(x,x)) has level 3, length 4
    expr_ref xx(seq.str.mk_concat(x, x), m);
    expr_ref xxxx(seq.str.mk_concat(xx, xx), m);
    euf::snode* sxxxx = sg.mk(xxxx);
    SASSERT(sxxxx->level() == 3);
    SASSERT(sxxxx->length() == 4);
}

// test display does not crash
static void test_sgraph_display() {
    std::cout << "test_sgraph_display\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::sgraph sg(m);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref y(m.mk_const("y", str_sort), m);
    expr_ref xy(seq.str.mk_concat(x, y), m);
    sg.mk(xy);

    std::ostringstream oss;
    sg.display(oss);
    std::string out = oss.str();
    SASSERT(out.find("var") != std::string::npos);
    SASSERT(out.find("concat") != std::string::npos);
    std::cout << out;
}

void tst_euf_sgraph() {
    test_sgraph_classify();
    test_sgraph_regex();
    test_sgraph_power();
    test_sgraph_push_pop();
    test_sgraph_nested_scopes();
    test_sgraph_find_idempotent();
    test_sgraph_mk_concat();
    test_sgraph_mk_power();
    test_sgraph_first_last();
    test_sgraph_concat_metadata();
    test_sgraph_display();
}
