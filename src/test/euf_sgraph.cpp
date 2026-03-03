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
#include <sstream>

// test classification and metadata for basic string nodes:
// variables, empty strings, characters, units, and concats
static void test_sgraph_classify() {
    std::cout << "test_sgraph_classify\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
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
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
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

// test re.concat is classified as s_concat (not s_other)
// and loop nullability with lower bound 0
static void test_sgraph_re_concat_and_loop() {
    std::cout << "test_sgraph_re_concat_and_loop\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref to_re_x(seq.re.mk_to_re(x), m);

    // re.concat should be classified as s_concat
    expr_ref re_a(seq.re.mk_to_re(x), m);
    sort_ref re_sort(seq.re.mk_re(str_sort), m);
    expr_ref ch_a(seq.str.mk_char('a'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref re_unit_a(seq.re.mk_to_re(unit_a), m);
    expr_ref star_x(seq.re.mk_star(to_re_x), m);

    // re.concat(star_x, re_unit_a): should be classified as s_concat
    expr_ref re_cat(seq.re.mk_concat(star_x, re_unit_a), m);
    euf::snode* src = sg.mk(re_cat);
    SASSERT(src && src->is_concat()); // fix 1: re.concat must be s_concat

    // loop with lower bound 0: r{0,5} should be nullable
    expr_ref loop_0(seq.re.mk_loop(star_x, 0, 5), m);
    euf::snode* sl0 = sg.mk(loop_0);
    SASSERT(sl0 && sl0->is_loop());
    SASSERT(sl0->is_nullable()); // fix 2: lo=0 => nullable

    // loop with lower bound 1: r{1,5} should NOT be nullable
    expr_ref loop_1(seq.re.mk_loop(star_x, 1, 5), m);
    euf::snode* sl1 = sg.mk(loop_1);
    SASSERT(sl1 && sl1->is_loop());
    SASSERT(!sl1->is_nullable()); // lo=1 => not nullable (body star is nullable but lo>=1)

    // loop with lower bound 0 (single-arg form): r{0} should be nullable
    expr_ref loop_0s(seq.re.mk_loop(star_x, 0u), m);
    euf::snode* sl0s = sg.mk(loop_0s);
    SASSERT(sl0s && sl0s->is_loop());
    SASSERT(sl0s->is_nullable()); // fix 2: lo=0 => nullable

    sg.display(std::cout);
}

// test power node classification and metadata
static void test_sgraph_power() {
    std::cout << "test_sgraph_power\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
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
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref y(m.mk_const("y", str_sort), m);

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
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
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
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
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
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    expr_ref x(m.mk_const("x", str_sort), m);
    expr_ref y(m.mk_const("y", str_sort), m);
    expr_ref empty(seq.str.mk_empty(str_sort), m);

    euf::snode* sx = sg.mk(x);
    euf::snode* sy = sg.mk(y);
    euf::snode* se = sg.mk(empty);

    // concat with empty yields the non-empty side at sgraph level
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
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
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
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
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
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
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
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
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

// test sgraph factory methods: mk_var, mk_char, mk_empty, mk_concat
static void test_sgraph_factory() {
    std::cout << "test_sgraph_factory\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    // mk_var
    euf::snode* x = sg.mk_var(symbol("x"));
    SASSERT(x && x->is_var());
    SASSERT(!x->is_ground());
    SASSERT(x->length() == 1);

    // mk_char
    euf::snode* a = sg.mk_char('A');
    SASSERT(a && a->is_char());
    SASSERT(a->is_ground());
    SASSERT(a->length() == 1);

    // mk_empty
    euf::snode* e = sg.mk_empty();
    SASSERT(e && e->is_empty());
    SASSERT(e->is_nullable());
    SASSERT(e->length() == 0);

    // mk_concat with empty absorption
    euf::snode* xe = sg.mk_concat(x, e);
    SASSERT(xe == x);
    euf::snode* ex = sg.mk_concat(e, x);
    SASSERT(ex == x);

    // mk_concat of two variables
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* xy = sg.mk_concat(x, y);
    SASSERT(xy && xy->is_concat());
    SASSERT(xy->length() == 2);
    SASSERT(xy->arg(0) == x);
    SASSERT(xy->arg(1) == y);

    // mk_concat of multiple characters
    euf::snode* b = sg.mk_char('B');
    euf::snode* c = sg.mk_char('C');
    euf::snode* abc = sg.mk_concat(sg.mk_concat(a, b), c);
    SASSERT(abc->length() == 3);
    SASSERT(abc->is_ground());
    SASSERT(abc->first() == a);
    SASSERT(abc->last() == c);
}

// test snode::at() and snode::collect_tokens()
static void test_sgraph_indexing() {
    std::cout << "test_sgraph_indexing\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* c = sg.mk_char('C');
    euf::snode* x = sg.mk_var(symbol("x"));

    // build concat(concat(a, b), concat(c, x)) => [A, B, C, x]
    euf::snode* ab = sg.mk_concat(a, b);
    euf::snode* cx = sg.mk_concat(c, x);
    euf::snode* abcx = sg.mk_concat(ab, cx);

    SASSERT(abcx->length() == 4);

    // test at()
    SASSERT(abcx->at(0) == a);
    SASSERT(abcx->at(1) == b);
    SASSERT(abcx->at(2) == c);
    SASSERT(abcx->at(3) == x);
    SASSERT(abcx->at(4) == nullptr); // out of bounds

    // test collect_tokens()
    euf::snode_vector tokens;
    abcx->collect_tokens(tokens);
    SASSERT(tokens.size() == 4);
    SASSERT(tokens[0] == a);
    SASSERT(tokens[1] == b);
    SASSERT(tokens[2] == c);
    SASSERT(tokens[3] == x);

    // single token: at(0) is self
    SASSERT(a->at(0) == a);
    SASSERT(a->at(1) == nullptr);

    // empty: at(0) is nullptr
    euf::snode* e = sg.mk_empty();
    SASSERT(e->at(0) == nullptr);
    euf::snode_vector empty_tokens;
    e->collect_tokens(empty_tokens);
    SASSERT(empty_tokens.empty());
}

// test sgraph drop operations
static void test_sgraph_drop() {
    std::cout << "test_sgraph_drop\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* c = sg.mk_char('C');
    euf::snode* d = sg.mk_char('D');

    // build concat(concat(a, b), concat(c, d)) => [A, B, C, D]
    euf::snode* ab = sg.mk_concat(a, b);
    euf::snode* cd = sg.mk_concat(c, d);
    euf::snode* abcd = sg.mk_concat(ab, cd);

    SASSERT(abcd->length() == 4);

    // drop_first: [A, B, C, D] => [B, C, D]
    euf::snode* bcd = sg.drop_first(abcd);
    SASSERT(bcd->length() == 3);
    SASSERT(bcd->first() == b);
    SASSERT(bcd->last() == d);

    // drop_last: [A, B, C, D] => [A, B, C]
    euf::snode* abc = sg.drop_last(abcd);
    SASSERT(abc->length() == 3);
    SASSERT(abc->first() == a);
    SASSERT(abc->last() == c);

    // drop_left(2): [A, B, C, D] => [C, D]
    euf::snode* cd2 = sg.drop_left(abcd, 2);
    SASSERT(cd2->length() == 2);
    SASSERT(cd2->first() == c);

    // drop_right(2): [A, B, C, D] => [A, B]
    euf::snode* ab2 = sg.drop_right(abcd, 2);
    SASSERT(ab2->length() == 2);
    SASSERT(ab2->last() == b);

    // drop all: [A, B, C, D] => empty
    euf::snode* empty = sg.drop_left(abcd, 4);
    SASSERT(empty->is_empty());

    // drop from single token: [A] => empty
    euf::snode* e = sg.drop_first(a);
    SASSERT(e->is_empty());

    // drop from empty: no change
    euf::snode* ee = sg.drop_first(sg.mk_empty());
    SASSERT(ee->is_empty());
}

// test sgraph substitution
static void test_sgraph_subst() {
    std::cout << "test_sgraph_subst\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');

    // concat(x, concat(a, x)) with x -> b gives concat(b, concat(a, b))
    euf::snode* ax = sg.mk_concat(a, x);
    euf::snode* xax = sg.mk_concat(x, ax);
    SASSERT(xax->length() == 3);

    euf::snode* result = sg.subst(xax, x, b);
    SASSERT(result->length() == 3);
    SASSERT(result->first() == b);
    SASSERT(result->last() == b);
    SASSERT(result->at(1) == a); // middle is still 'A'

    // substitution of non-occurring variable is identity
    euf::snode* same = sg.subst(xax, y, b);
    SASSERT(same == xax);

    // substitution of variable with empty
    euf::snode* e = sg.mk_empty();
    euf::snode* collapsed = sg.subst(xax, x, e);
    SASSERT(collapsed->length() == 1); // just 'a' remains
    SASSERT(collapsed == a);
}

// test complex concatenation creation, merging and simplification
static void test_sgraph_complex_concat() {
    std::cout << "test_sgraph_complex_concat\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);

    // build a string "HELLO" = concat(H, concat(E, concat(L, concat(L, O))))
    euf::snode* h = sg.mk_char('H');
    euf::snode* e = sg.mk_char('E');
    euf::snode* l = sg.mk_char('L');
    euf::snode* o = sg.mk_char('O');

    euf::snode* lo = sg.mk_concat(l, o);
    euf::snode* llo = sg.mk_concat(l, lo);
    euf::snode* ello = sg.mk_concat(e, llo);
    euf::snode* hello = sg.mk_concat(h, ello);

    SASSERT(hello->length() == 5);
    SASSERT(hello->is_ground());
    SASSERT(hello->first() == h);
    SASSERT(hello->last() == o);

    // index into "HELLO"
    SASSERT(hello->at(0) == h);
    SASSERT(hello->at(1) == e);
    SASSERT(hello->at(2) == l);
    SASSERT(hello->at(3) == l);
    SASSERT(hello->at(4) == o);

    // drop first 2 from "HELLO" => "LLO"
    euf::snode* llo2 = sg.drop_left(hello, 2);
    SASSERT(llo2->length() == 3);
    SASSERT(llo2->first() == l);

    // drop last 3 from "HELLO" => "HE"
    euf::snode* he = sg.drop_right(hello, 3);
    SASSERT(he->length() == 2);
    SASSERT(he->first() == h);
    SASSERT(he->last() == e);

    // mixed variables and characters: concat(x, "AB", y)
    euf::snode* x = sg.mk_var(symbol("x"));
    euf::snode* y = sg.mk_var(symbol("y"));
    euf::snode* a = sg.mk_char('A');
    euf::snode* b = sg.mk_char('B');
    euf::snode* ab = sg.mk_concat(a, b);
    euf::snode* xab = sg.mk_concat(x, ab);
    euf::snode* xaby = sg.mk_concat(xab, y);

    SASSERT(xaby->length() == 4);
    SASSERT(!xaby->is_ground());
    SASSERT(xaby->at(0) == x);
    SASSERT(xaby->at(1) == a);
    SASSERT(xaby->at(2) == b);
    SASSERT(xaby->at(3) == y);
}

// test Brzozowski derivative computation
static void test_sgraph_brzozowski() {
    std::cout << "test_sgraph_brzozowski\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    // derivative of re.star(to_re("a")) w.r.t. 'a'
    // d/da (a*) = a*
    expr_ref ch_a(seq.str.mk_char('a'), m);
    expr_ref unit_a(seq.str.mk_unit(ch_a), m);
    expr_ref to_re_a(seq.re.mk_to_re(unit_a), m);
    expr_ref star_a(seq.re.mk_star(to_re_a), m);

    euf::snode* s_star_a = sg.mk(star_a);
    euf::snode* s_unit_a = sg.mk(unit_a);

    euf::snode* deriv = sg.brzozowski_deriv(s_star_a, s_unit_a);
    SASSERT(deriv != nullptr);
    std::cout << "  d/da(a*) kind: " << (int)deriv->kind() << "\n";

    // derivative of re.empty w.r.t. 'a' should be re.empty
    sort_ref re_sort(seq.re.mk_re(str_sort), m);
    expr_ref re_empty(seq.re.mk_empty(re_sort), m);
    euf::snode* s_empty = sg.mk(re_empty);
    euf::snode* deriv_empty = sg.brzozowski_deriv(s_empty, s_unit_a);
    SASSERT(deriv_empty != nullptr);
    SASSERT(deriv_empty->is_fail()); // derivative of empty set is empty set
    std::cout << "  d/da(empty) kind: " << (int)deriv_empty->kind() << "\n";

    sg.display(std::cout);
}

// test minterm computation
static void test_sgraph_minterms() {
    std::cout << "test_sgraph_minterms\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    seq_util seq(m);
    sort_ref str_sort(seq.str.mk_string_sort(), m);

    // simple regex with no character predicates: re.all (.*)
    expr_ref re_all(seq.re.mk_full_seq(str_sort), m);
    euf::snode* s_re_all = sg.mk(re_all);

    euf::snode_vector minterms;
    sg.compute_minterms(s_re_all, minterms);
    // no predicates => single minterm (full_char)
    SASSERT(minterms.size() == 1);
    std::cout << "  re.all minterms: " << minterms.size() << "\n";
}

void tst_euf_sgraph() {
    test_sgraph_classify();
    test_sgraph_regex();
    test_sgraph_re_concat_and_loop();
    test_sgraph_power();
    test_sgraph_push_pop();
    test_sgraph_nested_scopes();
    test_sgraph_find_idempotent();
    test_sgraph_mk_concat();
    test_sgraph_mk_power();
    test_sgraph_first_last();
    test_sgraph_concat_metadata();
    test_sgraph_display();
    test_sgraph_factory();
    test_sgraph_indexing();
    test_sgraph_drop();
    test_sgraph_subst();
    test_sgraph_complex_concat();
    test_sgraph_brzozowski();
    test_sgraph_minterms();
}
