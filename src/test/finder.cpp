#include "sat/sat_solver.h"
#include "sat/sat_npn3_finder.h"

#include <fstream>
#include <functional>
#include <iostream>

static void _init_solver(sat::solver& s)
{
    s.mk_var();
    s.mk_var();
    s.mk_var();
    s.mk_var();
}

static void _mk_clause4(sat::solver& s, sat::literal const & w, sat::literal const& x, sat::literal const& y, sat::literal const& z)
{
    sat::literal lits[] = {w, x, y, z};
    s.mk_clause(4, lits);
}

template<class CbFn>
static void _check_finder(sat::solver& s, CbFn&& fn, const std::string& name, unsigned head_exp, unsigned a_exp, unsigned b_exp, unsigned c_exp)
{
    using namespace std::placeholders;

    uint32_t found{0u};
    sat::npn3_finder f_npn(s);
    fn(f_npn, [&](sat::literal head, sat::literal a, sat::literal b, sat::literal c) {
        std::cout << "[" << name << "]\n";
        ENSURE(head.to_uint() == head_exp && a.to_uint() == a_exp && b.to_uint() == b_exp && c.to_uint() == c_exp);
        ++found;
    });
    sat::clause_vector clauses(s.clauses());
    f_npn(clauses);
    ENSURE(found == 1u);
}

static void tst_single_mux() {
    reslimit r;
    sat::solver s({}, r);
    _init_solver(s);

    s.mk_clause(sat::literal(0, true), sat::literal(1, true), sat::literal(3, false));
    s.mk_clause(sat::literal(0, true), sat::literal(1, false), sat::literal(3, true));
    s.mk_clause(sat::literal(0, false), sat::literal(2, true), sat::literal(3, false));
    s.mk_clause(sat::literal(0, false), sat::literal(2, false), sat::literal(3, true));

    _check_finder(s, std::mem_fn(&sat::npn3_finder::set_on_mux), "mux", 7, 0, 3, 5);
}

static void tst_single_maj() {
    reslimit r;
    sat::solver s({}, r);
    _init_solver(s);

    s.mk_clause(sat::literal(0, false), sat::literal(1, false), sat::literal(3, true));
    s.mk_clause(sat::literal(0, false), sat::literal(2, false), sat::literal(3, true));
    s.mk_clause(sat::literal(1, false), sat::literal(2, false), sat::literal(3, true));
    s.mk_clause(sat::literal(0, true), sat::literal(1, true), sat::literal(3, false));
    s.mk_clause(sat::literal(0, true), sat::literal(2, true), sat::literal(3, false));
    s.mk_clause(sat::literal(1, true), sat::literal(2, true), sat::literal(3, false));

    _check_finder(s, std::mem_fn(&sat::npn3_finder::set_on_maj), "maj", 6, 0, 2, 4);
}

static void tst_single_orand() {
    reslimit r;
    sat::solver s({}, r);
    _init_solver(s);

    s.mk_clause(sat::literal(0, false), sat::literal(3, true));
    s.mk_clause(sat::literal(1, false), sat::literal(2, false), sat::literal(3, true));
    s.mk_clause(sat::literal(0, true), sat::literal(1, true), sat::literal(3, false));
    s.mk_clause(sat::literal(0, true), sat::literal(2, true), sat::literal(3, false));

    _check_finder(s, std::mem_fn(&sat::npn3_finder::set_on_orand), "orand", 6, 0, 2, 4);
}

static void tst_single_and() {
    reslimit r;
    sat::solver s({}, r);
    _init_solver(s);

    sat::literal ls1[] = {sat::literal(0, true), sat::literal(1, true), sat::literal(2, true), sat::literal(3, false)};
    s.mk_clause(4, ls1);
    s.mk_clause(sat::literal(0, false), sat::literal(3, true));
    s.mk_clause(sat::literal(1, false), sat::literal(3, true));
    s.mk_clause(sat::literal(2, false), sat::literal(3, true));

    _check_finder(s, std::mem_fn(&sat::npn3_finder::set_on_and), "and", 6, 0, 2, 4);
}

static void tst_single_xor() {
    reslimit r;
    sat::solver s({}, r);
    _init_solver(s);

    _mk_clause4(s, sat::literal(0, true), sat::literal(1, false), sat::literal(2, false), sat::literal(3, false));
    _mk_clause4(s, sat::literal(0, false), sat::literal(1, true), sat::literal(2, false), sat::literal(3, false));
    _mk_clause4(s, sat::literal(0, false), sat::literal(1, false), sat::literal(2, true), sat::literal(3, false));
    _mk_clause4(s, sat::literal(0, false), sat::literal(1, false), sat::literal(2, false), sat::literal(3, true));
    _mk_clause4(s, sat::literal(0, false), sat::literal(1, true), sat::literal(2, true), sat::literal(3, true));
    _mk_clause4(s, sat::literal(0, true), sat::literal(1, false), sat::literal(2, true), sat::literal(3, true));
    _mk_clause4(s, sat::literal(0, true), sat::literal(1, true), sat::literal(2, false), sat::literal(3, true));
    _mk_clause4(s, sat::literal(0, true), sat::literal(1, true), sat::literal(2, true), sat::literal(3, false));

    _check_finder(s, std::mem_fn(&sat::npn3_finder::set_on_xor), "xor", 1, 3, 4, 6);
}

static void tst_single_andxor() {
    reslimit r;
    sat::solver s({}, r);
    _init_solver(s);

    s.mk_clause(sat::literal(0, true), sat::literal(1, false), sat::literal(3, true));
    s.mk_clause(sat::literal(0, true), sat::literal(2, false), sat::literal(3, true));
    _mk_clause4(s, sat::literal(0, true), sat::literal(1, true), sat::literal(2, true), sat::literal(3, false));
    s.mk_clause(sat::literal(0, false), sat::literal(1, false), sat::literal(3, false));
    s.mk_clause(sat::literal(0, false), sat::literal(2, false), sat::literal(3, false));
    _mk_clause4(s, sat::literal(0, false), sat::literal(1, true), sat::literal(2, true), sat::literal(3, true));

    _check_finder(s, std::mem_fn(&sat::npn3_finder::set_on_andxor), "andxor", 0, 6, 2, 4);
}

static void tst_single_xorand() {
    reslimit r;
    sat::solver s({}, r);
    _init_solver(s);

    s.mk_clause(sat::literal(0, false), sat::literal(3, true));
    s.mk_clause(sat::literal(1, false), sat::literal(2, false), sat::literal(3, true));
    s.mk_clause(sat::literal(1, true), sat::literal(2, true), sat::literal(3, true));
    _mk_clause4(s, sat::literal(0, true), sat::literal(1, true), sat::literal(2, false), sat::literal(3, false));
    _mk_clause4(s, sat::literal(0, true), sat::literal(1, false), sat::literal(2, true), sat::literal(3, false));

    _check_finder(s, std::mem_fn(&sat::npn3_finder::set_on_xorand), "xorand", 6, 0, 3, 5);
}

static void tst_single_gamble() {
    reslimit r;
    sat::solver s({}, r);
    _init_solver(s);

    s.mk_clause(sat::literal(0, true), sat::literal(1, false), sat::literal(3, true));
    s.mk_clause(sat::literal(1, true), sat::literal(2, false), sat::literal(3, true));
    s.mk_clause(sat::literal(0, false), sat::literal(2, true), sat::literal(3, true));
    _mk_clause4(s, sat::literal(0, false), sat::literal(1, false), sat::literal(2, false), sat::literal(3, false));
    _mk_clause4(s, sat::literal(0, true), sat::literal(1, true), sat::literal(2, true), sat::literal(3, false));

    _check_finder(s, std::mem_fn(&sat::npn3_finder::set_on_gamble), "gamble", 6, 0, 2, 4);
}

static void tst_single_onehot() {
    reslimit r;
    sat::solver s({}, r);
    _init_solver(s);

    s.mk_clause(sat::literal(0, true), sat::literal(1, true), sat::literal(3, true));
    s.mk_clause(sat::literal(0, true), sat::literal(2, true), sat::literal(3, true));
    s.mk_clause(sat::literal(1, true), sat::literal(2, true), sat::literal(3, true));
    _mk_clause4(s, sat::literal(0, false), sat::literal(1, false), sat::literal(2, false), sat::literal(3, true));
    _mk_clause4(s, sat::literal(0, true), sat::literal(1, false), sat::literal(2, false), sat::literal(3, false));
    _mk_clause4(s, sat::literal(0, false), sat::literal(1, true), sat::literal(2, false), sat::literal(3, false));
    _mk_clause4(s, sat::literal(0, false), sat::literal(1, false), sat::literal(2, true), sat::literal(3, false));

    _check_finder(s, std::mem_fn(&sat::npn3_finder::set_on_onehot), "onehot", 6, 0, 2, 4);
}

static void tst_single_dot() {
    reslimit r;
    sat::solver s({}, r);
    _init_solver(s);

    s.mk_clause(sat::literal(0, false), sat::literal(2, false), sat::literal(3, true));
    s.mk_clause(sat::literal(0, true), sat::literal(1, true), sat::literal(3, true));
    s.mk_clause(sat::literal(0, true), sat::literal(2, true), sat::literal(3, true));
    s.mk_clause(sat::literal(0, false), sat::literal(2, true), sat::literal(3, false));
    _mk_clause4(s, sat::literal(0, true), sat::literal(1, false), sat::literal(2, false), sat::literal(3, false));

    _check_finder(s, std::mem_fn(&sat::npn3_finder::set_on_dot), "dot", 6, 0, 2, 4);
}

void tst_finder() {
    tst_single_mux();
    tst_single_maj();
    tst_single_orand();
    tst_single_and();
    tst_single_xor();
    tst_single_andxor();
    tst_single_xorand();
    tst_single_gamble();
    tst_single_onehot();
    tst_single_dot();
}
