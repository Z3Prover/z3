/*++
Copyright (c) 2026 Microsoft Corporation
--*/

#include "ast/ast_util.h"
#include "ast/arith_decl_plugin.h"
#include "ast/expr_abstract.h"
#include "ast/reg_decl_plugins.h"
#include "parsers/smt2/smt2parser.h"
#include "qe/qsat.h"
#include <cstdint>
#include <cstring>
#include <iterator>
#include <sstream>

static unsigned check_qsat(ast_manager& m, expr* fml, bool expected, bool recursive, bool qel = true) {
    scoped_rlimit limit(m.limit(), 1000000);
    params_ref p;
    p.set_bool("qsat_recursive_backjump", recursive);
    p.set_bool("qsat_use_qel", qel);
    tactic_ref tac = qel ? mk_qsat_tactic(m, p) : mk_qsat_tactic(m);
    if (!qel)
        tac->updt_params(p);
    goal_ref input = alloc(goal, m);
    input->assert_expr(fml);
    goal_ref_buffer result;
    (*tac)(input, result);
    VERIFY(result.size() == 1);
    VERIFY(expected ? result[0]->is_decided_sat() : result[0]->is_decided_unsat());
    statistics st;
    tac->collect_statistics(st);
    for (unsigned i = 0; i < st.size(); ++i)
        if (std::strcmp(st.get_key(i), "qsat recursive projections") == 0)
            return st.get_uint_value(i);
    return 0;
}

static void test_level_cache_lifetime() {
    ast_manager m;
    reg_decl_plugins(m);
    qe::pred_abs abstraction(m);
    app_ref x(m.mk_fresh_const("x", m.mk_bool_sort()), m);
    qe::max_level level;
    level.m_fa = 3;
    abstraction.set_expr_level(x, level);
    app_ref fml(m.mk_not(x), m);
    unsigned refs = fml->get_ref_count();
    VERIFY(abstraction.compute_level(fml) == level);
    VERIFY(fml->get_ref_count() > refs);
    unsigned cached_refs = fml->get_ref_count();
    VERIFY(abstraction.compute_level(fml) == level);
    VERIFY(fml->get_ref_count() == cached_refs);
    abstraction.reset();
    VERIFY(fml->get_ref_count() == refs);
}

static bool qbf_value(uint64_t table, unsigned level, unsigned assignment, bool first_exists) {
    if (level == 6)
        return (table >> assignment) & 1;
    bool lo = qbf_value(table, level + 1, assignment, first_exists);
    bool hi = qbf_value(table, level + 1, assignment | (1u << level), first_exists);
    return ((level % 2 == 0) == first_exists) ? lo || hi : lo && hi;
}

static void test_quantified_signs(unsigned theory) {
    // Independent numeric signs realize exactly the Boolean oracle's valuations.
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    sort* s = theory == 0 ? m.mk_bool_sort() : theory == 1 ? a.mk_real() : a.mk_int();
    unsigned recursive_projections = 0;
    for (unsigned seed = 0; seed < 128; ++seed) {
        unsigned state = seed + 1;
        app_ref_vector vars(m);
        for (unsigned i = 0; i < 6; ++i)
            vars.push_back(m.mk_fresh_const("x", s));
        expr_ref_vector clauses(m);
        uint64_t table = UINT64_MAX;
        for (unsigned c = 0; c < 8; ++c) {
            expr_ref_vector literals(m);
            uint64_t clause_table = 0;
            for (unsigned k = 0; k < 3; ++k) {
                state = 1664525u * state + 1013904223u;
                unsigned var = (state >> 16) % 6;
                bool negated = (state & 1) != 0;
                expr_ref atom(vars[var].get(), m);
                if (theory != 0)
                    atom = a.mk_gt(atom, a.mk_numeral(rational(0), theory == 2));
                literals.push_back(negated ? m.mk_not(atom) : atom.get());
                for (unsigned assignment = 0; assignment < 64; ++assignment)
                    if ((((assignment >> var) & 1) != 0) != negated)
                        clause_table |= uint64_t(1) << assignment;
            }
            clauses.push_back(mk_or(literals));
            table &= clause_table;
        }
        for (bool first_exists : { false, true }) {
            expr_ref fml(mk_and(clauses), m);
            for (unsigned i = vars.size(); i-- > 0;) {
                app* v = vars[i].get();
                fml = ((i % 2 == 0) == first_exists)
                    ? mk_exists(m, 1, &v, fml)
                    : mk_forall(m, 1, &v, fml);
            }
            bool expected = qbf_value(table, 0, 0, first_exists);
            for (bool qel : { false, true }) {
                VERIFY(check_qsat(m, fml, expected, false, qel) == 0);
                recursive_projections += check_qsat(m, fml, expected, true, qel);
            }
        }
    }
    VERIFY(recursive_projections > 0);
}

static void test_arithmetic() {
    char const* formulas[] = {
        "(exists ((x Real)) (forall ((y Real)) (exists ((z Real)) (> z (+ x y)))))",
        "(forall ((x Real)) (exists ((y Real)) (forall ((z Real)) (exists ((w Real)) (= (+ x y) (+ z w))))))",
        "(exists ((x Int)) (forall ((y Int)) (exists ((z Int)) (= z (+ x y)))))",
        "(forall ((a Real) (b Real) (c Real) (d Real)) (= (exists ((x Real)) (and (<= a x) (<= b x) (<= x c) (<= x d))) (and (<= a c) (<= a d) (<= b c) (<= b d))))",
        "(forall ((a Real) (b Real) (c Real) (d Real)) (= (exists ((x Real)) (and (< a x) (<= b x) (< x c) (<= x d))) (and (< a c) (< a d) (< b c) (<= b d))))",
        "(exists ((x Real)) (forall ((y Real)) (exists ((z Real)) (and (> x y) (= z (+ x y))))))",
        "(forall ((x Real)) (exists ((y Real)) (forall ((z Real)) (exists ((w Real)) (and (= (+ x y) (+ z w)) (> z x))))))",
        "(exists ((x Int)) (forall ((y Int)) (exists ((z Int)) (and (> x y) (= z (+ x y))))))",
    };
    for (unsigned i = 0; i < std::size(formulas); ++i) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context ctx(false, &m);
        std::istringstream input(std::string("(assert ") + formulas[i] + ")");
        VERIFY(parse_smt2_commands(ctx, input));
        expr_ref fml(ctx.assertions()[0], m);
        for (bool qel : { false, true }) {
            check_qsat(m, fml, i < 5, false, qel);
            check_qsat(m, fml, i < 5, true, qel);
        }
    }
}

void tst_qsat() {
    test_level_cache_lifetime();
    for (unsigned theory = 0; theory < 3; ++theory)
        test_quantified_signs(theory);
    test_arithmetic();
}
