/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    flatten_clauses.cpp

Abstract:

    Tests for asserted_formulas::flatten_clauses.

    A conjunction that is a disjunct of a single clause is distributed into
    binary clauses. A conjunction that is shared, with another clause of the
    same check-sat call or with an assertion of an earlier one, keeps a single
    literal instead of having its conjuncts copied into every clause.

--*/

#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"
#include "params/smt_params.h"
#include "smt/smt_kernel.h"
#include "util/statistics.h"
#include <cstring>
#include <string>

namespace {

    unsigned get_stat(smt::kernel const& s, char const* key) {
        statistics st;
        s.collect_statistics(st);
        for (unsigned i = 0; i < st.size(); ++i)
            if (st.is_uint(i) && strcmp(st.get_key(i), key) == 0)
                return st.get_uint_value(i);
        return 0;
    }

    unsigned num_clauses(smt::kernel const& s) {
        return get_stat(s, "mk clause") + get_stat(s, "mk clause binary");
    }

    expr_ref mk_bool(ast_manager& m, char const* prefix, unsigned i) {
        std::string name = std::string(prefix) + std::to_string(i);
        return expr_ref(m.mk_const(symbol(name.c_str()), m.mk_bool_sort()), m);
    }

    expr_ref mk_conjunction(ast_manager& m, char const* prefix, unsigned n) {
        expr_ref_vector bs(m);
        for (unsigned i = 0; i < n; ++i)
            bs.push_back(mk_bool(m, prefix, i));
        return expr_ref(m.mk_and(bs), m);
    }

    // (> name_i 0) for a fresh real constant
    expr_ref mk_positive(ast_manager& m, char const* prefix, unsigned i) {
        arith_util a(m);
        std::string name = std::string(prefix) + std::to_string(i);
        expr_ref x(m.mk_const(symbol(name.c_str()), a.mk_real()), m);
        return expr_ref(a.mk_gt(x, a.mk_numeral(rational(0), false)), m);
    }

    // (or g C) with a single occurrence of the conjunction C: C is distributed and
    // gets no Boolean variable of its own. The assertion and the conjunction stay
    // alive during check(), as they do for the SMT-LIB front end and API clients.
    // C is written as (and b0 .. b7) and as (not (or (not b0) .. (not b7))).
    void test_unshared_is_distributed(bool negated_disjunction) {
        ast_manager m;
        reg_decl_plugins(m);
        smt_params p;
        smt::kernel s(m, p);
        unsigned n = 8;
        expr_ref c = mk_conjunction(m, "b", n);
        if (negated_disjunction) {
            expr_ref_vector ns(m);
            for (expr* b : *to_app(c))
                ns.push_back(m.mk_not(b));
            c = m.mk_not(m.mk_or(ns));
        }
        expr_ref f(m.mk_or(mk_positive(m, "g", 0), c), m);
        s.assert_expr(f);
        VERIFY(l_true == s.check());
        VERIFY(get_stat(s, "mk bool var") == n + 1);
    }

    // (or (and a1 .. an) (and b1 .. bm)) produces O(n + m) clauses, not n * m.
    void test_two_conjunctions() {
        ast_manager m;
        reg_decl_plugins(m);
        smt_params p;
        smt::kernel s(m, p);
        unsigned n = 100;
        s.assert_expr(m.mk_or(mk_conjunction(m, "a", n), mk_conjunction(m, "b", n)));
        VERIFY(l_true == s.check());
        VERIFY(num_clauses(s) <= 2 * (n + n) + 2);
    }

    // The conjunction C has a literal after the first check-sat because it is
    // shared by the two clauses that (ite C x y) is split into. The later
    // assertions (or g_k C) reuse that literal: O(n + k) clauses, not n * k.
    // Checked with a theory atom and with a Boolean constant as the other disjunct.
    void test_incremental_shared(bool bool_guard) {
        ast_manager m;
        reg_decl_plugins(m);
        smt_params p;
        smt::kernel s(m, p);
        unsigned n = 64, k = 16;
        expr_ref c = mk_conjunction(m, "b", n);
        s.assert_expr(m.mk_ite(c, mk_positive(m, "x", 0), mk_positive(m, "y", 0)));
        VERIFY(l_true == s.check());
        for (unsigned i = 0; i < k; ++i) {
            expr_ref g = bool_guard ? mk_bool(m, "p", i) : mk_positive(m, "g", i);
            s.assert_expr(m.mk_or(g, c));
            VERIFY(l_true == s.check());
        }
        VERIFY(num_clauses(s) <= 2 * (n + k) + 8);
    }
}

void tst_flatten_clauses() {
    test_unshared_is_distributed(false);
    test_unshared_is_distributed(true);
    test_two_conjunctions();
    test_incremental_shared(false);
    test_incremental_shared(true);
}
