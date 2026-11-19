/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_lex_facet.cpp (test)

Abstract:

    Unit test for `seq::lex_facet::detect_cycles` (ast/seq/seq_lex_facet.h),
    specifically exercising the egraph-based cycle detection: a strict
    lexicographic-order cycle that only closes *modulo congruence* over
    sequence concatenation (i.e. `x` and `a ++ b` are only known equal
    because `x` was asserted equal to `a ++ b` via `eq_facet`, and `p`
    is only recognized as congruent to `a ++ b` via
    `euf::seq_plugin`'s associative-completion reasoning over
    `(a ++ b) ++ c` vs `a ++ (b ++ c)`), not via any syntactic identity
    that the old (pre-egraph) `detect_cycles` could see directly.

    Also exercises lexicographic completion, character-order adoption,
    regex interaction, and incremental model construction.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/seq/seq_lex_facet.h"
#include "cmd_context/cmd_context.h"
#include "model/model.h"
#include "parsers/smt2/smt2parser.h"
#include "smt/smt_solver.h"
#include "solver/solver.h"
#include <iostream>
#include <sstream>

namespace {

    // Detect a strict lex cycle that closes only after associativity
    // merges `(a ++ b) ++ c` with `a ++ (b ++ c)`.
    static void tst_strict_cycle_modulo_congruence() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();

        expr_ref a(m.mk_fresh_const("a", s), m);
        expr_ref b(m.mk_fresh_const("b", s), m);
        expr_ref c(m.mk_fresh_const("c", s), m);
        expr_ref x(m.mk_fresh_const("x", s), m);
        expr_ref y(m.mk_fresh_const("y", s), m);
        expr_ref z(m.mk_fresh_const("z", s), m);

        // x = (a ++ b) ++ c
        expr_ref ab(u.str.mk_concat(a, b), m);
        expr_ref abc_left(u.str.mk_concat(ab, c), m);
        // z = a ++ (b ++ c)   -- same sequence as x, but only provably
        // so via associativity, not syntactic identity.
        expr_ref bc(u.str.mk_concat(b, c), m);
        expr_ref abc_right(u.str.mk_concat(a, bc), m);

        trail_stack tr;
        seq::eq_tree::dep_manager_t dm;
        seq::eq_facet eqf(tr, m, u, dm);
        seq::deq_facet deqf(tr, m, u, dm);
        seq::lex_facet lexf(tr, m, u, dm);

        unsigned eq_leaf = 1;
        eqf.add_equation(x, abc_left, dm.mk_leaf(eq_leaf));

        // x < y
        {
            expr_ref_vector lhs(m), rhs(m);
            u.str.get_concat_units(x, lhs);
            u.str.get_concat_units(y, rhs);
            lexf.add_lex(lhs, rhs, true);
        }
        // y < z
        {
            expr_ref_vector lhs(m), rhs(m);
            u.str.get_concat_units(y, lhs);
            u.str.get_concat_units(z, rhs);
            lexf.add_lex(lhs, rhs, true);
        }
        // z <= a ++ (b ++ c)
        {
            expr_ref_vector lhs(m), rhs(m);
            u.str.get_concat_units(z, lhs);
            u.str.get_concat_units(abc_right, rhs);
            lexf.add_lex(lhs, rhs, false);
        }
        // Tie z to the associatively equivalent form of x's definition.
        unsigned eq_leaf2 = 2;
        eqf.add_equation(z, abc_right, dm.mk_leaf(eq_leaf2));

        bool conflict = false;
        seq::eq_tree::dep_tracker conflict_dep = nullptr;
        bool changed = lexf.detect_cycles(conflict, conflict_dep, eqf, deqf);

        ENSURE(changed);
        ENSURE(conflict);
        // The justification should include the equations that closed the
        // cycle modulo congruence.
        ENSURE(dm.contains(conflict_dep, eq_leaf));
        ENSURE(dm.contains(conflict_dep, eq_leaf2));
    }

    // Replacing the middle strict edge with `<=` should force equalities
    // instead of reporting a conflict.
    static void tst_non_strict_cycle_forces_equalities() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();

        expr_ref x(m.mk_fresh_const("x", s), m);
        expr_ref y(m.mk_fresh_const("y", s), m);

        trail_stack tr;
        seq::eq_tree::dep_manager_t dm;
        seq::eq_facet eqf(tr, m, u, dm);
        seq::deq_facet deqf(tr, m, u, dm);
        seq::lex_facet lexf(tr, m, u, dm);

        // x <= y, y <= x: a non-strict cycle over two plain variables.
        {
            expr_ref_vector lhs(m), rhs(m);
            u.str.get_concat_units(x, lhs);
            u.str.get_concat_units(y, rhs);
            lexf.add_lex(lhs, rhs, false);
        }
        {
            expr_ref_vector lhs(m), rhs(m);
            u.str.get_concat_units(y, lhs);
            u.str.get_concat_units(x, rhs);
            lexf.add_lex(lhs, rhs, false);
        }

        bool conflict = false;
        seq::eq_tree::dep_tracker conflict_dep = nullptr;
        bool changed = lexf.detect_cycles(conflict, conflict_dep, eqf, deqf);
        ENSURE(changed);
        ENSURE(!conflict);
        ENSURE(lexf.lexs().empty());
        ENSURE(!eqf.equations().empty());
    }

    static void tst_lex_completion() {
        struct test_case {
            char const* input;
            lbool expected;
            bool incremental = false;
        };
        test_case cases[] = {
            { R"(
                (declare-const x String)
                (assert (str.<= "B" x))
                (assert (= (str.len x) 1))
            )", l_true },
            { R"(
                (declare-const x String)
                (assert (str.< "B" x))
                (assert (str.prefixof "B" x))
                (assert (= (str.len x) 2))
            )", l_true },
            { R"(
                (declare-const x String)
                (declare-const y String)
                (assert (str.< x y))
                (assert (= (str.len x) 1))
                (assert (= (str.len y) 1))
            )", l_true },
            { R"(
                (declare-const x String)
                (assert (str.< "B" x))
                (assert (str.prefixof x "B"))
            )", l_false },
            { R"(
                (declare-const x String)
                (assert (not (str.<= "\u{0}" x)))
                (assert (= (str.len x) 1))
            )", l_false },
            { R"(
                (declare-const x String)
                (declare-const y String)
                (assert (str.< x y))
                (assert (str.in_re x (re.range "B" "C")))
                (assert (str.in_re y (re.range "A" "C")))
            )", l_true },
            { R"(
                (declare-const x String)
                (declare-const y String)
                (assert (str.<= x y))
            )", l_true, true },
            { R"(
                (declare-const x String)
                (assert (str.< "AA" x))
                (assert (str.< x "AC"))
                (assert (= (str.len x) 2))
            )", l_true }
        };
        for (auto const& c : cases) {
            ast_manager m;
            reg_decl_plugins(m);
            scoped_rlimit limit(m.limit(), 1000000);
            cmd_context cmd(false, &m);
            std::istringstream input(c.input);
            ENSURE(parse_smt2_commands(cmd, input));
            params_ref p;
            p.set_sym("string_solver", symbol("nseq"));
            p.set_bool("model", true);
            ref<solver> s = mk_smt_solver(m, p, symbol("ALL"));
            expr_ref_vector assertions(m);
            for (expr* assertion : cmd.assertions()) {
                assertions.push_back(assertion);
                s->assert_expr(assertion);
            }
            auto check = [&]() {
                lbool result = s->check_sat(0, nullptr);
                if (result != c.expected)
                    std::cerr << "lex completion failed (" << s->reason_unknown() << "): " << c.input << "\n";
                ENSURE(result == c.expected);
                if (result != l_true)
                    return;
                model_ref md;
                s->get_model(md);
                ENSURE(md);
                for (expr* assertion : assertions)
                    ENSURE(md->is_true(assertion));
            };
            check();
            if (!c.incremental)
                continue;
            seq_util u(m);
            arith_util a(m);
            expr_ref x(m.mk_const(cmd.find_func_decl(symbol("x"))), m);
            expr_ref y(m.mk_const(cmd.find_func_decl(symbol("y"))), m);
            expr_ref len_x(u.str.mk_length(x), m), len_y(u.str.mk_length(y), m);
            expr_ref one(a.mk_int(1), m);
            expr_ref x_length(m.mk_eq(len_x, one), m), y_length(m.mk_eq(len_y, one), m);
            s->push();
            s->assert_expr(x_length);
            s->assert_expr(y_length);
            assertions.push_back(x_length);
            assertions.push_back(y_length);
            check();
            expr_ref equal(m.mk_eq(x, y), m);
            expr_ref different(m.mk_not(equal), m);
            s->push();
            s->assert_expr(different);
            assertions.push_back(different);
            check();
            expr_ref opposite(u.str.mk_lex_le(y, x), m);
            s->push();
            s->assert_expr(opposite);
            ENSURE(s->check_sat(0, nullptr) == l_false);
            s->pop(1);
            check();
            s->pop(1);
            assertions.pop_back();
            check();
            s->pop(1);
            assertions.pop_back();
            assertions.pop_back();
            check();
        }
    }
}

void tst_seq_lex_facet() {
    tst_strict_cycle_modulo_congruence();
    tst_non_strict_cycle_forces_equalities();
    tst_lex_completion();
}
