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

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/seq/seq_lex_facet.h"
#include <iostream>

namespace {

    // x < y, y < z, z <= x, where x is asserted (via eq_facet) equal to
    // `a ++ b ++ c`, and z is asserted equal to `a ++ (b ++ c)` - the
    // same sequence, but only recognized as such via seq_plugin's
    // associative-completion reasoning, not by syntactic identity with
    // x's defining term. This closes a strict cycle x < y < z <= x,
    // which is only detectable once the egraph has merged x and z's
    // defining terms into the same equivalence class.
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
        // z <= (a ++ (b ++ c))   -- registers z's token-concat node, and
        // (via seq_plugin's completion) puts z's side of this edge into
        // the same equivalence class as x's defining term abc_left.
        {
            expr_ref_vector lhs(m), rhs(m);
            u.str.get_concat_units(z, lhs);
            u.str.get_concat_units(abc_right, rhs);
            lexf.add_lex(lhs, rhs, false);
        }
        // Tie z to x: assert z == a ++ (b ++ c) is not enough by itself
        // to close the cycle back to x syntactically - x's defining
        // term is `(a ++ b) ++ c`, a *different* (but associatively
        // equal) parse. Register that additional equation so the loop
        // z <= abc_right ~ abc_left = x closes.
        unsigned eq_leaf2 = 2;
        eqf.add_equation(z, abc_right, dm.mk_leaf(eq_leaf2));

        bool conflict = false;
        seq::eq_tree::dep_tracker conflict_dep = nullptr;
        bool changed = lexf.detect_cycles(conflict, conflict_dep, eqf, deqf);

        ENSURE(changed);
        ENSURE(conflict);
        // The conflict's justification must include the two equations
        // that established the congruence closing the cycle (x's and
        // z's ties to their respective associative parses of a++b++c),
        // not just the lex obligations' own (trivial, nullptr) deps.
        ENSURE(dm.contains(conflict_dep, eq_leaf));
        ENSURE(dm.contains(conflict_dep, eq_leaf2));
    }

    // Sanity check: the same three obligations but with the middle edge
    // relaxed to `<=` (no strict edge on the cycle) does not report a
    // conflict; instead the cycle's variables are forced pairwise equal
    // and folded into eq_facet.
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
}

void tst_seq_lex_facet() {
    tst_strict_cycle_modulo_congruence();
    tst_non_strict_cycle_forces_equalities();
}
