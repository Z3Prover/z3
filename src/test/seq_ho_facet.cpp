/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ho_facet.cpp

Abstract:

    Unit tests for seq::ho_facet.

--*/
#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/seq/seq_ho_facet.h"
#include <iostream>

static void tst_unfolded_obligations() {
    ast_manager m;
    reg_decl_plugins(m);
    trail_stack trail;
    seq_util seq(m);
    arith_util arith(m);
    array_util arrays(m);
    seq_rewriter rewriter(m);
    sort* integers = arith.mk_int();
    sort* booleans = m.mk_bool_sort();
    sort_ref function_sort(arrays.mk_array_sort(integers, booleans), m);
    sort_ref sequence_sort(seq.str.mk_seq(integers), m);
    expr_ref function(m.mk_fresh_const("f", function_sort), m);
    expr_ref sequence(m.mk_fresh_const("s", sequence_sort), m);
    expr_ref mapped(seq.str.mk_map(function, sequence), m);
    expr_ref zero(arith.mk_int(0), m);
    expr_ref unit(seq.str.mk_unit(zero), m);
    expr_ref_vector equalities(m);
    bool elaborate = false;
    seq::ho_facet facet(
        trail, m, seq, rewriter,
        [&](expr* lhs, expr* rhs, expr* premise) {
            expr_ref equality(m.mk_eq(lhs, rhs), m);
            if (premise)
                equality = m.mk_implies(premise, equality);
            if (equalities.contains(equality))
                return false;
            equalities.push_back(equality);
            return true;
        },
        [&](expr* input, expr*& output) {
            output = elaborate && input == sequence ? unit.get() : nullptr;
            return output != nullptr;
        });
    facet.add_term(mapped);
    ENSURE(facet.propagate());
    ENSURE(!facet.is_satisfied());
    trail.push_scope();
    elaborate = true;
    ENSURE(facet.propagate());
    ENSURE(facet.is_satisfied());
    {
        trail_stack clone_trail;
        scoped_ptr<stx::facet_i> clone(facet.clone(clone_trail));
        ENSURE(clone->is_satisfied());
    }
    trail.pop_scope(1);
    elaborate = false;
    ENSURE(!facet.is_satisfied());
    ENSURE(!facet.propagate());
    elaborate = true;
    ENSURE(facet.propagate());
    ENSURE(facet.is_satisfied());
    ENSURE(!facet.propagate());

    expr_ref empty_map(seq.str.mk_map(function, seq.str.mk_empty(sequence_sort)), m);
    seq::ho_facet structural_facet(
        trail, m, seq, rewriter,
        [&](expr* lhs, expr* rhs, expr* premise) {
            ENSURE(!premise);
            return true;
        },
        [](expr*, expr*&){ return false; });
    structural_facet.add_term(empty_map);
    ENSURE(structural_facet.propagate());
    ENSURE(structural_facet.is_satisfied());
}

void tst_seq_ho_facet() {
    tst_unfolded_obligations();
    ast_manager m;
    reg_decl_plugins(m);
    trail_stack trail;
    seq_util seq(m);
    seq_rewriter rewriter(m);
    seq::ho_facet facet(
        trail,
        m,
        seq,
        rewriter,
        [](expr*, expr*, expr*) { return false; },
        [](expr*, expr*&) { return false; });
    app* term = m.mk_true();

    trail.push_scope();
    facet.add_term(term);
    ENSURE(facet.terms().size() == 1);

    trail_stack clone_trail;
    scoped_ptr<stx::facet_i> clone(facet.clone(clone_trail));
    ENSURE(static_cast<seq::ho_facet*>(clone.get())->terms().size() == 1);

    trail.pop_scope(1);
    ENSURE(facet.terms().empty());
    facet.add_term(term);
    ENSURE(facet.terms().size() == 1);

    std::cout << "seq_ho_facet: all tests passed\n";
}
