/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ho_facet.cpp

Abstract:

    Unit tests for seq::ho_facet.

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/seq/seq_ho_facet.h"
#include <iostream>

void tst_seq_ho_facet() {
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
        [](expr*, expr*) { return false; },
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
