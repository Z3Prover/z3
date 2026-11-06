/*++
Copyright (c) 2026 Microsoft Corporation

Regression tests for interruptible sequence solving (issue #11271).
--*/

#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/seq/seq_axioms.h"
#include "smt/smt_context.h"
#include "util/rlimit.h"
#include <cstring>

static unsigned get_stat(smt::context& ctx, char const* key) {
    statistics st;
    ctx.collect_statistics(st);
    for (unsigned i = 0; i < st.size(); ++i)
        if (st.is_uint(i) && !strcmp(st.get_key(i), key))
            return st.get_uint_value(i);
    return 0;
}

static void check_at_expansion() {
    for (char const* index : {"3", "1024", "1025", "1000000000", "4294967295", "4294967296"}) {
        ast_manager m;
        reg_decl_plugins(m);
        th_rewriter rw(m);
        seq_util seq(m);
        arith_util a(m);
        seq::axioms ax(rw);
        expr_ref_vector clauses(m);
        std::function<void(expr_ref_vector const&)> add_clause = [&](expr_ref_vector const& clause) {
            clauses.append(clause);
        };
        std::function<void(expr*)> set_phase = [](expr*) {};
        ax.set_add_clause(add_clause);
        ax.set_phase(set_phase);
        sort_ref seq_int(seq.str.mk_seq(a.mk_int()), m);
        expr_ref s(m.mk_const("s", seq_int), m);
        rational k(index);
        expr_ref at(seq.str.mk_at(s, a.mk_numeral(k, true)), m);
        ax.at_axiom(at);
        ENSURE(!clauses.empty());
        if (k > 1024) {
            ENSURE(m.get_num_asts() < 1000);
        }
        else if (k == 1024) {
            ENSURE(m.get_num_asts() > 1024);
        }
    }
}

static void check_propagation_recovery() {
    struct propagation_context : smt::context {
        using smt::context::context;
        using smt::context::propagate;
    };
    for (bool cancel : {false, true}) {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util seq(m);
        arith_util a(m);
        smt_params params;
        propagation_context ctx(m, params);
        sort_ref seq_int(seq.str.mk_seq(a.mk_int()), m);
        expr_ref x(m.mk_const("x", seq_int), m);
        expr_ref y(m.mk_const("y", seq_int), m);
        expr_ref unit(seq.str.mk_unit(a.mk_int(1)), m);
        expr_ref rhs(seq.str.mk_concat(unit, y), m);
        expr_ref eq(m.mk_eq(x, rhs), m);
        expr_ref empty(seq.str.mk_empty(seq_int), m);
        ctx.push();
        ENSURE(ctx.at_base_level());
        ctx.internalize(eq, false);
        ctx.mark_as_relevant(eq.get());
        ctx.assign(ctx.get_literal(eq), smt::b_justification::mk_axiom());
        {
            scoped_rlimit limit(m.limit(), cancel ? 0 : 1);
            if (cancel)
                m.limit().cancel();
            ENSURE(ctx.propagate());
            // Equality callbacks finish eagerly in the cancellation-suspended phase.
            ENSURE(get_stat(ctx, "seq num reductions") > 0);
        }
        ENSURE(ctx.propagate());
        ENSURE(ctx.check() == l_true);
        ctx.push();
        ctx.assert_expr(m.mk_eq(x, empty));
        ENSURE(ctx.check() == l_false);
        ctx.pop(1);
        ENSURE(ctx.check() == l_true);
        ctx.pop(1);
        ENSURE(ctx.check() == l_true);
    }
}

static void check_fixed_length_recovery() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util seq(m);
    arith_util a(m);
    smt_params params;
    smt::context ctx(m, params);
    sort_ref seq_int(seq.str.mk_seq(a.mk_int()), m);
    expr_ref x(m.mk_const("x", seq_int), m);
    expr_ref length(seq.str.mk_length(x), m);
    expr_ref size(a.mk_int(64), m);
    ctx.assert_expr(m.mk_eq(length, size));
    unsigned before = m.get_num_asts();
    {
        scoped_rlimit limit(m.limit(), 500);
        ENSURE(ctx.check() == l_undef);
        ENSURE(m.limit().is_canceled());
        ENSURE(m.get_num_asts() - before < 20000);
    }
    ENSURE(get_stat(ctx, "seq fixed length") == 0);
    ENSURE(ctx.check() == l_true);
    ENSURE(get_stat(ctx, "seq fixed length") > 0);
    ctx.push();
    ctx.assert_expr(m.mk_eq(x, seq.str.mk_empty(seq_int)));
    ENSURE(ctx.check() == l_false);
    ctx.pop(1);
    ENSURE(ctx.check() == l_true);
}

static void check_eager_reduction_recovery() {
    struct propagation_context : smt::context {
        using smt::context::context;
        using smt::context::propagate;
    };
    ast_manager m;
    reg_decl_plugins(m);
    seq_util seq(m);
    arith_util a(m);
    smt_params params;
    propagation_context ctx(m, params);
    sort_ref seq_int(seq.str.mk_seq(a.mk_int()), m);
    expr_ref last(m);
    ctx.push();
    unsigned count = 2048;
    for (unsigned i = 0; i < count; ++i) {
        expr_ref x(m.mk_fresh_const("x", seq_int), m);
        expr_ref y(m.mk_fresh_const("y", seq_int), m);
        expr_ref unit(seq.str.mk_unit(a.mk_int(i)), m);
        expr_ref rhs(seq.str.mk_concat(unit, y), m);
        expr_ref eq(m.mk_eq(x, rhs), m);
        ctx.internalize(eq, false);
        ctx.mark_as_relevant(eq.get());
        ctx.assign(ctx.get_literal(eq), smt::b_justification::mk_axiom());
        last = x;
    }
    {
        scoped_rlimit limit(m.limit(), 1);
        ENSURE(ctx.propagate());
        ENSURE(m.limit().is_canceled());
        unsigned reductions = get_stat(ctx, "seq num reductions");
        ENSURE(reductions > 0 && reductions < count);
    }
    ENSURE(ctx.propagate());
    ENSURE(get_stat(ctx, "seq num reductions") == count);
    ENSURE(ctx.check() == l_true);
    ctx.push();
    ctx.assert_expr(m.mk_eq(last, seq.str.mk_empty(seq_int)));
    ENSURE(ctx.check() == l_false);
    ctx.pop(1);
    ENSURE(ctx.check() == l_true);
    ctx.pop(1);
    ENSURE(ctx.check() == l_true);
}

static void check_normalization_recovery(bool cancel) {
    struct propagation_context : smt::context {
        using smt::context::context;
        using smt::context::propagate;
    };
    ast_manager m;
    reg_decl_plugins(m);
    seq_util seq(m);
    arith_util a(m);
    smt_params params;
    propagation_context ctx(m, params);
    sort_ref seq_int(seq.str.mk_seq(a.mk_int()), m);
    expr_ref x(m.mk_const("x", seq_int), m);
    expr_ref_vector units(m);
    for (unsigned i = 0; i < 512; ++i)
        units.push_back(seq.str.mk_unit(a.mk_int(i)));
    expr_ref rhs(seq.str.mk_concat(units, seq_int), m);
    expr_ref eq(m.mk_eq(x, rhs), m);
    ctx.push();
    ctx.internalize(eq, false);
    ctx.mark_as_relevant(eq.get());
    ctx.assign(ctx.get_literal(eq), smt::b_justification::mk_axiom());
    {
        scoped_rlimit limit(m.limit(), cancel ? 0 : 1);
        if (cancel)
            m.limit().cancel();
        ENSURE(ctx.propagate());
        ENSURE(m.limit().is_canceled());
        ENSURE(get_stat(ctx, "seq num reductions") == 0);
    }
    ENSURE(ctx.propagate());
    ENSURE(get_stat(ctx, "seq num reductions") > 0);
    ENSURE(ctx.check() == l_true);
    ctx.push();
    ctx.assert_expr(m.mk_eq(x, seq.str.mk_empty(seq_int)));
    ENSURE(ctx.check() == l_false);
    ctx.pop(1);
    ENSURE(ctx.check() == l_true);
    ctx.pop(1);
    ENSURE(ctx.check() == l_true);
}

void tst_seq_limits() {
    check_at_expansion();
    check_propagation_recovery();
    check_fixed_length_recovery();
    check_eager_reduction_recovery();
    for (bool cancel : {false, true})
        check_normalization_recovery(cancel);
}
