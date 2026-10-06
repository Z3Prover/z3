/*++
Copyright (c) 2026 Romain Soulat

    Shared-DAG finite-field domain preservation tests.
--*/
#include "ast/reg_decl_plugins.h"
#include "ast/simplifiers/ff_domain_analysis.h"
#include "util/debug.h"

static void domain_analysis_contract() {
    ast_manager m;
    reg_decl_plugins(m);
    ff_util ff(m);
    for (unsigned prime : {2u, 7u, 101u}) {
        sort_ref field(ff.mk_sort(rational(prime)), m);
        expr_ref x(m.mk_const("domain-x", field), m), y(m.mk_const("domain-y", field), m);
        expr_ref zero(ff.mk_numeral(rational(0), field), m), one(ff.mk_numeral(rational(1), field), m);
        expr_ref square(ff.mk_mul(x, x), m);
        ff_domain_analysis analysis(m);
        ENSURE(analysis.variable(m.mk_eq(square, x)) == x);
        ENSURE(!analysis.variable(m.mk_eq(square, y)));
        ENSURE(!analysis.variable(m.mk_eq(ff.mk_mul(square, x), x)));
        ENSURE(analysis.variable(m.mk_eq(ff.mk_mul(x, ff.mk_add(x, ff.mk_neg(one))), zero)) == x);
        // An identically-zero quadratic still matches the preservation heuristic.
        ENSURE(analysis.variable(m.mk_eq(square, square)) == x);
        // Foreign arguments must not become polynomial variables.
        sort* args[] = {m.mk_bool_sort()};
        func_decl_ref f(m.mk_func_decl(symbol("domain-f"), 1, args, field), m);
        expr_ref foreign(m.mk_app(f, m.mk_true()), m);
        ENSURE(analysis.variable(m.mk_eq(ff.mk_mul(foreign, foreign), foreign)) == foreign);
        // Cache lifetime is independent of temporary assertions and variables
        // from an earlier query. Negative results cannot poison later roots.
        for (unsigned i = 0; i < 100; ++i) {
            expr_ref fresh(m.mk_fresh_const("domain-fresh", field), m);
            ENSURE(!analysis.variable(m.mk_eq(square, fresh)));
            ENSURE(analysis.variable(m.mk_eq(square, x)) == x);
        }
        // Many assertions share a long DAG. Re-analysis must cost only the new
        // roots, not another walk over the shared thousand-node subexpression.
        expr_ref shared(square, m);
        for (unsigned i = 0; i < 1000; ++i)
            shared = ff.mk_add(shared, zero);
        ENSURE(analysis.variable(m.mk_eq(shared, x)) == x);
        auto before = m.limit().count();
        for (unsigned i = 0; i < 1000; ++i) {
            expr_ref c(ff.mk_numeral(rational(i % prime), field), m);
            expr_ref lhs(ff.mk_add(shared, c), m), rhs(ff.mk_add(x, c), m);
            ENSURE(analysis.variable(m.mk_eq(lhs, rhs)) == x);
        }
        ENSURE(m.limit().count() - before < 10000);
        m.limit().inc_cancel();
        bool canceled = false;
        try { analysis.variable(m.mk_eq(square, x)); }
        catch (rewriter_exception const&) { canceled = true; }
        m.limit().dec_cancel();
        ENSURE(canceled);
        ENSURE(analysis.variable(m.mk_eq(square, x)) == x);
    }
}

void tst_ff_domain() {
    domain_analysis_contract();
}
