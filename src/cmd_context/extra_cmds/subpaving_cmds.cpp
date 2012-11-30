/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_cmds.cpp

Abstract:
    Commands for debugging subpaving module.

Author:

    Leonardo (leonardo) 2012-08-09

Notes:

--*/
#include<sstream>
#include"cmd_context.h"
#include"cmd_util.h"
#include"expr2subpaving.h"
#include"th_rewriter.h"
#include"ast_smt2_pp.h"
#include"expr2var.h"

static void to_subpaving(cmd_context & ctx, expr * t) {
    ast_manager & m = ctx.m();
    unsynch_mpq_manager qm;
    scoped_ptr<subpaving::context> s;
    s = subpaving::mk_mpq_context(qm);
    expr2var e2v(m);
    expr2subpaving e2s(m, *s, &e2v);
    params_ref p;
    p.set_bool("mul_to_power", true);
    th_rewriter simp(m, p);
    expr_ref t_s(m);
    simp(t, t_s);
    scoped_mpz n(qm), d(qm);
    ctx.regular_stream() << mk_ismt2_pp(t_s, m) << "\n=======>" << std::endl;
    subpaving::var x = e2s.internalize_term(t_s, n, d);
    expr2var::iterator it  = e2v.begin();
    expr2var::iterator end = e2v.end();
    for (; it != end; ++it) {
        ctx.regular_stream() << "x" << it->m_value << " := " << mk_ismt2_pp(it->m_key, m) << "\n";
    }
    s->display_constraints(ctx.regular_stream());
    ctx.regular_stream() << n << "/" << d << " x" << x << "\n";
}

UNARY_CMD(to_subpaving_cmd, "to-subpaving", "<expr>", "internalize expression into subpaving module", CPK_EXPR, expr *, to_subpaving(ctx, arg););

void install_subpaving_cmds(cmd_context & ctx) {
#ifndef _EXTERNAL_RELEASE
    ctx.insert(alloc(to_subpaving_cmd));
#endif
}
