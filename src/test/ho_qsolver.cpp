/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "ast/reg_decl_plugins.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "smt/smt_context.h"
#include <sstream>

static lbool check_ho_qsolver(char const* input, bool ho_matching) {
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context cmd(false, &m);
    std::istringstream is(input);
    VERIFY(parse_smt2_commands(cmd, is));

    smt_params params;
    params.m_ematching = false;
    params.m_mbqi = false;
    params.m_ho_matching = ho_matching;
    params.m_term_enumeration = true;
    params.m_ho_matching_bound = 100;

    smt::context ctx(m, params);
    for (expr* assertion : cmd.assertions())
        ctx.assert_expr(assertion);
    return ctx.check();
}

void tst_ho_qsolver() {
    // Cantor/Leibniz instance: q(b) != q(a) creates the array-extensionality
    // witness delta(a,b). Matching the quantified clause uses
    // P := lambda z. a(delta(a,b)) = z and X := delta(a,b).
    char const* cantor =
        "(declare-sort U 0)\n"
        "(declare-const a (Array U U))\n"
        "(declare-const b (Array U U))\n"
        "(declare-fun q ((Array U U)) Bool)\n"
        "(assert (forall ((P (Array U Bool)) (X U))\n"
        "  (=> (select P (select a X)) (select P (select b X)))))\n"
        "(assert (q b))\n"
        "(assert (not (q a)))\n";
    VERIFY(l_undef == check_ho_qsolver(cantor, false));
    VERIFY(l_false == check_ho_qsolver(cantor, true));

    char const* reversed =
        "(declare-sort U 0)\n"
        "(declare-const a (Array U U))\n"
        "(declare-const b (Array U U))\n"
        "(declare-fun q ((Array U U)) Bool)\n"
        "(assert (forall ((P (Array U Bool)) (X U))\n"
        "  (=> (select P (select b X)) (select P (select a X)))))\n"
        "(assert (q b))\n"
        "(assert (not (q a)))\n";
    VERIFY(l_false == check_ho_qsolver(reversed, true));

    char const* many_sorted =
        "(declare-sort U 0)\n"
        "(declare-sort V 0)\n"
        "(declare-const a (Array U V))\n"
        "(declare-const b (Array U V))\n"
        "(declare-fun g ((Array U V)) Bool)\n"
        "(assert (forall ((P (Array V Bool)) (X U))\n"
        "  (=> (select P (select a X)) (select P (select b X)))))\n"
        "(assert (g b))\n"
        "(assert (not (g a)))\n";
    VERIFY(l_false == check_ho_qsolver(many_sorted, true));
}
