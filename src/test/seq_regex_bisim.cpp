/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "ast/rewriter/seq_regex_bisim.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/reg_decl_plugins.h"
#include "util/debug.h"

static expr_ref mk_regex_literal(ast_manager& m, seq_util& seq, char const* s) {
    return expr_ref(seq.re.mk_to_re(seq.str.mk_string(zstring(s))), m);
}

static void test_step_bound_accounts_for_leaf_traversal() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_rewriter rw(m);
    seq_util seq(m);

    expr_ref re_a = mk_regex_literal(m, seq, "a");
    expr_ref re_b = mk_regex_literal(m, seq, "b");
    expr_ref re_c = mk_regex_literal(m, seq, "c");

    expr_ref left(seq.re.mk_union(re_a, re_b), m);
    expr_ref right(seq.re.mk_union(re_a, re_c), m);

    seq::regex_bisim bisim(rw);
    ENSURE(bisim.are_equivalent(left, right) == l_false);

    bisim.set_step_bound(1);
    ENSURE(bisim.are_equivalent(left, right) == l_undef);
}

void tst_seq_regex_bisim() {
    test_step_bound_accounts_for_leaf_traversal();
}
