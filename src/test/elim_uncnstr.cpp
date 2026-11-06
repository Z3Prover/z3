/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "ast/ast_translation.h"
#include "ast/reg_decl_plugins.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/portfolio/default_tactic.h"
#include <sstream>

namespace {
    void check_rewrite(char const* input, bool changed, bool freeze = false, bool translate = false) {
        ast_manager m;
        ast_manager other;
        reg_decl_plugins(m);
        reg_decl_plugins(other);
        cmd_context ctx(false, &m);
        std::istringstream stream(input);
        ENSURE(parse_smt2_commands(ctx, stream));
        goal_ref g = alloc(goal, m);
        expr_ref_vector original(m);
        original.append(ctx.assertions().size(), ctx.assertions().data());
        for (expr* f : original)
            g->assert_expr(f);
        tactic_ref t = mk_elim_uncnstr_seq_concat_tactic(m);
        if (freeze) {
            expr* concat = to_app(original.get(0))->get_arg(1);
            t->user_propagate_register_expr(to_app(concat)->get_arg(0));
        }
        if (translate) {
            ast_translation tr(m, other);
            g = g->translate(tr);
            t = t->translate(other);
        }
        expr_ref_vector before(g->m());
        g->get_formulas(before);
        goal_ref_buffer result;
        (*t)(g, result);
        ENSURE(result.size() == 1 && result[0]->size() == before.size());
        bool modified = false;
        for (unsigned i = 0; i < before.size(); ++i)
            modified |= before[i] != result[0]->form(i);
        ENSURE(modified == changed);
        if (changed)
            for (unsigned i = 1; i < before.size(); ++i)
                ENSURE(before[i] == result[0]->form(i));
    }

    void check_model(char const* input, bool proofs = false) {
        ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
        reg_decl_plugins(m);
        cmd_context ctx(false, &m);
        std::istringstream stream(input);
        ENSURE(parse_smt2_commands(ctx, stream));
        goal_ref g = alloc(goal, m, proofs, true, false);
        for (expr* f : ctx.assertions())
            g->assert_expr(f);
        tactic_ref t = mk_default_tactic(m);
        model_ref md;
        labels_vec labels;
        proof_ref pr(m);
        expr_dependency_ref core(m);
        std::string reason;
        lbool result = check_sat(*t, g, md, labels, pr, core, reason);
        if (proofs) {
            ENSURE(result == l_false && pr);
        }
        else {
            ENSURE(result == l_true && md);
            md->set_model_completion(true);
            for (expr* f : ctx.assertions())
                ENSURE(md->is_true(f));
        }
    }
}

void tst_elim_uncnstr() {
    char const* definition = R"(
        (declare-const x String)
        (declare-const a String)
        (declare-const b String)
        (assert (= x (str.++ a b)))
    )";
    check_rewrite(definition, true);
    check_rewrite(definition, false, true);
    check_rewrite(definition, true, false, true);
    check_rewrite(R"(
        (declare-const p Int)
        (declare-const q Int)
        (assert (> (+ p q) 1))
    )", false, false, true);
    check_rewrite(R"(
        (declare-const x String)
        (declare-const a String)
        (declare-const b String)
        (declare-const p Int)
        (declare-const q Int)
        (assert (= x (str.++ a b)))
        (assert (> (+ p q) 1))
    )", true);
    check_rewrite(R"(
        (declare-const x String)
        (declare-const a String)
        (assert (= x (str.++ a a)))
    )", false);
    check_rewrite(R"(
        (declare-const x String)
        (declare-const a String)
        (declare-const b String)
        (assert (= x (str.++ a b)))
        (assert (> (str.len a) 0))
    )", false);
    check_rewrite(R"(
        (declare-const x String)
        (declare-const a String)
        (assert (= x (str.++ a "c")))
    )", false);
    check_rewrite(R"(
        (declare-const x String)
        (declare-const a String)
        (declare-const b String)
        (declare-fun p (String Int) Bool)
        (assert (= x (str.++ a b)))
        (assert (forall ((i Int)) (p (str.++ a b) i)))
    )", false);
    for (char const* sort : {"Int", "Bool"}) {
        std::string seq = std::string("(Seq ") + sort + ")";
        std::string input =
            "(declare-const x " + seq + ")(declare-const a " + seq + ")"
            "(declare-const b " + seq + ")(assert (= x (seq.++ a b)))";
        check_rewrite(input.c_str(), true);
    }
    check_model(R"(
        (declare-const x String)
        (declare-const a String)
        (declare-const b String)
        (declare-const p Int)
        (declare-const q Int)
        (assert (= x (str.++ a b)))
        (assert (str.in_re x (str.to_re "ab")))
        (assert (> (+ p q) 1))
    )");
    check_model(R"(
        (declare-const a String)
        (declare-const b String)
        (assert (= (str.++ a b) "a"))
        (assert (= (str.++ a b) "b"))
    )", true);
}
