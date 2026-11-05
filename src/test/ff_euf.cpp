/*++
Copyright (c) 2026 Romain Soulat

    Persistent SAT/EUF use of the shared field core and scoped proof hints.
--*/
#include "ast/reg_decl_plugins.h"
#include "ast/ff_decl_plugin.h"
#include "ast/ff/ff_evidence.h"
#include "solver/solver.h"
#include "sat/smt/euf_proof_checker.h"
#include "model/model.h"
#include "tactic/user_propagator_base.h"
#include "util/debug.h"

void tst_ff_euf() {
    ast_manager m;
    reg_decl_plugins(m);
    ff_util ff(m);
    sort_ref field(ff.mk_sort(rational(7)), m);
    expr_ref x(m.mk_const("x", field), m), square(ff.mk_mul(x, x), m);
    expr_ref one(ff.mk_numeral(rational(1), field), m), six(ff.mk_numeral(rational(6), field), m);
    params_ref p;
    p.set_bool("smt", true);
    p.set_bool("euf", true);
    p.set_bool("smt.proof.check", true);
    // The online checker must replay FF evidence and discharge removed
    // literals by RUP, including scoped clauses. It cannot fall back to SMT.
    scoped_ptr<solver> s = mk_smt2_solver(m, p);
    expr_ref_vector proofs(m);
    unsigned count = 0;
    user_propagator::on_clause_eh_t callback = [&](void *, expr *proof, unsigned, unsigned const *, unsigned,
                                                   expr *const *) {
        if (!is_app(proof) || to_app(proof)->get_name() != symbol("ff-pac"))
            return;
        ENSURE(ff::check_refutation(m, to_app(proof)));
        proofs.push_back(proof);
        ++count;
    };
    s->register_on_clause(nullptr, callback);
    expr_ref root(m.mk_eq(square, one), m);
    s->assert_expr(root);
    for (unsigned i = 0; i < 8; ++i) {
        ENSURE(s->check_sat() == l_true);
        model_ref model;
        s->get_model(model);
        expr_ref value(m);
        ENSURE(model->eval_expr(root, value, true) && m.is_true(value));
        s->push();
        expr_ref positive(m.mk_not(m.mk_eq(x, one)), m);
        expr_ref negative(m.mk_not(m.mk_eq(x, six)), m);
        s->assert_expr(positive);
        s->assert_expr(negative);
        ENSURE(s->check_sat() == l_false);
        s->pop(1);
        ENSURE(s->check_sat() == l_true);
        expr *assumptions[] = {positive, negative};
        ENSURE(s->check_sat(2, assumptions) == l_false);
    }
    ENSURE(count > 0);
    // Even a true target clause must not conceal a malformed field DAG.
    // A fresh SMT solve could validate the clause without validating its hint.
    euf::smt_proof_checker rejecting(m, p);
    app_ref malformed(m.mk_const("ff-pac", m.mk_proof_sort()), m);
    expr_ref_vector tautology(m);
    tautology.push_back(m.mk_true());
    bool rejected = false;
    try { rejecting.infer(tautology, malformed); }
    catch (default_exception const&) { rejected = true; }
    ENSURE(rejected);
    // A consumer can retain and replay hints after their SAT scope disappears:
    // all original premises and derivation nodes are owned by the proof AST.
    for (expr *proof : proofs)
        ENSURE(ff::check_refutation(m, to_app(proof)));
}
