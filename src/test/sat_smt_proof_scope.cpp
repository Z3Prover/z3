/*++
Copyright (c) 2026 Romain Soulat

    Incremental SAT/SMT proof clauses must bind user-scope guard literals.
--*/
#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"
#include "solver/solver.h"
#include "model/model.h"
#include "tactic/user_propagator_base.h"
#include "util/debug.h"

void tst_sat_smt_proof_scope() {
    for (bool early_scope : {false, true}) {
        ast_manager m;
        reg_decl_plugins(m);
        arith_util a(m);
        params_ref p;
        p.set_bool("smt", true);
        p.set_bool("euf", true);
        p.set_bool("smt.proof.check", true);
        scoped_ptr<solver> s = mk_smt2_solver(m, p);
        if (early_scope) {
            s->push();
            s->push();
        }
        unsigned clauses = 0;
        auto pop = [&](unsigned n) { s->pop(n); };
        user_propagator::on_clause_eh_t callback = [&](void*, expr*, unsigned, unsigned const*,
                                                       unsigned n, expr* const* literals) {
            // Includes deletion notifications during pop, before variable IDs
            // can be recycled for a different scope's atoms.
            for (unsigned i = 0; i < n; ++i)
                ENSURE(literals[i] && m.is_bool(literals[i]));
            ++clauses;
        };
        s->register_on_clause(nullptr, callback);
        expr_ref x(m.mk_const("scope_x", a.mk_int()), m);
        s->assert_expr(a.mk_ge(x, a.mk_int(0)));
        s->assert_expr(a.mk_le(x, a.mk_int(3)));
        ENSURE(s->check_sat() == l_true);
        for (unsigned i = 0; i < 8; ++i) {
            s->push();
            expr_ref value(m.mk_eq(x, a.mk_int(i % 4)), m);
            s->assert_expr(value);
            ENSURE(s->check_sat() == l_true);
            model_ref model;
            s->get_model(model);
            expr_ref evaluated(m);
            ENSURE(model->eval_expr(value, evaluated, true) && m.is_true(evaluated));
            // The scope's proof atom is internal and must not pollute models.
            for (unsigned j = 0; j < model->get_num_constants(); ++j)
                ENSURE(model->get_constant(j)->get_name().str().find("sat.scope") != 0);
            s->push();
            s->assert_expr(m.mk_not(value));
            ENSURE(s->check_sat() == l_false);
            pop(1);
            ENSURE(s->check_sat() == l_true);
            pop(1);
            ENSURE(s->check_sat() == l_true);
            expr_ref out_of_range(m.mk_eq(x, a.mk_int(4)), m);
            expr* assumptions[] = {out_of_range};
            ENSURE(s->check_sat(1, assumptions) == l_false);
            ENSURE(s->check_sat() == l_true);
        }
        if (early_scope) {
            pop(2);
            ENSURE(s->check_sat() == l_true);
            s->push();
            s->assert_expr(m.mk_eq(x, a.mk_int(7)));
            ENSURE(s->check_sat() == l_true);
            pop(1);
        }
        ENSURE(clauses > 0);
    }
}
