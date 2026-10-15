/*++
Copyright (c) 2026 Romain Soulat

    Default proof-enabled solving and original-premise proof composition.
--*/
#include "ast/reg_decl_plugins.h"
#include "ast/ff_decl_plugin.h"
#include "ast/ff/ff_evidence.h"
#include "ast/proofs/proof_checker.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/expr_substitution.h"
#include "ast/rewriter/expr_replacer.h"
#include "solver/solver.h"
#include "solver/simplifier_solver.h"
#include "ast/simplifiers/ff_simplify.h"
#include "model/model.h"
#include "util/debug.h"

namespace {
    unsigned check_native(ast_manager& m, proof* root) {
        ENSURE(root && m.is_false(m.get_fact(root)));
        proof_checker checker(m);
        expr_ref_vector conditions(m);
        ENSURE(checker.check(root, conditions));
        th_rewriter rw(m);
        for (expr* c : conditions) {
            expr_ref simplified(m);
            rw(c, simplified);
        ENSURE(m.is_true(simplified) || ff::check_polynomial_rewrite(m, c));
        }
        unsigned fields = 0;
        ptr_vector<expr> todo;
        expr_mark seen;
        todo.push_back(root);
        while (!todo.empty()) {
            expr* e = todo.back(); todo.pop_back();
            if (seen.is_marked(e)) continue;
            seen.mark(e, true);
            if (!is_app(e)) continue;
            auto* a = to_app(e);
            if (a->get_family_id() == m.get_basic_family_id() && a->get_decl_kind() == PR_TH_LEMMA &&
                a->get_decl()->get_parameter(0).get_symbol() == symbol("ff")) {
                ENSURE(ff::check_refutation_lemma(m, a));
                ++fields;
                // A valid DAG does not justify deleting its premise literals.
                auto* evidence = to_app(a->get_decl()->get_parameter(2).get_ast());
                auto forged = ff::mk_refutation_lemma(m, m.mk_false(), evidence);
                ENSURE(!ff::check_refutation_lemma(m, forged));
            }
            for (expr* child : *a) todo.push_back(child);
        }
        return fields;
    }
}

void tst_ff_native_proof() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    ff_util ff(m);
    sort_ref field(ff.mk_sort(rational(7)), m);
    expr_ref x(m.mk_const("x", field), m), y(m.mk_const("y", field), m);
    expr_ref one(ff.mk_numeral(rational(1), field), m);
    expr_ref three(ff.mk_numeral(rational(3), field), m);
    expr_ref six(ff.mk_numeral(rational(6), field), m);
    expr_ref square(ff.mk_mul(x, x), m);
    params_ref params;
    params.set_uint("timeout", 10000);
    // Boolean replay accepts structural tautologies, but must not turn field
    // equations or incomplete assignments into assumptions.
    expr_ref a(m.mk_const("a", m.mk_bool_sort()), m), b(m.mk_const("b", m.mk_bool_sort()), m);
    expr_ref ab(m.mk_or(a, b), m);
    ENSURE(ff::check_boolean_tautology(m, m.mk_true()));
    ENSURE(!ff::check_boolean_tautology(m, m.mk_false()));
    ENSURE(!ff::check_boolean_tautology(m, a));
    ENSURE(!ff::check_boolean_tautology(m, ab));
    ENSURE(ff::check_boolean_tautology(m, m.mk_or(m.mk_not(ab), a, b)));
    ENSURE(ff::check_boolean_tautology(m, m.mk_eq(m.mk_and(a, b), m.mk_not(m.mk_or(m.mk_not(a), m.mk_not(b))))));
    ENSURE(ff::check_boolean_tautology(m, m.mk_eq(m.mk_ite(a, b, m.mk_not(b)), m.mk_eq(a, b))));
    ENSURE(!ff::check_boolean_tautology(m, m.mk_eq(x, one)));
    ENSURE(!ff::check_boolean_tautology(m, m.mk_or(m.mk_eq(x, one), m.mk_eq(x, six))));
    expr_ref many(m.mk_true(), m);
    for (unsigned i = 0; i < 13; ++i) {
        expr_ref atom(m.mk_fresh_const("bounded", m.mk_bool_sort()), m);
        many = m.mk_and(many, m.mk_or(atom, m.mk_not(atom)));
    }
    ENSURE(!ff::check_boolean_tautology(m, many)); // Bound exhaustion is inconclusive.
    // Rewriting equations may choose different pivots. Only an exact ring
    // identity or a nonzero scalar multiple licenses this replay rule.
    {
        expr_ref zero(ff.mk_numeral(rational(0), field), m);
        expr_ref f(ff.mk_add(ff.mk_mul(x, x), y), m);
        expr_ref scaled(ff.mk_mul(three, f), m);
        ENSURE(ff::check_polynomial_rewrite(m, m.mk_eq(m.mk_eq(f, zero), m.mk_eq(scaled, zero))));
        ENSURE(!ff::check_polynomial_rewrite(m, m.mk_eq(m.mk_eq(f, zero), m.mk_eq(ff.mk_add(scaled, one), zero))));
        ENSURE(!ff::check_polynomial_rewrite(m, m.mk_eq(m.mk_eq(f, zero), m.mk_eq(ff.mk_mul(zero, f), zero))));
        ENSURE(!ff::check_polynomial_rewrite(m, m.mk_eq(ff.mk_mul(x, x), x)));
        expr_ref product(ff.mk_mul(x, ff.mk_add(y, one)), m);
        expr_ref expanded(ff.mk_add(ff.mk_mul(x, y), x), m);
        ENSURE(ff::check_polynomial_rewrite(m, m.mk_eq(product, expanded)));
        sort_ref other(ff.mk_sort(rational(101)), m);
        expr_ref alien(m.mk_const("other_field", other), m);
        ENSURE(!ff::check_polynomial_rewrite(m, m.mk_eq(m.mk_eq(x, zero), m.mk_eq(alien, ff.mk_numeral(rational(0), other)))));
        m.limit().push(1);
        ENSURE(!ff::check_polynomial_rewrite(m, m.mk_eq(product, expanded)));
        m.limit().pop();
        ENSURE(ff::check_polynomial_rewrite(m, m.mk_eq(product, expanded)));
    }
    // Local circuit rewrites use complete Boolean cases, with ordinary native
    // proof steps. Check the arithmetic independently on every assignment;
    // in particular, an ordinary sum is not a bit outside characteristic two.
    for (unsigned prime : {2u, 7u, 101u}) {
        sort_ref f(ff.mk_sort(rational(prime)), m);
        expr_ref c(m.mk_const("selector", m.mk_bool_sort()), m);
        expr_ref zero(ff.mk_numeral(rational(0), f), m), unit(ff.mk_numeral(rational(1), f), m);
        expr_ref left(m.mk_ite(a, unit, zero), m), right(m.mk_ite(b, unit, zero), m);
        expr_ref select(m.mk_ite(c, unit, zero), m);
        expr_ref complement(ff.mk_add(unit, ff.mk_neg(left)), m);
        expr_ref and_gate(ff.mk_mul(left, right), m);
        expr_ref twice(ff.mk_mul(ff.mk_numeral(rational(2 % prime), f), and_gate), m);
        expr_ref xor_gate(ff.mk_add(ff.mk_add(left, right), ff.mk_neg(twice)), m);
        expr_ref mux(ff.mk_add(ff.mk_mul(select, left),
            ff.mk_mul(ff.mk_add(unit, ff.mk_neg(select)), right)), m);
        for (expr* term : {complement.get(), and_gate.get(), xor_gate.get(), mux.get()}) {
            expr_ref rewritten(m); proof_ref identity(m);
            ENSURE(ff_simplify_circuit(m, term, rewritten, identity, true));
            ENSURE(identity && m.get_fact(identity) == m.mk_eq(term, rewritten));
            proof_ref denied(m.mk_asserted(m.mk_not(m.get_fact(identity))), m);
            proof_ref root(m.mk_unit_resolution({identity, denied}, m.mk_false()), m);
            ENSURE(check_native(m, root) == 0);
            for (unsigned assignment = 0; assignment < 8; ++assignment) {
                expr_substitution sub(m);
                sub.insert(a, assignment & 1 ? m.mk_true() : m.mk_false());
                sub.insert(b, assignment & 2 ? m.mk_true() : m.mk_false());
                sub.insert(c, assignment & 4 ? m.mk_true() : m.mk_false());
                scoped_ptr<expr_replacer> replace = mk_default_expr_replacer(m, false);
                replace->set_substitution(&sub);
                expr_ref equality(m.get_fact(identity), m);
                (*replace)(equality);
                th_rewriter rw(m); rw(equality);
                ENSURE(m.is_true(equality));
            }
        }
        expr_ref_vector factors(m);
        for (unsigned i = 0; i < 10; ++i)
            factors.push_back(m.mk_ite(m.mk_fresh_const("wide", m.mk_bool_sort()), unit, zero));
        expr_ref wide(ff.mk_mul(factors), m), wide_result(m); proof_ref wide_proof(m);
        ENSURE(ff_simplify_circuit(m, wide, wide_result, wide_proof, true));
        proof_ref wide_denied(m.mk_asserted(m.mk_not(m.get_fact(wide_proof))), m);
        proof_ref wide_root(m.mk_unit_resolution({wide_proof, wide_denied}, m.mk_false()), m);
        ENSURE(check_native(m, wide_root) == 0);
        // Negated and disjunctive selectors require exact hypothesis
        // boundaries when discharging clauses; do not flatten their negations.
        for (expr* selector : {m.mk_not(a), m.mk_or(a, b), m.mk_not(m.mk_or(a, b))}) {
            expr_ref selected(m.mk_ite(selector, unit, zero), m);
            expr_ref atom(m.mk_eq(ff.mk_add(selected, right), zero), m), normalized(m);
            proof_ref identity(m);
            ENSURE(ff_simplify_circuit(m, atom, normalized, identity, true));
            proof_ref denied(m.mk_asserted(m.mk_not(m.get_fact(identity))), m);
            proof_ref root(m.mk_unit_resolution({identity, denied}, m.mk_false()), m);
            ENSURE(check_native(m, root) == 0);
        }
        // Modular wrap is preserved: over F_2, two true bits sum to zero.
        expr_ref atom(m.mk_eq(ff.mk_add(left, right), zero), m), normalized(m);
        proof_ref atom_proof(m);
        ENSURE(ff_simplify_circuit(m, atom, normalized, atom_proof, true));
        for (unsigned assignment = 0; assignment < 4; ++assignment) {
            expr_substitution sub(m);
            sub.insert(a, assignment & 1 ? m.mk_true() : m.mk_false());
            sub.insert(b, assignment & 2 ? m.mk_true() : m.mk_false());
            scoped_ptr<expr_replacer> replace = mk_default_expr_replacer(m, false);
            replace->set_substitution(&sub);
            expr_ref value(normalized, m); (*replace)(value);
            th_rewriter rw(m); rw(value);
            unsigned sum = (assignment & 1) + ((assignment >> 1) & 1);
            ENSURE(m.is_true(value) == (sum % prime == 0));
        }
        expr_ref sum(ff.mk_add(left, right), m), output(m); proof_ref pr(m);
        ENSURE(ff_simplify_circuit(m, sum, output, pr, true) == (prime == 2));
        expr_ref foreign(m.mk_const("unconstrained_wire", f), m);
        expr_ref unknown(ff.mk_mul(left, foreign), m);
        ENSURE(!ff_simplify_circuit(m, unknown, output, pr, true));
    }
    // A bit-domain constraint must not prevent substitution through an
    // explicit Boolean ITE. Preserve the frozen prefix and exact source proof.
    {
        expr_ref zero(ff.mk_numeral(rational(0), field), m);
        expr_ref domain(m.mk_eq(ff.mk_mul(x, x), x), m);
        expr_ref definition(m.mk_eq(x, m.mk_ite(a, one, zero)), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, b, m.mk_asserted(b), nullptr));
        state.advance_qhead();
        state.add(dependent_expr(m, domain, m.mk_asserted(domain), nullptr));
        state.add(dependent_expr(m, definition, m.mk_asserted(definition), nullptr));
        ff_wire_simplifier pass(m, state); pass.reduce();
        ENSURE(state[0].fml() == b && state[1].fml() != domain);
        proof_ref denied(m.mk_asserted(m.mk_not(state[1].fml())), m);
        proof_ref root(m.mk_unit_resolution({state[1].pr(), denied}, m.mk_false()), m);
        ENSURE(check_native(m, root) == 0);
    }
    // Alias elimination transports, rather than drops, a bit-domain assertion.
    {
        expr_ref domain(m.mk_eq(ff.mk_mul(x, x), x), m);
        expr_ref alias(m.mk_eq(x, y), m);
        expr_ref expected(m.mk_eq(ff.mk_mul(y, y), y), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, domain, m.mk_asserted(domain), nullptr));
        state.add(dependent_expr(m, alias, m.mk_asserted(alias), nullptr));
        ff_wire_simplifier pass(m, state); pass.reduce();
        ENSURE(state[0].fml() == expected);
        proof_ref denied(m.mk_asserted(m.mk_not(expected)), m);
        proof_ref root(m.mk_unit_resolution({state[0].pr(), denied}, m.mk_false()), m);
        ENSURE(check_native(m, root) == 0);
    }
    // A wide symbolic sum is still one input to a zero-test gate; its
    // arbitrary inverse witness must not hide the Boolean indicator.
    {
        sort_ref f(ff.mk_sort(rational("52435875175126190479447740508185965837690552500527637822603658699938581184513")), m);
        expr_ref_vector terms(m);
        for (unsigned i = 0; i < 10; ++i) terms.push_back(m.mk_fresh_const("sum_input", f));
        expr_ref sum(ff.mk_add(terms), m), z(m.mk_const("sum_indicator", f), m), u(m.mk_const("sum_inverse", f), m);
        expr_ref zero(ff.mk_numeral(rational(0), f), m), unit(ff.mk_numeral(rational(1), f), m);
        expr_ref guard(m.mk_eq(ff.mk_mul(sum, ff.mk_add(unit, ff.mk_mul(ff.mk_numeral(ff.modulus(f) - rational(1), f), z))), zero), m);
        expr_ref definition(m.mk_eq(z, ff.mk_mul(sum, u)), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, guard, m.mk_asserted(guard), nullptr));
        state.add(dependent_expr(m, definition, m.mk_asserted(definition), nullptr));
        ff_zero_test_simplifier pass(m, state); pass.reduce();
        ENSURE(state.qtail() == 3);
        proof_ref denied(m.mk_asserted(m.mk_not(state[2].fml())), m);
        proof_ref root(m.mk_unit_resolution({state[2].pr(), denied}, m.mk_false()), m);
        ENSURE(check_native(m, root) >= 2);
    }
    // Proof-producing preprocessing must bind both original equations. Check
    // both indicator polarities and characteristic two, where -1 = 1.
    for (unsigned prime : {2u, 7u, 101u}) {
        sort_ref f(ff.mk_sort(rational(prime)), m);
        expr_ref z(m.mk_const("indicator", f), m), u(m.mk_const("inverse", f), m);
        expr_ref input(m.mk_const("input", f), m);
        expr_ref zero(ff.mk_numeral(rational(0), f), m), unit(ff.mk_numeral(rational(1), f), m);
        for (bool nonzero : {false, true}) {
            expr_ref negated(prime == 2 ? z.get() : ff.mk_mul(ff.mk_numeral(rational(prime - 1), f), z), m);
            expr_ref factor(nonzero ? ff.mk_add(unit, negated) : z.get(), m);
            expr_ref guard(m.mk_eq(ff.mk_mul(input, factor), zero), m);
            expr_ref rhs(ff.mk_mul(input, u), m);
            if (!nonzero) rhs = ff.mk_add(unit, rhs);
            expr_ref definition(m.mk_eq(z, rhs), m);
            base_dependent_expr_state state(m);
            state.add(dependent_expr(m, guard, m.mk_asserted(guard), nullptr));
            state.add(dependent_expr(m, definition, m.mk_asserted(definition), nullptr));
            ff_zero_test_simplifier pass(m, state);
            pass.reduce();
            ENSURE(state.qtail() == 3);
            ENSURE(state[2].pr() && m.get_fact(state[2].pr()) == state[2].fml());
            proof_ref denied(m.mk_asserted(m.mk_not(state[2].fml())), m);
            proof_ref root(m.mk_unit_resolution({state[2].pr(), denied}, m.mk_false()), m);
            ENSURE(check_native(m, root) >= 2);
        }
        expr_ref domain(m.mk_or(m.mk_eq(input, zero), m.mk_eq(input, unit)), m);
        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, domain, m.mk_asserted(domain), nullptr));
        ff_disjunctive_simplifier pass(m, params, state);
        pass.reduce();
        ENSURE(state[0].fml() != domain && state[0].pr());
        proof_ref denied(m.mk_asserted(m.mk_not(state[0].fml())), m);
        proof_ref root(m.mk_unit_resolution({state[0].pr(), denied}, m.mk_false()), m);
        ENSURE(check_native(m, root) >= 2);
    }
    {
        expr_ref_vector premises(m);
        premises.push_back(m.mk_eq(ff.mk_mul(x, x), three));
        params_ref exhausted;
        exhausted.set_uint("ff.max_steps", 0);
        ENSURE(!ff::record_refutation(m, premises, exhausted));
    }
    proof_ref retained(m);
    {
        scoped_ptr<solver> s = mk_smt2_solver(m, params, symbol("QF_FF"));
        s->assert_expr(m.mk_eq(square, three));
        ENSURE(s->check_sat() == l_false);
        retained = s->get_proof();
        ENSURE(check_native(m, retained) > 0);
    }
    // The native proof owns the evidence after the solver is destroyed.
    ENSURE(check_native(m, retained) > 0);
    // The SMT adapter may receive a second, irrelevant field assertion.
    // Its learned clause must use only the source literals named by PAC.
    {
        scoped_ptr<solver> s = mk_smt2_solver(m, params, symbol("QF_FF"));
        s->assert_expr(m.mk_eq(square, three));
        s->assert_expr(m.mk_eq(ff.mk_mul(y, y), three));
        ENSURE(s->check_sat() == l_false);
        proof *root = s->get_proof();
        ENSURE(check_native(m, root) > 0);
        bool narrowed = false;
        ptr_vector<expr> pending;
        expr_mark seen;
        pending.push_back(root);
        while (!pending.empty()) {
            expr *step = pending.back(); pending.pop_back();
            if (seen.is_marked(step)) continue;
            seen.mark(step, true);
            if (!is_app(step)) continue;
            auto *a = to_app(step);
            if (a->get_family_id() == m.get_basic_family_id() && a->get_decl_kind() == PR_TH_LEMMA &&
                a->get_decl()->get_parameter(0).get_symbol() == symbol("ff")) {
                auto *evidence = to_app(a->get_decl()->get_parameter(2).get_ast());
                narrowed |= to_app(evidence->get_arg(2))->get_num_args() <
                            to_app(evidence->get_arg(0))->get_num_args();
            }
            for (expr *child : *a) pending.push_back(child);
        }
        ENSURE(narrowed);
    }
    // Exercise both the tactic constructor (before it owns a goal) and
    // persistent model-trail substitution replay after a scope boundary.
    for (bool incremental_simplifier : {false, true}) {
        scoped_ptr<solver> s = mk_smt2_solver(m, params, symbol("QF_FF"));
        if (incremental_simplifier) {
            simplifier_factory factory = [](ast_manager& m, params_ref const& p, dependent_expr_state& st) {
                return alloc(ff_basic_simplifier, m, p, st);
            };
            s = mk_simplifier_solver(s.detach(), &factory);
        }
        s->assert_expr(m.mk_eq(x, one));
        s->push();
        s->assert_expr(m.mk_eq(x, three));
        ENSURE(s->check_sat() == l_false);
        check_native(m, s->get_proof());
        s->pop(1);
        ENSURE(s->check_sat() == l_true);
        expr_ref assumption(m.mk_eq(x, three), m);
        expr* assumptions[] = {assumption};
        ENSURE(s->check_sat(1, assumptions) == l_false);
        check_native(m, s->get_proof());
        ENSURE(s->check_sat() == l_true);
    }
    {
        scoped_ptr<solver> s = mk_smt2_solver(m, params);
        // Reversed wire definition exercises symmetry, substitution and rewrite
        // composition through preprocessing rather than a bare field conflict.
        s->assert_expr(m.mk_eq(ff.mk_add(x, one), y));
        s->assert_expr(m.mk_eq(x, one));
        s->assert_expr(m.mk_not(m.mk_eq(ff.mk_mul(y, y), ff.mk_numeral(rational(4), field))));
        ENSURE(s->check_sat() == l_false);
        check_native(m, s->get_proof());
    }
    {
        scoped_ptr<solver> s = mk_smt2_solver(m, params);
        s->assert_expr(m.mk_eq(square, one));
        ENSURE(s->check_sat() == l_true);
        expr_ref pos(m.mk_not(m.mk_eq(x, one)), m), neg(m.mk_not(m.mk_eq(x, six)), m);
        for (unsigned i = 0; i < 3; ++i) {
            s->push();
            s->assert_expr(pos); s->assert_expr(neg);
            ENSURE(s->check_sat() == l_false);
            check_native(m, s->get_proof());
            s->pop(1);
            ENSURE(s->check_sat() == l_true);
            expr* assumptions[] = {pos, neg};
            ENSURE(s->check_sat(2, assumptions) == l_false);
            check_native(m, s->get_proof());
        }
    }
    {
        scoped_ptr<solver> s = mk_smt2_solver(m, params);
        sort* domain[] = {field};
        func_decl_ref h(m.mk_func_decl(symbol("h"), 1, domain, m.mk_bool_sort()), m);
        s->assert_expr(m.mk_eq(square, one));
        s->assert_expr(m.mk_not(m.mk_eq(m.mk_app(h.get(), x), m.mk_app(h.get(), one))));
        s->assert_expr(m.mk_not(m.mk_eq(m.mk_app(h.get(), x), m.mk_app(h.get(), six))));
        ENSURE(s->check_sat() == l_false);
        ENSURE(check_native(m, s->get_proof()) > 0);
    }
}
