/*++
Copyright (c) 2026

Module Name:

    bv_mul_bounds.cpp

Abstract:

    Guarded order lemmas for unsigned multiplication with a common factor.

--*/
#include "ast/simplifiers/bv_mul_bounds.h"
#include "ast/for_each_expr.h"
#include "util/obj_pair_hashtable.h"

namespace {

    // atom, or its negation, denotes lhs <=u rhs. Keep the existing atom
    // instead of introducing another comparison or overflow circuit.
    struct comparison {
        expr* lhs = nullptr;
        expr* rhs = nullptr;
        expr* atom = nullptr;
        bool negated = false;
    };

    bool get_comparison(bv_util& bv, expr* e, comparison& c) {
        if (!is_app(e) || to_app(e)->get_family_id() != bv.get_fid())
            return false;
        app* a = to_app(e);
        if (a->get_num_args() != 2)
            return false;
        c = { a->get_arg(0), a->get_arg(1), e, false };
        switch (a->get_decl_kind()) {
        case OP_ULEQ:
            return true;
        case OP_UGEQ:
            std::swap(c.lhs, c.rhs);
            return true;
        case OP_ULT:
            std::swap(c.lhs, c.rhs);
            c.negated = true;
            return true;
        case OP_UGT:
            c.negated = true;
            return true;
        default:
            return false;
        }
    }

    void order_operands(expr*& a, expr*& b) {
        if (a->get_id() > b->get_id())
            std::swap(a, b);
    }
}

namespace bv {

    void mul_bounds::reduce() {
        expr_ref_vector fmls(m);
        obj_hashtable<expr> emitted;
        obj_map<expr, unsigned> units;
        for (unsigned i : indices()) {
            expr* f = m_fmls[i].fml();
            fmls.push_back(f);
            emitted.insert(f);
            units.insert(f, i);
        }

        obj_pair_map<expr, expr, expr*> guards;
        obj_pair_map<expr, expr, comparison> orders;
        vector<comparison> targets;
        for (expr* e : subterms::ground(fmls)) {
            if (!m.inc())
                return;
            expr* a, * b;
            if (m_util.is_bv_umul_no_ovfl(e, a, b)) {
                order_operands(a, b);
                guards.insert(a, b, e);
            }
            comparison c;
            if (!get_comparison(m_util, e, c))
                continue;
            orders.insert(c.lhs, c.rhs, c);
            if (m_util.is_bv_mul(c.lhs) && m_util.is_bv_mul(c.rhs))
                targets.push_back(c);
        }

        auto literal = [&](comparison const& c, bool negate = false) -> expr* {
            return c.negated != negate ? m.mk_not(c.atom) : c.atom;
        };
        auto resolve = [&](app* clause, proof* pr) {
            unsigned idx[3];
            for (unsigned k = 0; k < 3; ++k) {
                expr* arg = clause->get_arg(k), * negated;
                expr_ref complement(m);
                complement = m.is_not(arg, negated) ? negated : m.mk_not(arg);
                if (!units.find(complement, idx[k]))
                    return false;
            }
            // Only top-level asserted complements can close the goal. Keep
            // their dependencies and resolve their proofs with the valid
            // guarded clause; an atom merely seen below an OR is not a fact.
            expr_dependency_ref dep(m);
            proof_ref_vector premises(m);
            if (proofs_enabled())
                premises.push_back(pr);
            for (unsigned i : idx) {
                dependent_expr fact = m_fmls[i];
                dep = m.mk_join(dep, fact.dep());
                if (proofs_enabled())
                    premises.push_back(fact.pr());
            }
            proof_ref resolved(m);
            if (proofs_enabled())
                resolved = m.mk_unit_resolution(premises.size(), premises.data());
            m_fmls.add(dependent_expr(m, m.mk_false(), resolved, dep));
            return true;
        };
        for (comparison const& target : targets) {
            if (!m.inc())
                return;
            expr* left[2], * right[2];
            if (!m_util.is_bv_mul(target.lhs, left[0], left[1]) ||
                !m_util.is_bv_mul(target.rhs, right[0], right[1]))
                continue;
            for (unsigned i = 0; i < 2; ++i) {
                for (unsigned j = 0; j < 2; ++j) {
                    if (left[i] != right[j])
                        continue;
                    expr* a = left[1 - i];
                    expr* b = right[1 - j];
                    expr* factor = left[i];
                    expr* g1 = b, * g2 = factor, * guard;
                    order_operands(g1, g2);
                    if (!guards.find(g1, g2, guard))
                        continue;

                    for (bool strict : {false, true}) {
                        comparison premise;
                        if (!orders.find(strict ? b : a, strict ? a : b, premise))
                            continue;
                        expr_ref output(literal(target), m);
                        expr_ref antecedent_negation(literal(premise, !strict), m);
                        expr_ref guard_negation(m.mk_not(guard), m);
                        // A clause already satisfied by a top-level fact adds
                        // no information and can needlessly perturb SAT search.
                        if (units.contains(antecedent_negation) ||
                            units.contains(guard_negation) || units.contains(output))
                            continue;
                        // a <=u b (or a <u b) and no unsigned overflow in
                        // b*factor imply a*factor <=u b*factor, including
                        // factor=0. The guard stays in the lemma even if it
                        // occurs below a disjunction or with negative polarity.
                        expr_ref lemma(m.mk_or(antecedent_negation, guard_negation, output), m);
                        if (emitted.contains(lemma))
                            continue;
                        emitted.insert(lemma);
                        proof_ref pr(m);
                        if (proofs_enabled())
                            pr = m.mk_th_lemma(m_util.get_fid(), lemma, 0, nullptr);
                        ++m_num_lemmas;
                        if (resolve(to_app(lemma), pr))
                            return;
                        m_fmls.add(dependent_expr(m, lemma, pr, nullptr));
                    }
                }
            }
        }
    }
}
