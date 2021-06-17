/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation / resolution

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#include "math/polysat/explain.h"
#include "math/polysat/log.h"

namespace polysat {

    conflict_explainer::conflict_explainer(solver& s, constraints_and_clauses const& conflict):
        m_solver(s), m_conflict(conflict) {}

    clause_ref conflict_explainer::resolve(pvar v, ptr_vector<constraint> const& cjust) {
        LOG_H3("Attempting to explain conflict for v" << v);
        m_var = v;
        m_cjust_v = cjust;

        for (auto* c : cjust)
            m_conflict.push_back(c);

        // TODO: we should share work done for examining constraints between different resolution methods
        clause_ref lemma;
        if (!lemma) lemma = by_polynomial_superposition();
        if (!lemma) lemma = by_ugt_x();
        if (!lemma) lemma = by_ugt_y();
        if (!lemma) lemma = by_ugt_z();

        if (lemma) {
            LOG("New lemma: " << *lemma);
            for (auto* c : lemma->new_constraints()) {
                LOG("New constraint: " << show_deref(c));
            }
        }

        m_var = null_var;
        m_cjust_v.reset();
        return lemma;
    }

    clause_ref conflict_explainer::by_polynomial_superposition() {
        if (m_conflict.units().size() != 2 || m_conflict.clauses().size() > 0)
            return nullptr;
        constraint* c1 = m_conflict.units()[0];
        constraint* c2 = m_conflict.units()[1];
        if (c1 == c2)
            return nullptr;
        if (!c1->is_eq() || !c2->is_eq())
            return nullptr;
        if (c1->is_positive() && c2->is_positive()) {
            pdd a = c1->to_eq().p();
            pdd b = c2->to_eq().p();
            pdd r = a;
            if (!a.resolve(m_var, b, r) && !b.resolve(m_var, a, r))
                return nullptr;
            p_dependency_ref d(m_solver.m_dm.mk_join(c1->dep(), c2->dep()), m_solver.m_dm);
            unsigned lvl = std::max(c1->level(), c2->level());
            constraint_ref c = m_solver.m_constraints.eq(lvl, pos_t, r, d);
            c->assign(true);
            return clause::from_unit(c);
        }
        return nullptr;
    }

    /// [x] zx > yx  ==>  ...
    clause_ref conflict_explainer::by_ugt_x() {
        LOG_H3("Try zx > yx");
        for (auto* c : m_conflict.units())
            LOG("Constraint: " << show_deref(c));
        for (auto* c : m_conflict.clauses())
            LOG("Clause: " << show_deref(c));

        // Find constraint of desired shape
        for (auto* c : m_conflict.units()) {
            if (!c->is_ule())
                continue;
            pdd lhs = c->to_ule().lhs();
            pdd rhs = c->to_ule().rhs();
            if (lhs.degree(m_var) != 1)
                continue;
            if (rhs.degree(m_var) != 1)
                continue;
            pdd y = lhs;
            pdd rest = lhs;
            rhs.factor(m_var, 1, y, rest);
            if (!rest.is_zero())
                continue;
            pdd z = lhs;
            lhs.factor(m_var, 1, z, rest);
            if (!rest.is_zero())
                continue;

            if (c->is_positive()) {
                // zx <= yx
                NOT_IMPLEMENTED_YET();
            }
            else {
                SASSERT(c->is_negative());
                // zx > yx

                unsigned const lvl = c->level();

                pdd x = m_solver.var(m_var);
                unsigned const p = m_solver.size(m_var);

                clause_builder clause(m_solver);
                // Omega^*(x, y)
                push_omega_mul(clause, lvl, p, x, y);
                // z > y
                constraint_ref z_gt_y = m_solver.m_constraints.ult(lvl, pos_t, y, z, null_dep());
                LOG("z>y: " << show_deref(z_gt_y));
                clause.push_new_constraint(std::move(z_gt_y));

                p_dependency_ref d(c->dep(), m_solver.m_dm);
                return clause.build(lvl, d);
            }

        }
        return nullptr;
    }

    /// [y] y >= z' /\ zx > yx  ==>  ...
    clause_ref conflict_explainer::by_ugt_y() {
        return nullptr;
    }

    /// [z] y' >= z /\ zx > yx  ==>  ...
    clause_ref conflict_explainer::by_ugt_z() {
        return nullptr;
    }

    /// Add Ω*(x, y) to the clause.
    ///
    /// @param[in] p    bit width
    void conflict_explainer::push_omega_mul(clause_builder& clause, unsigned level, unsigned p, pdd const& x, pdd const& y) {
        LOG_H3("Omega^*(x, y)");
        LOG("x = " << x);
        LOG("y = " << y);
        auto& pddm = m_solver.sz2pdd(p);
        unsigned min_k = 0;
        unsigned max_k = p - 1;
        unsigned k = p/2;

        rational x_val;
        if (m_solver.try_eval(x, x_val)) {
            unsigned x_bits = x_val.bitsize();
            LOG("eval x: " << x << " := " << x_val << " (x_bits: " << x_bits << ")");
            SASSERT(x_val < rational::power_of_two(x_bits));
            min_k = x_bits;
        }

        rational y_val;
        if (m_solver.try_eval(y, y_val)) {
            unsigned y_bits = y_val.bitsize();
            LOG("eval y: " << y << " := " << y_val << " (y_bits: " << y_bits << ")");
            SASSERT(y_val < rational::power_of_two(y_bits));
            max_k = p - y_bits;
        }

        SASSERT(min_k <= max_k);  // in this case, cannot choose k s.t. both literals are false

        // TODO: could also choose other value for k (but between the bounds)
        if (min_k == 0)
            k = max_k;
        else
            k = min_k;

        LOG("k = " << k << "; min_k = " << min_k << "; max_k = " << max_k << "; p = " << p);
        SASSERT(min_k <= k && k <= max_k);

        // x >= 2^k
        constraint_ref c1 = m_solver.m_constraints.ult(level, pos_t, pddm.mk_val(rational::power_of_two(k)), x, null_dep());
        // y > 2^{p-k}
        constraint_ref c2 = m_solver.m_constraints.ule(level, pos_t, pddm.mk_val(rational::power_of_two(p-k)), y, null_dep());
        clause.push_new_constraint(std::move(c1));
        clause.push_new_constraint(std::move(c2));
    }
}
