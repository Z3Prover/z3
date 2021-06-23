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
        if (!lemma) lemma = y_ule_ax_and_x_ule_z();

        if (lemma) {
            LOG("New lemma: " << *lemma);
            for (auto* c : lemma->new_constraints()) {
                LOG("New constraint: " << show_deref(c));
            }
        }
        else {
            LOG("No lemma");
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
        LOG_H3("Try zx > yx where x := v" << m_var);
        for (auto* c : m_conflict.units())
            LOG("Constraint: " << show_deref(c));
        for (auto* c : m_conflict.clauses())
            LOG("Clause: " << show_deref(c));

        // Find constraint of desired shape
        for (auto* c : m_conflict.units()) {
            if (!c->is_ule())
                continue;
            pdd const& lhs = c->to_ule().lhs();
            pdd const& rhs = c->to_ule().rhs();
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
                if (!push_omega_mul(clause, lvl, p, x, y))
                    continue;
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

    /// [y] z' <= y /\ zx > yx  ==>  ...
    clause_ref conflict_explainer::by_ugt_y() {
        LOG_H3("Try z' <= y && zx > yx where y := v" << m_var);
        for (auto* c : m_conflict.units())
            LOG("Constraint: " << show_deref(c));
        for (auto* c : m_conflict.clauses())
            LOG("Clause: " << show_deref(c));

        pdd const y = m_solver.var(m_var);

        // Collect constraints of shape "_ <= y"
        ptr_vector<constraint> ds;
        for (auto* d : m_conflict.units()) {
            if (!d->is_ule())
                continue;
            if (!d->is_positive())
                continue;
            pdd const& rhs = d->to_ule().rhs();
            // TODO: a*y where 'a' divides 'x' should also be easy to handle (assuming for now they're numbers)
            // TODO: also z' < y should follow the same pattern.
            if (rhs != y)
                continue;
            LOG("z' <= y candidate: " << show_deref(d));
            ds.push_back(d);
        }
        if (ds.empty())
            return nullptr;

        // Find constraint of shape: zx > yx
        for (auto* c : m_conflict.units()) {
            if (!c->is_ule())
                continue;
            pdd const& lhs = c->to_ule().lhs();
            pdd const& rhs = c->to_ule().rhs();
            if (rhs.degree(m_var) != 1)
                continue;
            pdd x = lhs;
            pdd rest = lhs;
            rhs.factor(m_var, 1, x, rest);
            if (!rest.is_zero())
                continue;
            // TODO: in principle, 'x' could be any polynomial. However, we need to divide the lhs by x, and we don't have general polynomial division yet.
            //       so for now we just allow the form 'value*variable'.
            //       (extension to arbitrary monomials for 'x' should be fairly easy too)
            if (!x.is_unary())
                continue;
            unsigned x_var = x.var();
            rational x_coeff = x.hi().val();
            pdd xz = lhs;
            if (!lhs.try_div(x_coeff, xz))
                continue;
            pdd z = lhs;
            xz.factor(x_var, 1, z, rest);
            if (!rest.is_zero())
                continue;

            unsigned const lvl = c->level();  // TODO: max of both levels
            if (c->is_positive()) {
                // zx <= yx
                NOT_IMPLEMENTED_YET();
            }
            else {
                SASSERT(c->is_negative());
                // zx > yx

                LOG("zx > yx: " << show_deref(c));

                // TODO: for now, we just choose the first of the other constraints
                constraint* d = ds[0];
                SASSERT(d->is_ule() && d->is_positive());
                pdd const& z_prime = d->to_ule().lhs();

                unsigned const p = m_solver.size(m_var);

                clause_builder clause(m_solver);
                // Omega^*(x, y)
                if (!push_omega_mul(clause, lvl, p, x, y))
                    continue;
                // zx > z'x
                constraint_ref zx_gt_zpx = m_solver.m_constraints.ult(lvl, pos_t, z*x, z_prime*x, null_dep());
                LOG("zx>z'x: " << show_deref(zx_gt_zpx));
                clause.push_new_constraint(std::move(zx_gt_zpx));

                return clause.build(lvl, {c->dep(), m_solver.m_dm});  // TODO: join deps
            }
        }
        return nullptr;
    }

    /// [z] z <= y' /\ zx > yx  ==>  ...
    clause_ref conflict_explainer::by_ugt_z() {
        LOG_H3("Try z <= y' && zx > yx where z := v" << m_var);
        for (auto* c : m_conflict.units())
            LOG("Constraint: " << show_deref(c));
        for (auto* c : m_conflict.clauses())
            LOG("Clause: " << show_deref(c));

        pdd const z = m_solver.var(m_var);

        // Collect constraints of shape "z <= _"
        ptr_vector<constraint> ds;
        for (auto* d : m_conflict.units()) {
            if (!d->is_ule())
                continue;
            if (!d->is_positive())
                continue;
            pdd const& lhs = d->to_ule().lhs();
            // TODO: a*y where 'a' divides 'x' should also be easy to handle (assuming for now they're numbers)
            // TODO: also z < y' should follow the same pattern.
            if (lhs != z)
                continue;
            LOG("z <= y' candidate: " << show_deref(d));
            ds.push_back(d);
        }
        if (ds.empty())
            return nullptr;

        // Find constraint of shape: zx > yx
        for (auto* c : m_conflict.units()) {
            if (!c->is_ule())
                continue;
            pdd const& lhs = c->to_ule().lhs();
            pdd const& rhs = c->to_ule().rhs();
            if (lhs.degree(m_var) != 1)
                continue;
            pdd x = lhs;
            pdd rest = lhs;
            lhs.factor(m_var, 1, x, rest);
            if (!rest.is_zero())
                continue;
            // TODO: in principle, 'x' could be any polynomial. However, we need to divide the lhs by x, and we don't have general polynomial division yet.
            //       so for now we just allow the form 'value*variable'.
            //       (extension to arbitrary monomials for 'x' should be fairly easy too)
            if (!x.is_unary())
                continue;
            unsigned x_var = x.var();
            rational x_coeff = x.hi().val();
            pdd xy = lhs;
            if (!rhs.try_div(x_coeff, xy))
                continue;
            pdd y = lhs;
            xy.factor(x_var, 1, y, rest);
            if (!rest.is_zero())
                continue;

            unsigned const lvl = c->level();  // TODO: max of both levels
            if (c->is_positive()) {
                // zx <= yx
                NOT_IMPLEMENTED_YET();
            }
            else {
                SASSERT(c->is_negative());
                // zx > yx

                LOG("zx > yx: " << show_deref(c));

                // TODO: for now, we just choose the first of the other constraints
                constraint* d = ds[0];
                SASSERT(d->is_ule() && d->is_positive());
                pdd const& y_prime = d->to_ule().rhs();

                unsigned const p = m_solver.size(m_var);

                clause_builder clause(m_solver);
                // Omega^*(x, y')
                if (!push_omega_mul(clause, lvl, p, x, y_prime))
                    continue;
                // y'x > yx
                constraint_ref ypx_gt_yx = m_solver.m_constraints.ult(lvl, pos_t, y_prime*x, y*x, null_dep());
                LOG("y'x>yx: " << show_deref(ypx_gt_yx));
                clause.push_new_constraint(std::move(ypx_gt_yx));

                return clause.build(lvl, {c->dep(), m_solver.m_dm});  // TODO: join deps
            }
        }
        return nullptr;
    }

    /// [x]  y <= ax /\ x <= z  (non-overflow case)
    ///     ==>   Ω*(a, z)  \/  y <= az
    clause_ref conflict_explainer::y_ule_ax_and_x_ule_z() {
        LOG_H3("Try y <= ax && x <= z where x := v" << m_var);
        for (auto* c : m_conflict.units())
            LOG("Constraint: " << show_deref(c));
        for (auto* c : m_conflict.clauses())
            LOG("Clause: " << show_deref(c));

        pdd const x = m_solver.var(m_var);
        unsigned const sz = m_solver.size(m_var);
        pdd const zero = m_solver.sz2pdd(sz).zero();

        // Collect constraints of shape "x <= _"
        vector<inequality> ds;
        ptr_vector<constraint> d1s;
        for (auto* d1 : m_conflict.units()) {
            inequality d = d1->as_inequality();
            if (d.lhs != x)
                continue;
            LOG("x <= z' candidate: " << show_deref(d1));
            ds.push_back(std::move(d));
            d1s.push_back(d1);
        }
        if (ds.empty())
            return nullptr;

        // Find constraint of shape: y <= ax
        for (auto* c1 : m_conflict.units()) {
            inequality c = c1->as_inequality();
            if (c.rhs.degree(m_var) != 1)
                continue;
            pdd a = zero;
            pdd rest = zero;
            c.rhs.factor(m_var, 1, a, rest);
            if (!rest.is_zero())
                continue;
            pdd const& y = c.lhs;

            LOG("y <= ax: " << show_deref(c1));

            // TODO: for now, we just try all of the other constraints in order
            for (unsigned i = 0; i < ds.size(); ++i) {
                inequality d = ds[i];
                constraint* d1 = d1s[i];
                unsigned const lvl = std::max(c1->level(), d1->level());
                pdd const& z = d.rhs;

                clause_builder clause(m_solver);
                // Omega^*(a, z)
                if (!push_omega_mul(clause, lvl, sz, a, z))
                    continue;
                // y'x > yx
                constraint_ref y_ule_az;
                if (c.is_strict || d.is_strict)
                    y_ule_az = m_solver.m_constraints.ult(lvl, pos_t, y, a*z, null_dep());
                else
                    y_ule_az = m_solver.m_constraints.ule(lvl, pos_t, y, a*z, null_dep());
                LOG("y<=az: " << show_deref(y_ule_az));
                clause.push_new_constraint(std::move(y_ule_az));

                return clause.build(lvl, {c1->dep(), m_solver.m_dm});  // TODO: join deps
            }
        }
        return nullptr;
    }

    /// Add Ω*(x, y) to the clause.
    ///
    /// @param[in] p    bit width
    bool conflict_explainer::push_omega_mul(clause_builder& clause, unsigned level, unsigned p, pdd const& x, pdd const& y) {
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

        if (min_k > max_k) {
            // In this case, we cannot choose k such that both literals are false.
            // This means x*y overflows in the current model and the chosen rule is not applicable.
            // (or maybe we are in the case where we need the msb-encoding for overflow).
            return false;
        }

        SASSERT(min_k <= max_k);  // if this assertion fails, we cannot choose k s.t. both literals are false

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
        return true;
    }
}
