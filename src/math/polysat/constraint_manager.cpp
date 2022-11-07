/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraint manager

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/

#include "math/polysat/constraint_manager.h"
#include "math/polysat/clause.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"
#include "math/polysat/ule_constraint.h"
#include "math/polysat/umul_ovfl_constraint.h"
#include "math/polysat/smul_fl_constraint.h"
#include "math/polysat/op_constraint.h"

namespace polysat {

    // class constraint_dedup {
    // public:
    //     using op_constraint_args_eq = default_eq<op_constraint_args>;
    //     using op_constraint_args_hash = obj_hash<op_constraint_args>;
    //     map<op_constraint_args, pvar, op_constraint_args_hash, op_constraint_args_eq> op_constraint_vars;
    // };

    constraint_manager::constraint_manager(bool_var_manager& bvars)
        : m_bvars(bvars) /*, m_dedup(alloc(constraint_dedup))*/ {}

    void constraint_manager::assign_bv2c(sat::bool_var bv, constraint* c) {
        SASSERT_EQ(get_bv2c(bv), nullptr);
        SASSERT(!c->has_bvar());
        c->m_bvar = bv;
        m_bv2constraint.setx(bv, c, nullptr);
    }

    void constraint_manager::erase_bv2c(constraint* c) {
        SASSERT(c->has_bvar());
        SASSERT_EQ(get_bv2c(c->bvar()), c);
        m_bv2constraint[c->bvar()] = nullptr;
        c->m_bvar = sat::null_bool_var;
    }

    constraint* constraint_manager::get_bv2c(sat::bool_var bv) const {
        return m_bv2constraint.get(bv, nullptr);
    }

    void constraint_manager::ensure_bvar(constraint* c) {
        if (!c->has_bvar())
            assign_bv2c(m_bvars.new_var(), c);
    }

    void constraint_manager::erase_bvar(constraint* c) {
        if (c->has_bvar())
            erase_bv2c(c);
    }

    /** Add constraint to per-level storage */
    void constraint_manager::store(constraint* c) {
        LOG_V("Store constraint: " << show_deref(c));
        m_constraints.push_back(c);
    }


    void constraint_manager::register_clause(clause* cl, solver& s) {
        while (m_clauses.size() <= s.base_level())
            m_clauses.push_back({});
        m_clauses[s.base_level()].push_back(cl);
    }

    void constraint_manager::store(clause* cl, solver& s, bool value_propagate) {
        register_clause(cl, s);
        watch(*cl, s, value_propagate);
    }

    // Release constraints at the given level and above.
    void constraint_manager::release_level(unsigned lvl) {
        for (unsigned l = m_clauses.size(); l-- > lvl; ) {
            for (auto& cl : m_clauses[l]) {
                unwatch(*cl);
                SASSERT_EQ(cl->m_ref_count, 1);  // otherwise there is a leftover reference somewhere
            }
            m_clauses[l].reset();
        }
    }

    // find literals that are not propagated to false
    // if clause is unsat then assign arbitrary
    // solver handles unsat clauses by creating a conflict.
    // solver also can propagate, but need to check that it does indeed.
    void constraint_manager::watch(clause& cl, solver& s, bool value_propagate) {
        if (cl.empty())
            return;

        bool first = true;
        for (unsigned i = 0; i < cl.size(); ++i) {
            if (m_bvars.is_false(cl[i]))
                continue;
            signed_constraint sc = s.lit2cnstr(cl[i]);
            if (value_propagate && sc.is_currently_false(s)) {
                if (m_bvars.is_true(cl[i])) {
                    s.set_conflict(sc);
                    return;
                }
                s.assign_eval(~cl[i]);
                continue;
            }

            m_bvars.watch(cl[i]).push_back(&cl);
            std::swap(cl[!first], cl[i]);
            if (!first)
                return;
            first = false;
        }

        if (first)
            m_bvars.watch(cl[0]).push_back(&cl);
        if (cl.size() > 1)
            m_bvars.watch(cl[1]).push_back(&cl);
        if (m_bvars.is_true(cl[0]))
            return;
        if (first)
            s.set_conflict(cl);
        else
            s.assign_propagate(cl[0], cl);
    }

    void constraint_manager::unwatch(clause& cl) {
        if (cl.size() <= 1)
            return;
        m_bvars.watch(~cl[0]).erase(&cl);
        m_bvars.watch(~cl[1]).erase(&cl);
    }

    constraint_manager::~constraint_manager() {
        // Release explicitly to check for leftover references in debug mode,
        // and to make sure all constraints are destructed before the bvar->constraint mapping.
        release_level(0);
    }

    constraint* constraint_manager::lookup(sat::bool_var var) const {
        return get_bv2c(var);
    }

    signed_constraint constraint_manager::lookup(sat::literal lit) const {
        return {lookup(lit.var()), lit};
    }

    /** Look up constraint among stored constraints. */
    constraint* constraint_manager::dedup(constraint* c1) {
        constraint* c2 = nullptr;
        if (m_constraint_table.find(c1, c2)) {
            dealloc(c1);
            return c2;
        }
        else {
            SASSERT(!c1->has_bvar());
            ensure_bvar(c1);
            m_constraint_table.insert(c1);
            store(c1);
            return c1;
        }
    }

    void constraint_manager::gc(solver& s) {
        LOG_H1("gc");
        gc_clauses(s);
        gc_constraints(s);
    }

    void constraint_manager::gc_clauses(solver& s) {
        LOG_H3("gc_clauses");
        // place to gc redundant clauses
    }

    void constraint_manager::gc_constraints(solver& s) {
        LOG_H3("gc_constraints");
        uint_set used_vars;
        for (auto const& cls : m_clauses)
            for (auto const& cl : cls)
                for (auto lit : *cl)
                    used_vars.insert(lit.var());
        // anything on the search stack is justified by a clause?
        for (auto const& a : s.m_search)
            if (a.is_boolean())
                used_vars.insert(a.lit().var());
        for (unsigned i = 0; i < m_constraints.size(); ++i) {
            constraint* c = m_constraints[i];
            if (c->has_bvar() && used_vars.contains(c->bvar()))
                continue;
            if (c->is_external())
                continue;
            LOG("Erasing: " << show_deref(c));
            erase_bvar(c);
            m_constraints.swap(i, m_constraints.size() - 1);
            m_constraints.pop_back();
            --i;
        }

    }

    bool constraint_manager::should_gc() {
        return false;
        // TODO control gc decay rate
        return m_constraints.size() > m_num_external + 100;
    }

    signed_constraint constraint_manager::ule(pdd const& a, pdd const& b) {
        bool is_positive = true;
        pdd lhs = a;
        pdd rhs = b;
        ule_constraint::simplify(is_positive, lhs, rhs);
        return { dedup(alloc(ule_constraint, *this, lhs, rhs)), is_positive };
    }

    signed_constraint constraint_manager::eq(pdd const& p) {
        return ule(p, p.manager().zero());
    }

    signed_constraint constraint_manager::ult(pdd const& a, pdd const& b) {
        return ~ule(b, a);
    }

    /**
    * encode that the i'th bit of p is 1.
    * It holds if p << (K - i - 1) >= 2^{K-1}, where K is the bit-width.
    */
    signed_constraint constraint_manager::bit(pdd const& p, unsigned i) {
        unsigned K = p.manager().power_of_2();
        pdd q = p * rational::power_of_two(K - i - 1);
        rational msb = rational::power_of_two(K - 1);
        return ule(p.manager().mk_val(msb), q);
    }

    signed_constraint constraint_manager::umul_ovfl(pdd const& a, pdd const& b) {
        return { dedup(alloc(umul_ovfl_constraint, *this, a, b)), true };
    }

    signed_constraint constraint_manager::smul_ovfl(pdd const& a, pdd const& b) {
        return { dedup(alloc(smul_fl_constraint, *this, a, b, true)), true };
    }

    signed_constraint constraint_manager::smul_udfl(pdd const& a, pdd const& b) {
        return { dedup(alloc(smul_fl_constraint, *this, a, b, false)), true };
    }

    signed_constraint constraint_manager::lshr(pdd const& p, pdd const& q, pdd const& r) {
        return { dedup(alloc(op_constraint, *this, op_constraint::code::lshr_op, p, q, r)), true };
    }

    signed_constraint constraint_manager::band(pdd const& p, pdd const& q, pdd const& r) {
        return { dedup(alloc(op_constraint, *this, op_constraint::code::and_op, p, q, r)), true };
    }

    // To do signed comparison of bitvectors, flip the msb and do unsigned comparison:
    //
    //      x <=s y    <=>    x + 2^(w-1)  <=u  y + 2^(w-1)
    //
    // Example for bit width 3:
    //      111  -1
    //      110  -2
    //      101  -3
    //      100  -4
    //      011   3
    //      010   2
    //      001   1
    //      000   0
    //
    // Argument: flipping the msb swaps the negative and non-negative blocks
    //
    signed_constraint constraint_manager::sle(pdd const& a, pdd const& b) {
        auto shift = rational::power_of_two(a.power_of_2() - 1);
        return ule(a + shift, b + shift);
    }

    signed_constraint constraint_manager::slt(pdd const& a, pdd const& b) {
        auto shift = rational::power_of_two(a.power_of_2() - 1);
        return ult(a + shift, b + shift);
    }

}
