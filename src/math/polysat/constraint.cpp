/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/constraint.h"
#include "math/polysat/clause.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"
#include "math/polysat/ule_constraint.h"

namespace polysat {

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


    clause* constraint_manager::store(clause_ref cl_ref) {
        clause* cl = cl_ref.get();
        while (m_clauses.size() <= cl->level())
            m_clauses.push_back({});
        m_clauses[cl->level()].push_back(std::move(cl_ref));
        return cl;
    }

    void constraint_manager::register_external(signed_constraint c) {
        SASSERT(c);
        SASSERT(!c->is_external());
        if (c->unit_dep() && c->unit_dep()->is_leaf()) {
            unsigned const dep = c->unit_dep()->leaf_value();
            SASSERT(!m_external_constraints.contains(dep));
            m_external_constraints.insert(dep, c.get());
        }
        c->set_external(c.is_negative());
        ++m_num_external;
    }

    void constraint_manager::unregister_external(constraint* c) {
        if (c->unit_dep() && c->unit_dep()->is_leaf()) 
            m_external_constraints.remove(c->unit_dep()->leaf_value());        
        c->unset_external();
        --m_num_external;
    }

    signed_constraint constraint_manager::lookup_external(unsigned dep) const {
        constraint* c = m_external_constraints.get(dep, nullptr);
        if (c)
            return {c, !c->external_sign()};
        else
            return {};
    }

    // Release constraints at the given level and above.
    void constraint_manager::release_level(unsigned lvl) {
        for (unsigned l = m_clauses.size(); l-- > lvl; ) {
            for (auto const& cl : m_clauses[l]) {
                SASSERT_EQ(cl->m_ref_count, 1);  // otherwise there is a leftover reference somewhere
            }
            m_clauses[l].reset();
        }
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
            m_constraint_table.insert(c1);
            store(c1);
            return c1;
        }
    }

    void constraint_manager::gc(solver& s) {
        gc_clauses(s);
        gc_constraints(s);
    }

    void constraint_manager::gc_clauses(solver& s) {
        // place to gc redundant clauses
    }

    void constraint_manager::gc_constraints(solver& s) {
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
            erase_bvar(c);
            m_constraints.swap(i, m_constraints.size() - 1);
            m_constraints.pop_back();
            --i;
        }
            
    }

    bool constraint_manager::should_gc() {
        // TODO control gc decay rate
        return m_constraints.size() > m_num_external + 100;
    }

    signed_constraint constraint_manager::eq(pdd const& p) {
        pdd z = p.manager().zero();
        return {dedup(alloc(ule_constraint, *this, p, z)), true};
    }

    signed_constraint constraint_manager::ule(pdd const& a, pdd const& b) {
        return {dedup(alloc(ule_constraint, *this, a, b)), true};
    }

    signed_constraint constraint_manager::ult(pdd const& a, pdd const& b) {
        // a < b  <=>  !(b <= a)
        return ~ule(b, a);
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

    signed_constraint inequality::as_signed_constraint() const {
        return signed_constraint(const_cast<constraint*>(src), !is_strict);
    }

    ule_constraint& constraint::to_ule() {
        return *dynamic_cast<ule_constraint*>(this);
    }

    ule_constraint const& constraint::to_ule() const {
        return *dynamic_cast<ule_constraint const*>(this);
    }

    std::ostream& constraint::display_extra(std::ostream& out, lbool status) const {
        out << " (b";
        if (has_bvar()) { out << bvar(); } else { out << "_"; }
        out << ")";
        (void)status;
        return out;
    }

    bool constraint::propagate(solver& s, bool is_positive, pvar v) {
        LOG_H3("Propagate " << s.m_vars[v] << " in " << signed_constraint(this, is_positive));
        SASSERT(!vars().empty());
        unsigned idx = 0;
        if (var(idx) != v)
            idx = 1;
        SASSERT(v == var(idx));
        // find other watch variable.
        for (unsigned i = vars().size(); i-- > 2; ) {
            unsigned other_v = vars()[i];
            if (!s.is_assigned(other_v)) {
                s.add_watch({this, is_positive}, other_v);
                std::swap(vars()[idx], vars()[i]);
                return true;
            }
        }
        // at most one variable remains unassigned.
        unsigned other_v = var(idx);
        propagate_core(s, is_positive, v, other_v);
        return false;
    }

    void constraint::propagate_core(solver& s, bool is_positive, pvar v, pvar other_v) {
        (void)v;
        (void)other_v;
        narrow(s, is_positive);
    }

    void constraint::set_unit_clause(clause *cl) {
        // can be seen as a cache... store the lowest-level unit clause for this constraint.
        if (!cl || !m_unit_clause || m_unit_clause->level() > cl->level())
            m_unit_clause = cl;
    }

    lbool signed_constraint::bvalue(solver& s) const {
        return s.m_bvars.value(blit());
    }
}
