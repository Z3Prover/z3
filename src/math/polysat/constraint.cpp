/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/constraint.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"
#include "math/polysat/eq_constraint.h"
#include "math/polysat/ule_constraint.h"

namespace polysat {

    static_assert(!std::is_copy_assignable_v<scoped_signed_constraint>);
    static_assert(!std::is_copy_constructible_v<scoped_signed_constraint>);

    void constraint_manager::assign_bv2c(sat::bool_var bv, constraint* c) {
        SASSERT_EQ(get_bv2c(bv), nullptr);
        SASSERT(!c->has_bvar());
        SASSERT(!m_constraint_table.contains(c));
        c->m_bvar = bv;
        m_bv2constraint.setx(bv, c, nullptr);
        m_constraint_table.insert(c);
    }

    void constraint_manager::erase_bv2c(constraint* c) {
        SASSERT(c->has_bvar());
        SASSERT_EQ(get_bv2c(c->bvar()), c);
        SASSERT(m_constraint_table.contains(c));
        m_bv2constraint[c->bvar()] = nullptr;
        m_constraint_table.remove(c);
        c->m_bvar = sat::null_bool_var;
    }

    constraint* constraint_manager::get_bv2c(sat::bool_var bv) const {
        return m_bv2constraint.get(bv, nullptr);
    }

    constraint* constraint_manager::store(scoped_constraint_ptr scoped_c) {
        constraint* c = scoped_c.detach();
        LOG_V("Store constraint: " << show_deref(c));
        assign_bv2c(m_bvars.new_var(), c);
        while (m_constraints.size() <= c->level())
            m_constraints.push_back({});
        m_constraints[c->level()].push_back(c);
        return c;
    }

    clause* constraint_manager::store(clause_ref cl_ref) {
        clause* cl = cl_ref.get();
        while (m_clauses.size() <= cl->level())
            m_clauses.push_back({});
        m_clauses[cl->level()].push_back(std::move(cl_ref));
        return cl;
    }

    void constraint_manager::register_external(constraint* c) {
        SASSERT(c);
        SASSERT(c->unit_dep());
        SASSERT(c->unit_dep()->is_leaf());
        unsigned const dep = c->unit_dep()->leaf_value();
        SASSERT(!m_external_constraints.contains(dep));
        m_external_constraints.insert(dep, c);
    }

    // Release constraints at the given level and above.
    void constraint_manager::release_level(unsigned lvl) {
        for (unsigned l = m_constraints.size(); l-- > lvl; ) {
            for (auto* c : m_constraints[l]) {
                LOG_V("Destroying constraint: " << show_deref(c));
                auto* d = c->unit_dep();
                if (d && d->is_leaf()) {
                    unsigned const dep = d->leaf_value();
                    SASSERT(m_external_constraints.contains(dep));
                    m_external_constraints.remove(dep);
                }
                erase_bv2c(c);
            }
            m_constraints[l].reset();
        }
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
        auto it = m_constraint_table.find(c1);
        if (it == m_constraint_table.end())
            return c1;
        constraint* c0 = *it;
        // TODO: can this assertion be violated?
        // Yes, e.g.: constraint c was asserted at level 1, the conflict resolution derived ~c from c1,c2 at level 0...
        // In that case we have to adjust c0's level in the storage.
        // What about the level of the boolean variable? That depends on its position in the assignment stack and should probably stay where it is.
        // Will be updated separately when we patch the assignment stack.

        // NB code review: currently you separate dedup from insertion into the constraint table.
        // It seems more convenient to also ensure that the new constraint is inserted into the table at this point.
        // You also erase c from the constraint table in erase_bv2c.
        // again association with m_constraint_table seems to be only for deduplication purposes.
        //
        // the store function is used separately from solver::new_constraint
        // shouldn't it be combined with deduplication?
        // in this way we can fix the level if a new duplicate constraint is created at a lower level
#if 0
        auto it = m_constraint_table.find(c1);
        if (it == m_constraint_table.end()) {
            store(c1);
            m_constraint_table.insert(c1);
            return c1;
        }
        constraint* c0 = *it;
        if (c1->level() < c0->level()) {
            m_constraints[c0->level()].erase(c0);
            m_constraints[c1->level()].push_back(c0);
            c0->m_level = c1->level();
        }
        dealloc(c1);
        return c0;

#endif
        
        SASSERT(c0->level() <= c1->level());
        dealloc(c1);
        return c0;
    }

    scoped_signed_constraint constraint_manager::eq(unsigned lvl, pdd const& p) {
        return {dedup(alloc(eq_constraint, *this, lvl, p)), true};
    }

    scoped_signed_constraint constraint_manager::ule(unsigned lvl, pdd const& a, pdd const& b) {
        return {dedup(alloc(ule_constraint, *this, lvl, a, b)), true};
    }

    scoped_signed_constraint constraint_manager::ult(unsigned lvl, pdd const& a, pdd const& b) {
        // a < b  <=>  !(b <= a)
        return ~ule(lvl, b, a);
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
    scoped_signed_constraint constraint_manager::sle(unsigned lvl, pdd const& a, pdd const& b) {
        auto shift = rational::power_of_two(a.power_of_2() - 1);
        return ule(lvl, a + shift, b + shift);
    }

    scoped_signed_constraint constraint_manager::slt(unsigned lvl, pdd const& a, pdd const& b) {
        auto shift = rational::power_of_two(a.power_of_2() - 1);
        return ult(lvl, a + shift, b + shift);
    }

    eq_constraint& constraint::to_eq() { 
        return *dynamic_cast<eq_constraint*>(this); 
    }

    eq_constraint const& constraint::to_eq() const { 
        return *dynamic_cast<eq_constraint const*>(this); 
    }

    ule_constraint& constraint::to_ule() {
        return *dynamic_cast<ule_constraint*>(this);
    }

    ule_constraint const& constraint::to_ule() const {
        return *dynamic_cast<ule_constraint const*>(this);
    }

    std::ostream& constraint::display_extra(std::ostream& out, lbool status) const {
        out << " @" << level() << " (b" << bvar() << ")";
        (void)status;
        // if (is_positive()) out << " [pos]";
        // if (is_negative()) out << " [neg]";
        // if (is_undef()) out << " [inactive]";    // TODO: not sure if we still need/want this... decide later
        return out;
    }

    bool constraint::propagate(solver& s, bool is_positive, pvar v) {
        LOG_H3("Propagate " << s.m_vars[v] << " in " << *this);
        SASSERT(!vars().empty());
        unsigned idx = 0;
        if (vars()[idx] != v)
            idx = 1;
        SASSERT(v == vars()[idx]);
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
        unsigned other_v = vars()[idx];
        propagate_core(s, is_positive, v, other_v);
        return false;
    }

    void constraint::propagate_core(solver& s, bool is_positive, pvar v, pvar other_v) {
        (void)v;
        (void)other_v;
        narrow(s, is_positive);
    }

    clause_ref clause::from_unit(signed_constraint c, p_dependency_ref d) {
        SASSERT(c->has_bvar());
        unsigned const lvl = c->level();
        sat::literal_vector lits;
        lits.push_back(c.blit());
        return clause::from_literals(lvl, std::move(d), std::move(lits));
    }

    clause_ref clause::from_literals(unsigned lvl, p_dependency_ref d, sat::literal_vector literals) {
        return alloc(clause, lvl, std::move(d), std::move(literals));
    }

    bool clause::is_always_false(solver& s) const {
        return std::all_of(m_literals.begin(), m_literals.end(), [&s](sat::literal lit) {
            signed_constraint c = s.m_constraints.lookup(lit);
            return c.is_always_false();
        });
    }

    bool clause::is_currently_false(solver& s) const {
        return std::all_of(m_literals.begin(), m_literals.end(), [&s](sat::literal lit) {
            signed_constraint c = s.m_constraints.lookup(lit);
            return c.is_currently_false(s);
        });
    }

    bool clause::resolve(sat::bool_var var, clause const& other) {
        DEBUG_CODE({
            bool this_has_pos = std::count(begin(), end(), sat::literal(var)) > 0;
            bool this_has_neg = std::count(begin(), end(), ~sat::literal(var)) > 0;
            bool other_has_pos = std::count(other.begin(), other.end(), sat::literal(var)) > 0;
            bool other_has_neg = std::count(other.begin(), other.end(), ~sat::literal(var)) > 0;
            SASSERT(!this_has_pos || !this_has_neg);  // otherwise this is tautology
            SASSERT(!other_has_pos || !other_has_neg);  // otherwise other is tautology
            SASSERT((this_has_pos && other_has_neg) || (this_has_neg && other_has_pos));
        });
        // The resolved var should not be one of the new constraints
        int j = 0;
        for (auto lit : m_literals)
            if (lit.var() != var)
                m_literals[j++] = lit;
        m_literals.shrink(j);
        for (sat::literal lit : other)
            if (lit.var() != var)
                m_literals.push_back(lit);
        return true;
    }

    std::ostream& clause::display(std::ostream& out) const {
        bool first = true;
        for (auto lit : *this) {
            if (first)
                first = false;
            else
                out << " \\/ ";
            out << lit;
        }
        return out;
    }

}
