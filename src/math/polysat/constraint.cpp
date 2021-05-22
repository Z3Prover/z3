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
#include "math/polysat/var_constraint.h"
#include "math/polysat/eq_constraint.h"
#include "math/polysat/ule_constraint.h"

namespace polysat {

    constraint* constraint_manager::insert(scoped_ptr<constraint>&& sc) {
        constraint* c = sc.detach();
        LOG_V("Inserting constraint: " << show_deref(c));
        SASSERT(c);
        SASSERT(c->bvar() != sat::null_bool_var);
        SASSERT(get_bv2c(c->bvar()) == nullptr);
        insert_bv2c(c->bvar(), c);
        // TODO: use explicit insert_external(constraint* c, unsigned dep) for that.
        if (c->dep() && c->dep()->is_leaf()) {
            unsigned dep = c->dep()->leaf_value();
            SASSERT(!m_external_constraints.contains(dep));
            m_external_constraints.insert(dep, c);
        }
        while (m_constraints.size() <= c->level())
            m_constraints.push_back({});
        m_constraints[c->level()].push_back(c);
        return c;
    }

    // Release constraints at the given level and above.
    void constraint_manager::release_level(unsigned lvl) {
        for (unsigned l = m_constraints.size(); l-- > lvl; ) {
            for (constraint* c : m_constraints[l]) {
                LOG_V("Removing constraint: " << show_deref(c));
                erase_bv2c(c->bvar());
                if (c->dep() && c->dep()->is_leaf()) {
                    unsigned dep = c->dep()->leaf_value();
                    SASSERT(m_external_constraints.contains(dep));
                    m_external_constraints.remove(dep);
                }
            }
            m_constraints[l].reset();
        }
    }

    constraint* constraint_manager::lookup(sat::bool_var var) const {
        return get_bv2c(var);
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

    var_constraint& constraint::to_bit() {
        return *dynamic_cast<var_constraint*>(this);
    }

    var_constraint const& constraint::to_bit() const {
        return *dynamic_cast<var_constraint const*>(this);
    }

    scoped_ptr<constraint> constraint_manager::eq(unsigned lvl, csign_t sign, pdd const& p, p_dependency_ref const& d) {
        return alloc(eq_constraint, *this, lvl, sign, p, d);
    }

    scoped_ptr<constraint> constraint_manager::viable(unsigned lvl, csign_t sign, pvar v, bdd const& b, p_dependency_ref const& d) {
        return alloc(var_constraint, *this, lvl, sign, v, b, d);
    }

    scoped_ptr<constraint> constraint_manager::ule(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d) {
        return alloc(ule_constraint, *this, lvl, sign, a, b, d);
    }

    scoped_ptr<constraint> constraint_manager::ult(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d) {
        // a < b  <=>  !(b <= a)
        return ule(lvl, static_cast<csign_t>(!sign), b, a, d);
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
    scoped_ptr<constraint> constraint_manager::sle(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d) {
        auto shift = rational::power_of_two(a.power_of_2() - 1);
        return ule(lvl, sign, a + shift, b + shift, d);
    }

    scoped_ptr<constraint> constraint_manager::slt(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d) {
        auto shift = rational::power_of_two(a.power_of_2() - 1);
        return ult(lvl, sign, a + shift, b + shift, d);
    }

    bool constraint::propagate(solver& s, pvar v) {
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
                s.add_watch(*this, other_v);
                std::swap(vars()[idx], vars()[i]);
                return true;
            }
        }
        // at most one variable remains unassigned.
        unsigned other_v = vars()[idx];
        propagate_core(s, v, other_v);
        return false;
    }

    void constraint::propagate_core(solver& s, pvar v, pvar other_v) {
        (void)v;
        (void)other_v;
        narrow(s);
    }

    clause* clause::from_literals(unsigned lvl, p_dependency_ref const& d, sat::literal_vector const& literals) {
        return alloc(clause, lvl, d, literals);
    }

    bool clause::is_always_false(solver& s) const {
        return std::all_of(m_literals.begin(), m_literals.end(), [&s](sat::literal lit) {
            constraint *c = s.m_constraints.lookup(lit.var());
            return c->is_always_false();
        });
    }

    bool clause::is_currently_false(solver& s) const {
        return std::all_of(m_literals.begin(), m_literals.end(), [&s](sat::literal lit) {
            constraint *c = s.m_constraints.lookup(lit.var());
            return c->is_currently_false(s);
        });
    }
    std::ostream& clause::display(std::ostream& out) const {
        bool first = true;
        for (auto lit : literals()) {
            if (first)
                first = false;
            else
                out << " \\/ ";
            out << lit;
        }
        return out;
    }

    scoped_clause::scoped_clause(scoped_ptr<constraint>&& c) {
        SASSERT(c);
        sat::literal_vector lits;
        lits.push_back(sat::literal(c->bvar()));
        m_clause = clause::from_literals(c->level(), c->m_dep, lits);
        m_owned.push_back(c.detach());
    }

    std::ostream& scoped_clause::display(std::ostream& out) const {
        if (m_clause)
            return out << *m_clause;
        else
            return out << "<NULL>";
    }

    std::ostream& constraints_and_clauses::display(std::ostream& out) const {
        bool first = true;
        for (auto* c : units()) {
            if (first)
                first = false;
            else
                out << "  ;  ";
            out << show_deref(c);
        }
        for (auto* cl : clauses()) {
            if (first)
                first = false;
            else
                out << "  ;  ";
            out << show_deref(cl);
        }
        return out;
    }
}
