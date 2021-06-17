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

    constraint* constraint_manager::insert(constraint_ref c) {
        LOG_V("Inserting constraint: " << show_deref(c));
        SASSERT(c);
        SASSERT(c->bvar() != sat::null_bool_var);
        SASSERT(get_bv2c(c->bvar()) == c.get());
        // TODO: use explicit insert_external(constraint* c, unsigned dep) for that.
        if (c->dep() && c->dep()->is_leaf()) {
            unsigned dep = c->dep()->leaf_value();
            SASSERT(!m_external_constraints.contains(dep));
            m_external_constraints.insert(dep, c.get());
        }
        while (m_constraints.size() <= c->level())
            m_constraints.push_back({});
        constraint* pc = c.get();
        m_constraints[c->level()].push_back(std::move(c));
        return pc;
    }

    clause* constraint_manager::insert(clause_ref cl) {
        SASSERT(cl);
        // Insert new constraints
        for (constraint* c : cl->m_new_constraints)
            // TODO: if (!inserted) ?
            insert(c);
        cl->m_new_constraints = {};  // free vector memory
        // Insert clause
        while (m_clauses.size() <= cl->level())
            m_clauses.push_back({});
        clause* pcl = cl.get();
        m_clauses[cl->level()].push_back(std::move(cl));
        return pcl;
    }

    // Release constraints at the given level and above.
    void constraint_manager::release_level(unsigned lvl) {
        for (unsigned l = m_clauses.size(); l-- > lvl; ) {
            for (auto const& cl : m_clauses[l]) {
                SASSERT_EQ(cl->m_ref_count, 1);  // otherwise there is a leftover reference somewhere
            }
            m_clauses[l].reset();
        }
        for (unsigned l = m_constraints.size(); l-- > lvl; ) {
            for (auto const& c : m_constraints[l]) {
                LOG_V("Removing constraint: " << show_deref(c));
                SASSERT_EQ(c->m_ref_count, 1);  // otherwise there is a leftover reference somewhere
                if (c->dep() && c->dep()->is_leaf()) {
                    unsigned dep = c->dep()->leaf_value();
                    SASSERT(m_external_constraints.contains(dep));
                    m_external_constraints.remove(dep);
                }
            }
            m_constraints[l].reset();
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

    constraint_ref constraint_manager::eq(unsigned lvl, csign_t sign, pdd const& p, p_dependency_ref const& d) {
        return alloc(eq_constraint, *this, lvl, sign, p, d);
    }

    constraint_ref constraint_manager::viable(unsigned lvl, csign_t sign, pvar v, bdd const& b, p_dependency_ref const& d) {
        return alloc(var_constraint, *this, lvl, sign, v, b, d);
    }

    constraint_ref constraint_manager::ule(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d) {
        return alloc(ule_constraint, *this, lvl, sign, a, b, d);
    }

    constraint_ref constraint_manager::ult(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d) {
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
    constraint_ref constraint_manager::sle(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d) {
        auto shift = rational::power_of_two(a.power_of_2() - 1);
        return ule(lvl, sign, a + shift, b + shift, d);
    }

    constraint_ref constraint_manager::slt(unsigned lvl, csign_t sign, pdd const& a, pdd const& b, p_dependency_ref const& d) {
        auto shift = rational::power_of_two(a.power_of_2() - 1);
        return ult(lvl, sign, a + shift, b + shift, d);
    }

    std::ostream& constraint::display_extra(std::ostream& out) const {
        out << " @" << level() << " (b" << bvar() << ")";
        if (is_undef())
            out << " [inactive]";
        return out;
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

    clause_ref clause::from_unit(constraint_ref c) {
        SASSERT(c);
        unsigned const lvl = c->level();
        auto const& dep = c->m_dep;
        sat::literal_vector lits;
        lits.push_back(sat::literal(c->bvar()));
        constraint_ref_vector cs;
        cs.push_back(std::move(c));
        return clause::from_literals(lvl, dep, std::move(lits), std::move(cs));
    }

    clause_ref clause::from_literals(unsigned lvl, p_dependency_ref const& d, sat::literal_vector literals, constraint_ref_vector constraints) {
        return alloc(clause, lvl, d, literals, constraints);
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
        SASSERT(std::all_of(new_constraints().begin(), new_constraints().end(), [var](constraint* c) { return c->bvar() != var; }));
        SASSERT(std::all_of(other.new_constraints().begin(), other.new_constraints().end(), [var](constraint* c) { return c->bvar() != var; }));
        int j = 0;
        for (int i = 0; i < m_literals.size(); ++i)
            if (m_literals[i].var() != var)
                m_literals[j++] = m_literals[i];
        m_literals.shrink(j);
        for (sat::literal lit : other.literals())
            if (lit.var() != var)
                m_literals.push_back(lit);
        return true;
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

    void clause_builder::reset() {
        m_literals.reset();
        m_new_constraints.reset();
        SASSERT(empty());
    }

    clause_ref clause_builder::build(unsigned lvl, p_dependency_ref const& d) {
        clause_ref cl = clause::from_literals(lvl, d, std::move(m_literals), std::move(m_new_constraints));
        SASSERT(empty());
        return cl;
    }

    void clause_builder::push_literal(sat::literal lit) {
        if (m_solver.active_at_base_level(lit))
            return;
        m_literals.push_back(lit);
    }

    void clause_builder::push_new_constraint(constraint_ref c) {
        SASSERT(c);
        SASSERT(c->is_undef());
        sat::literal lit{c->bvar()};
        tmp_assign _t(c, lit);
        if (c->is_always_false())
            return;
        m_literals.push_back(lit);
        m_new_constraints.push_back(std::move(c));
    }

    std::ostream& constraints_and_clauses::display(std::ostream& out) const {
        bool first = true;
        for (auto c : units()) {
            if (first)
                first = false;
            else
                out << "  ;  ";
            out << show_deref(c);
        }
        for (auto cl : clauses()) {
            if (first)
                first = false;
            else
                out << "  ;  ";
            out << show_deref(cl);
        }
        return out;
    }
}
