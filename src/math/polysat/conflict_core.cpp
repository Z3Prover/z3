/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/conflict_core.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"
#include "math/polysat/saturation.h"
#include "math/polysat/variable_elimination.h"
#include <algorithm>

namespace polysat {

    conflict_core::conflict_core(solver& s) {
        m_solver = &s;
        ve_engines.push_back(alloc(ve_reduction));
        // ve_engines.push_back(alloc(ve_forbidden_intervals));
        inf_engines.push_back(alloc(inf_polynomial_superposition));
        for (auto* engine : inf_engines)
            engine->set_solver(s);
    }

    conflict_core::~conflict_core() {}

    constraint_manager& conflict_core::cm() { return m_solver->m_constraints; }

    std::ostream& conflict_core::display(std::ostream& out) const {
        bool first = true;
        for (auto c : m_constraints) {
            if (first)
                first = false;
            else
                out << "  ;  ";
            out << c;
        }
        if (m_needs_model)
            out << "  ;  + current model";
        return out;
    }

    void conflict_core::set(std::nullptr_t) {
        SASSERT(empty());
        m_constraints.push_back({});
        m_needs_model = false;
    }

    void conflict_core::set(signed_constraint c) {
        LOG("Conflict: " << c);
        SASSERT(empty());
        m_needs_model = true;
        insert(c);
    }

    void conflict_core::set(pvar v) {
        LOG("Conflict: v" << v);
        SASSERT(empty());
        m_conflict_var = v;
        m_needs_model = true;
    }

    void conflict_core::insert(signed_constraint c) {
        SASSERT(!empty());  // should use set() to enter conflict state
        // Skip trivial constraints
        // (e.g., constant ones such as "4 > 1"... only true ones should appear, otherwise the lemma would be a tautology)
        if (c.is_always_true())
            return;
        SASSERT(!c.is_always_false());
        m_constraints.push_back(c);
    }

    void conflict_core::insert(signed_constraint c, vector<signed_constraint> premises) {
        insert(c);
        m_saturation_premises.insert(c, std::move(premises));  // TODO: map doesn't have move-insertion, so this still copies the vector. Maybe we want a clause_ref (but this doesn't work either since c doesn't have a boolean variable yet).
    }

    void conflict_core::resolve(constraint_manager const& m, sat::bool_var var, clause const& cl) {
        // Note: core: x, y, z; corresponds to clause ~x \/ ~y \/ ~z
        //       clause: x \/ u \/ v
        //       resolvent: ~y \/ ~z \/ u \/ v; as core: y, z, ~u, ~v

        SASSERT(!is_bailout());
        SASSERT(var != sat::null_bool_var);
        DEBUG_CODE({
            bool core_has_pos = std::count_if(begin(), end(), [var](auto c){ return c.blit() == sat::literal(var); }) > 0;
            bool core_has_neg = std::count_if(begin(), end(), [var](auto c){ return c.blit() == ~sat::literal(var); }) > 0;
            bool clause_has_pos = std::count(cl.begin(), cl.end(), sat::literal(var)) > 0;
            bool clause_has_neg = std::count(cl.begin(), cl.end(), ~sat::literal(var)) > 0;
            SASSERT(!core_has_pos || !core_has_neg);  // otherwise core is tautology
            SASSERT(!clause_has_pos || !clause_has_neg);  // otherwise clause is tautology
            SASSERT((core_has_pos && clause_has_pos) || (core_has_neg && clause_has_neg));
        });

        // TODO: maybe implement by marking literals instead (like SAT solvers are doing); if we need to iterate, keep an indexed_uint_set (from util/uint_set.h)
        //       (i.e., instead of keeping an explicit list of constraints as core, we just mark them.)
        //       (we still need the list though, for new/temporary constraints.)
        int j = 0;
        for (auto c : m_constraints)
            if (c->bvar() == var)
                m_constraints[j++] = c;
        m_constraints.shrink(j);

        for (sat::literal lit : cl)
            if (lit.var() != var)
                m_constraints.push_back(m.lookup(~lit));
    }

    clause_ref conflict_core::build_lemma() {
        sat::literal_vector literals;
        p_dependency_ref dep = m_solver->mk_dep_ref(null_dependency);
        unsigned lvl = 0;

        // TODO: try a final core reduction step?

        for (auto c : m_constraints) {
            if (!c->has_bvar()) {
                // temporary constraint -> keep it
                cm().ensure_bvar(c.get());
                // Insert the temporary constraint from saturation into \Gamma.
                auto it = m_saturation_premises.find_iterator(c);
                if (it != m_saturation_premises.end()) {
                    auto& premises = it->m_value;
                    clause_builder c_lemma(*m_solver);
                    for (auto premise : premises)
                        c_lemma.push_literal(~premise.blit());
                    c_lemma.push_literal(c.blit());
                    clause* cl = cm().store(c_lemma.build());
                    if (cl->size() == 1)
                        c->set_unit_clause(cl);
                    // TODO: actually, this should be backtrackable (unless clause is unit). But currently we cannot insert in the middle of the stack!
                    //      (or do it like MCSAT... they keep "theory-propagated" literals also at the end and restore them on backtracking)
                    m_solver->assign_bool_core(c.blit(), cl, nullptr);
                    m_solver->activate_constraint(c);
                }
            }
            if (c->unit_clause()) {
                dep = m_solver->m_dm.mk_join(dep, c->unit_dep());
                continue;
            }
            lvl = std::max(lvl, c->level());
            literals.push_back(~c.blit());
        }

        if (m_needs_model) {
            // TODO: add equalities corresponding to current model.
            //       until we properly track variables (use marks from solver?), we just use all of them (reverted decision and the following ones should have been popped from the stack)
            uint_set vars;
            for (auto c : m_constraints)
                for (pvar v : c->vars())
                    vars.insert(v);
            // Add v != val for each variable
            for (pvar v : vars) {
                auto diseq = ~cm().eq(lvl, m_solver->var(v) - m_solver->m_value[v]);
                cm().ensure_bvar(diseq.get());
                literals.push_back(diseq.blit());
            }
        }

        return clause::from_literals(lvl, std::move(dep), std::move(literals));
    }

    bool conflict_core::try_eliminate(pvar v) {
        // TODO: could be tracked incrementally when constraints are added/removed
        vector<signed_constraint> v_constraints;
        for (auto c : *this)
            if (c->contains_var(v)) {
                v_constraints.push_back(c);
                break;
            }

        // Variable already eliminated trivially (does this ever happen?)
        if (v_constraints.empty())
            return true;

        for (auto* engine : ve_engines)
            if (engine->perform(*m_solver, v, *this))
                return true;
        return false;
    }

    bool conflict_core::try_saturate(pvar v) {
        for (auto* engine : inf_engines)
            if (engine->perform(v, *this))
                return true;
        return false;
    }
}
