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
#include "math/polysat/explain.h"
#include "math/polysat/forbidden_intervals.h"
#include "math/polysat/saturation.h"
#include "math/polysat/variable_elimination.h"
#include <algorithm>

namespace polysat {

    conflict_core::conflict_core(solver& s) {
        m_solver = &s;
        ex_engines.push_back(alloc(ex_polynomial_superposition));
        for (auto* engine : ex_engines)
            engine->set_solver(s);
        ve_engines.push_back(alloc(ve_reduction));
        inf_engines.push_back(alloc(inf_saturate));
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
        LOG("inserting:" << c);
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

    void conflict_core::remove(signed_constraint c) {
        m_constraints.erase(c);
    }

    void conflict_core::replace(signed_constraint c_old, signed_constraint c_new, vector<signed_constraint> c_new_premises) {
        remove(c_old);
        insert(c_new, c_new_premises);
    }

    void conflict_core::remove_var(pvar v) {
        unsigned j = 0;
        for (unsigned i = 0; i < m_constraints.size(); ++i)
            if (!m_constraints[i]->contains_var(v))
                m_constraints[j++] = m_constraints[i];
        m_constraints.shrink(j);
    }

    void conflict_core::keep(signed_constraint c) {
        SASSERT(!c->has_bvar());
        cm().ensure_bvar(c.get());
        LOG("new constraint: " << c);
        // Insert the temporary constraint from saturation into \Gamma.
        handle_saturation_premises(c);
    }

    void conflict_core::resolve(constraint_manager const& m, sat::bool_var var, clause const& cl) {
        // Note: core: x, y, z; corresponds to clause ~x \/ ~y \/ ~z
        //       clause: x \/ u \/ v
        //       resolvent: ~y \/ ~z \/ u \/ v; as core: y, z, ~u, ~v

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
            if (c->bvar() != var)
                m_constraints[j++] = c;
        m_constraints.shrink(j);

        for (sat::literal lit : cl)
            if (lit.var() != var)
                m_constraints.push_back(m.lookup(~lit));
    }

    /** If the constraint c is a temporary constraint derived by core saturation, insert it (and recursively, its premises) into \Gamma */
    void conflict_core::handle_saturation_premises(signed_constraint c) {
        // NOTE: maybe we should skip intermediate steps and just collect the leaf premises for c?
        auto it = m_saturation_premises.find_iterator(c);
        if (it == m_saturation_premises.end())
            return;
        unsigned active_level = 0;
        auto& premises = it->m_value;
        clause_builder c_lemma(*m_solver);
        for (auto premise : premises) {
            handle_saturation_premises(premise);
            c_lemma.push(~premise.blit());
            active_level = std::max(active_level, m_solver->m_bvars.level(premise.blit()));
        }
        c_lemma.push(c.blit());
        clause* cl = cm().store(c_lemma.build());
        if (cl->size() == 1)
            c->set_unit_clause(cl);
        m_solver->propagate_bool_at(active_level, c.blit(), cl);
    }

    /** Create fallback lemma that excludes the current search state */
    /**
    * revisit: can prune literals further by slicing base on cone of influence
    * based on marked literals/variables on the stack. Only decisions that affect
    * marked items need to be included.
    */
    clause_builder conflict_core::build_fallback_lemma(unsigned lvl) {
        LOG_H3("Creating fallback lemma for level " << lvl);
        LOG_V("m_search: " << m_solver->m_search);
        clause_builder lemma(*m_solver);
        unsigned todo = lvl;
        unsigned i = 0;
        while (todo > 0) {
            auto const& item = m_solver->m_search[i++];
            if (!m_solver->is_decision(item))
                continue;
            LOG_V("Adding: " << item);
            if (item.is_assignment()) {
                pvar v = item.var();
                auto c = ~cm().eq(0, m_solver->var(v) - m_solver->m_value[v]);
                cm().ensure_bvar(c.get());
                lemma.push(c.blit());
            } else {
                sat::literal lit = item.lit();
                lemma.push(~lit);
            }
            --todo;
        }
        return lemma;
    }

    clause_builder conflict_core::build_core_lemma(unsigned model_level) {
        LOG_H3("Build lemma from core");
        LOG("core: " << *this);
        LOG("model_level: " << model_level);
        clause_builder lemma(*m_solver);

        // TODO: try a final core reduction step?

        for (auto c : m_constraints) {
            if (!c->has_bvar())
                keep(c);
            lemma.push(~c);
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
                // SASSERT(!m_solver->m_justification[v].is_unassigned());  // TODO: why does this trigger????
                if (m_solver->m_justification[v].is_unassigned())
                    continue;
                if (m_solver->m_justification[v].level() > model_level)
                    continue;
                auto diseq = ~cm().eq(lemma.level(), m_solver->var(v) - m_solver->m_value[v]);
                cm().ensure_bvar(diseq.get());
                lemma.push(diseq);
            }
        }

        return lemma;
    }

    clause_builder conflict_core::build_lemma(unsigned reverted_level) {
        if (!is_bailout())
            return build_core_lemma(reverted_level);
        else if (m_bailout_lemma)
            return *std::move(m_bailout_lemma);
        else
            return build_fallback_lemma(reverted_level);
    }

    bool conflict_core::resolve_value(pvar v, vector<signed_constraint> const& cjust_v) {
        // NOTE:
        // In the "standard" case where "v = val" is on the stack:
        //      - cjust_v contains true constraints
        //      - core contains both false and true constraints... (originally only false ones, but additional true ones may come from saturation?).
        // In the case where no assignment to v is on the stack, i.e., conflict_var == v and viable(v) = \emptyset:
        //      - the constraints in cjust_v cannot be evaluated.
        //      - for now, we just pick a value. TODO: revise later
        /*
        if (conflict_var() == v) {
            // Temporary assignment
            // (actually we shouldn't just pick any value, but one that makes at least one constraint true...)
            LOG_H1("WARNING: temporary assignment of conflict_var");
            m_solver->assign_core(v, m_solver->m_value[v], justification::propagation(m_solver->m_level));
        }
        */
        if (conflict_var() == v) {
            clause_builder lemma(s());
            forbidden_intervals fi;
            if (fi.perform(s(), v, *this, lemma)) {
                set_bailout();
                m_bailout_lemma = std::move(lemma);
                return true;
            }
        }

        for (auto c : cjust_v)
            insert(c);

        for (auto* engine : ex_engines)
            if (engine->try_explain(v, *this))
                return true;

        // No value resolution method was successful => fall back to saturation and variable elimination
        while (true) {  // TODO: limit?
            // TODO: as a last resort, substitute v by m_value[v]?
            if (!try_saturate(v))
                break;
            if (try_eliminate(v))
                return true;
        }
        return false;
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
