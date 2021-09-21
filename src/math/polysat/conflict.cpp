/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

Notes:

 TODO: constraints containing v could be tracked incrementally when constraints are added/removed using an index.

 TODO: try a final core reduction step or other core minimization

TODO: If we have e.g. 4x+y=2 and y=0, then we have a conflict no matter the value of x, so we should drop x=? from the core.
      (works currently if x is unassigned; for other cases we would need extra info from constraint::is_currently_false)

--*/

#include "math/polysat/conflict.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"
#include "math/polysat/explain.h"
#include "math/polysat/forbidden_intervals.h"
#include "math/polysat/saturation.h"
#include "math/polysat/variable_elimination.h"
#include <algorithm>

namespace polysat {

    conflict::conflict(solver& s) {
        m_solver = &s;
        ex_engines.push_back(alloc(ex_polynomial_superposition));
        for (auto* engine : ex_engines)
            engine->set_solver(s);
        ve_engines.push_back(alloc(ve_reduction));
        inf_engines.push_back(alloc(inf_saturate));
        for (auto* engine : inf_engines)
            engine->set_solver(s);
    }

    conflict::~conflict() {}

    constraint_manager& conflict::cm() const { return s().m_constraints; }

    std::ostream& conflict::display(std::ostream& out) const {
        char const* sep = "";
        for (auto c : *this) 
            out << sep << c->bvar2string() << " " << c, sep = " ; ";
        if (!m_vars.empty())
            out << " vars";
        for (auto v : m_vars)
            out << " v" << v;
        return out;
    }

    void conflict::reset() {
        for (auto c : *this)
            unset_mark(c);
        m_constraints.reset();
        m_literals.reset();
        m_vars.reset();
        m_conflict_var = null_var;
        m_saturation_premises.reset();
        m_bailout = false;
        SASSERT(empty());        
    }

    /**
    * The constraint is false under the current assignment of variables.
    * The core is then the conjuction of this constraint and assigned variables.
    */
    void conflict::set(signed_constraint c) {
        LOG("Conflict: " << c);
        SASSERT(empty());
        c->set_var_dependent();
        insert(c);       
        SASSERT(!empty());
    }

    /**
    * The variable v cannot be assigned.
    * The conflict is the set of justifications accumulated for the viable values for v.
    * These constraints are (in the current form) not added to the core, but passed directly 
    * to the forbidden interval module.
    * A consistent approach could be to add these constraints to the core and then also include the
    * variable assignments.
    */
    void conflict::set(pvar v) {
        LOG("Conflict: v" << v);
        SASSERT(empty());
        m_conflict_var = v;
        for (auto c : s().m_cjust[v]) {
            c->set_var_dependent();
            insert(c);
        }
        SASSERT(!empty());
    }

    void conflict::set(clause const& cl) {
        LOG("Conflict: " << cl);
        SASSERT(empty());
        for (auto lit : cl) {
            auto c = s().lit2cnstr(lit);
            c->set_var_dependent();
            insert(~c);
        }
        SASSERT(!empty());
    }

    void conflict::insert(signed_constraint c) {
        LOG("inserting: " << c);
        // Skip trivial constraints
        // (e.g., constant ones such as "4 > 1"... only true ones should appear, otherwise the lemma would be a tautology)
        if (c.is_always_true())
            return;
        if (c->is_marked())
            return;
        set_mark(c);
        if (c->has_bvar())
            insert_literal(c.blit());
        else
            m_constraints.push_back(c);
    }

    void conflict::insert(signed_constraint c, vector<signed_constraint> premises) {
        insert(c);
        m_saturation_premises.insert(c, std::move(premises));  // TODO: map doesn't have move-insertion, so this still copies the vector.
    }

    void conflict::remove(signed_constraint c) {
        unset_mark(c);       
        if (c->has_bvar()) {
            SASSERT(std::count(m_constraints.begin(), m_constraints.end(), c) == 0);
            remove_literal(c.blit());
        }
        else
            m_constraints.erase(c);
    }

    void conflict::replace(signed_constraint c_old, signed_constraint c_new, vector<signed_constraint> c_new_premises) {
        remove(c_old);
        insert(c_new, c_new_premises);
    }

    void conflict::set_bailout() {
        SASSERT(!is_bailout());
        m_bailout = true;
        s().m_stats.m_num_bailouts++;
    }

    void conflict::resolve(constraint_manager const& m, sat::bool_var var, clause const& cl) {
        // Note: core: x, y, z; corresponds to clause ~x \/ ~y \/ ~z
        //       clause: x \/ u \/ v
        //       resolvent: ~y \/ ~z \/ u \/ v; as core: y, z, ~u, ~v

        SASSERT(var != sat::null_bool_var);
        SASSERT(std::all_of(m_constraints.begin(), m_constraints.end(), [](auto c){ return !c->has_bvar(); }));
        bool core_has_pos = contains_literal(sat::literal(var));
        bool core_has_neg = contains_literal(~sat::literal(var));
        DEBUG_CODE({
            bool clause_has_pos = std::count(cl.begin(), cl.end(), sat::literal(var)) > 0;
            bool clause_has_neg = std::count(cl.begin(), cl.end(), ~sat::literal(var)) > 0;
            SASSERT(!core_has_pos || !core_has_neg);  // otherwise core is tautology
            SASSERT(!clause_has_pos || !clause_has_neg);  // otherwise clause is tautology
            SASSERT((core_has_pos && clause_has_pos) || (core_has_neg && clause_has_neg));
        });

        sat::literal var_lit(var);
        if (core_has_pos)
            remove_literal(var_lit);
        if (core_has_neg)
            remove_literal(~var_lit);
        
        unset_mark(m.lookup(var_lit));
        
        for (sat::literal lit : cl)
            if (lit.var() != var)
                insert(m.lookup(~lit));
    }

    /** If the constraint c is a temporary constraint derived by core saturation, insert it (and recursively, its premises) into \Gamma */
    void conflict::keep(signed_constraint c) {
        if (!c->has_bvar()) {
            remove(c);
            cm().ensure_bvar(c.get());
            insert(c);
        }
        LOG_H3("keeping: " << c);
        // NOTE: maybe we should skip intermediate steps and just collect the leaf premises for c?
        auto it = m_saturation_premises.find_iterator(c);
        if (it == m_saturation_premises.end())
            return;
        auto& premises = it->m_value;
        clause_builder c_lemma(s());
        for (auto premise : premises) {
            LOG_H3("premise: " << premise);
            keep(premise);
            SASSERT(premise->has_bvar());
            SASSERT(premise.is_currently_true(s()) || premise.bvalue(s()) == l_true);
            // otherwise the propagation doesn't make sense
            c_lemma.push(~premise.blit());
        }
        c_lemma.push(c.blit());
        clause_ref lemma = c_lemma.build();
        cm().store(lemma.get(), s());
        if (s().m_bvars.value(c.blit()) == l_undef)
            s().assign_bool(s().level(*lemma), c.blit(), lemma.get(), nullptr);
    }

    clause_builder conflict::build_lemma() {
        LOG_H3("Build lemma from core");
        LOG("core: " << *this);
        clause_builder lemma(s());

        while (!m_constraints.empty()) {
            signed_constraint c = m_constraints.back();
            SASSERT(!c->has_bvar());
            keep(c);
        }

        for (auto c : *this)
            lemma.push(~c);

        for (unsigned v : m_vars) {
            if (!is_pmarked(v))
                continue;
            SASSERT(s().is_assigned(v));  // note that we may have added too many variables: e.g., y disappears in x*y if x=0
            if (!s().is_assigned(v))
                continue;
            auto diseq = ~s().eq(s().var(v), s().get_value(v));
            cm().ensure_bvar(diseq.get());
            lemma.push(diseq);
        }        

        return lemma;
    }


    bool conflict::resolve_value(pvar v, vector<signed_constraint> const& cjust_v) {
        // NOTE:
        // In the "standard" case where "v = val" is on the stack:
        //      - cjust_v contains true constraints
        //      - core contains both false and true constraints (originally only false ones, but additional true ones may come from saturation)

        if (is_bailout())
            return false;

        if (conflict_var() == v) {
            forbidden_intervals fi;
            if (fi.perform(s(), v, cjust_v, *this))
                return true;
        }

        m_vars.remove(v);

        for (auto c : cjust_v)
            insert(c);

        for (auto* engine : ex_engines)
            if (engine->try_explain(v, *this))
                return true;

        // No value resolution method was successful => fall back to saturation and variable elimination
        while (s().inc()) {
            // TODO: as a last resort, substitute v by m_value[v]?
            if (try_eliminate(v))
                return true;
            if (!try_saturate(v))
                break;
        }
        set_bailout();
        m_vars.insert(v);
        return false;
    }

    bool conflict::try_eliminate(pvar v) {       
        bool has_v = false;
        for (auto c : *this)
            has_v |= c->contains_var(v);
        if (!has_v)
            return true;
        for (auto* engine : ve_engines)
            if (engine->perform(s(), v, *this))
                return true;
        return false;
    }

    bool conflict::try_saturate(pvar v) {
        for (auto* engine : inf_engines)
            if (engine->perform(v, *this))
                return true;
        return false;
    }

    void conflict::set_mark(signed_constraint c) {
        if (c->is_marked())
            return;
        c->set_mark();
        if (c->has_bvar())
            set_bmark(c->bvar());    
        if (c->is_var_dependent()) {
            for (auto v : c->vars()) {
                if (s().is_assigned(v))
                    m_vars.insert(v);
                inc_pref(v);
            }
        }
    }

    void conflict::unset_mark(signed_constraint c) {
        if (!c->is_marked())
            return;
        c->unset_mark();
        if (c->has_bvar())
            unset_bmark(c->bvar());
        if (c->is_var_dependent()) {
            c->unset_var_dependent();
            for (auto v : c->vars())
                dec_pref(v);
        }
    }

    void conflict::inc_pref(pvar v) {
        if (v >= m_pvar2count.size())
            m_pvar2count.resize(v + 1);
        m_pvar2count[v]++;
    }

    void conflict::dec_pref(pvar v) {
        SASSERT(m_pvar2count[v] > 0);
        m_pvar2count[v]--;
    }

    bool conflict::is_pmarked(pvar v) const {
        return m_pvar2count.get(v, 0) > 0;
    }

    void conflict::set_bmark(sat::bool_var b) {
        if (b >= m_bvar2mark.size())
            m_bvar2mark.resize(b + 1);
        SASSERT(!m_bvar2mark[b]);
        m_bvar2mark[b] = true;
    }

    void conflict::unset_bmark(sat::bool_var b) {
        SASSERT(m_bvar2mark[b]);
        m_bvar2mark[b] = false;
    }

    bool conflict::is_bmarked(sat::bool_var b) const {
        return m_bvar2mark.get(b, false);
    }

    bool conflict::contains_literal(sat::literal lit) const {
        return m_literals.contains(lit.to_uint());
    }

    void conflict::insert_literal(sat::literal lit) {
        m_literals.insert(lit.to_uint());
    }

    void conflict::remove_literal(sat::literal lit) {
        m_literals.remove(lit.to_uint());
    }

}
