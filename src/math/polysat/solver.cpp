/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat

Abstract:

    Polynomial solver for modular arithmetic.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/

#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/polysat_params.hpp"
#include <variant>

// For development; to be removed once the linear solver works well enough
#define ENABLE_LINEAR_SOLVER 0

namespace polysat {

    solver::solver(reslimit& lim):
        m_lim(lim),
        m_viable(*this),
        m_viable_fallback(*this),
        m_linear_solver(*this),
        m_conflict(*this),
        m_simplify_clause(*this),
        m_simplify(*this),
        m_restart(*this),
        m_bvars(),
        m_free_pvars(m_activity),
        m_constraints(*this),
        m_search(*this) {
    }

    solver::~solver() {
        // Need to remove any lingering clause/constraint references before the constraint manager is destructed
        m_conflict.reset();
    }

    void solver::updt_params(params_ref const& p) {
        polysat_params pp(p);
        m_params.append(p);
        m_config.m_max_conflicts = m_params.get_uint("max_conflicts", UINT_MAX);
        m_config.m_max_decisions = m_params.get_uint("max_decisions", UINT_MAX);
        m_config.m_log_conflicts = pp.log_conflicts();
    }

    bool solver::should_search() {
        return
            m_lim.inc() &&
            (m_stats.m_num_conflicts < get_config().m_max_conflicts) &&
            (m_stats.m_num_decisions < get_config().m_max_decisions);
    }

    lbool solver::check_sat() {
        LOG("Starting");
        while (should_search()) {
            m_stats.m_num_iterations++;
            LOG_H1("Next solving loop iteration (#" << m_stats.m_num_iterations << ")");
            LOG("Free variables: " << m_free_pvars);
            LOG("Assignment:     " << assignments_pp(*this));
            if (is_conflict()) LOG("Conflict:       " << m_conflict);
            IF_LOGGING(m_viable.log());
            if (is_conflict() && at_base_level()) { LOG_H2("UNSAT"); return l_false; }
            else if (is_conflict()) resolve_conflict();
            else if (can_propagate()) propagate();
            else if (!can_decide()) { LOG_H2("SAT"); SASSERT(verify_sat()); return l_true; }
            else if (m_constraints.should_gc()) m_constraints.gc();
            else if (m_simplify.should_apply()) m_simplify();
            else if (m_restart.should_apply()) m_restart();
            else decide();
        }
        LOG_H2("UNDEF (resource limit)");
        return l_undef;
    }

    lbool solver::unit_propagate() {
        return l_undef;
        // disabled to allow debugging unsoundness for watched literals
        flet<uint64_t> _max_d(m_config.m_max_conflicts, m_stats.m_num_conflicts + 2);
        return check_sat();
    }

    dd::pdd_manager& solver::sz2pdd(unsigned sz) const {
        m_pdd.reserve(sz + 1);
        if (!m_pdd[sz])
            m_pdd.set(sz, alloc(dd::pdd_manager, 1000, dd::pdd_manager::semantics::mod2N_e, sz));
        return *m_pdd[sz];
    }

    dd::pdd_manager& solver::var2pdd(pvar v) const {
        return sz2pdd(size(v));
    }

    unsigned solver::add_var(unsigned sz) {
        pvar v = m_value.size();
        m_value.push_back(rational::zero());
        m_justification.push_back(justification::unassigned());
        m_viable.push_var(sz);
        m_viable_fallback.push_var(sz);
        m_pwatch.push_back({});
        m_activity.push_back(0);
        m_vars.push_back(sz2pdd(sz).mk_var(v));
        m_size.push_back(sz);
        m_trail.push_back(trail_instr_t::add_var_i);
        m_free_pvars.mk_var_eh(v);
        return v;
    }

    pdd solver::value(rational const& v, unsigned sz) {
        return sz2pdd(sz).mk_val(v);
    }

    void solver::del_var() {
        NOT_IMPLEMENTED_YET();  // need to take care of helper variables in learned constraints, arising e.g. from bitwise "and"-terms.
        // TODO also remove v from all learned constraints.
        pvar v = m_value.size() - 1;
        m_viable.pop_var();
        m_viable_fallback.pop_var();
        m_value.pop_back();
        m_justification.pop_back();
        m_pwatch.pop_back();
        m_activity.pop_back();
        m_vars.pop_back();
        m_size.pop_back();
        m_free_pvars.del_var_eh(v);
    }

    void solver::assign_eh(signed_constraint c, dependency dep) {
        backjump(base_level());
        SASSERT(at_base_level());
        SASSERT(c);
        if (is_conflict())
            return;  // no need to do anything if we already have a conflict at base level
        sat::literal lit = c.blit();
        LOG("New constraint: " << c);
        switch (m_bvars.value(lit)) {
        case l_false:
            // Input literal contradicts current boolean state (e.g., opposite literals in the input)
            // => conflict only flags the inconsistency
            set_conflict_at_base_level();
            SASSERT(dep == null_dependency && "track dependencies is TODO");
            return;
        case l_true:
            // constraint c is already asserted
            SASSERT(m_bvars.level(lit) <= m_level);
            break;
        case l_undef:
            if (c.is_always_false()) {
                LOG("Always false: " << c);
                // asserted an always-false constraint
                set_conflict_at_base_level();
                return;
            }
            m_bvars.assumption(lit, m_level, dep);
            m_trail.push_back(trail_instr_t::assign_bool_i);
            m_search.push_boolean(lit);
            if (c.is_currently_false(*this))
                set_conflict(c);
            break;
        default:
            UNREACHABLE();
        }
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.new_constraint(*c.get());
#endif
    }


    bool solver::can_propagate() {
        return m_qhead < m_search.size() && !is_conflict();
    }

    void solver::propagate() {
        if (!can_propagate())
            return;
#ifndef NDEBUG
        SASSERT(!m_propagating);
        flet<bool> save_(m_propagating, true);
#endif
        push_qhead();
        while (can_propagate()) {
            auto const& item = m_search[m_qhead++];
            if (item.is_assignment())
                propagate(item.var());
            else
                propagate(item.lit());
        }
        if (!is_conflict())
            linear_propagate();
        SASSERT(wlist_invariant());
        SASSERT(assignment_invariant());
    }

    /**
    * Propagate assignment to a Boolean variable
    */
    void solver::propagate(sat::literal lit) {
        LOG_H2("Propagate bool " << lit << "@" << m_bvars.level(lit) << " " << m_level << " qhead: " << m_qhead);
        LOG("Literal " << lit_pp(*this, lit));
        signed_constraint c = lit2cnstr(lit);
        SASSERT(c);
        // TODO: review active and activate_constraint
        if (c->is_active())
            return;
        activate_constraint(c);
        auto& wlist = m_bvars.watch(~lit);
        unsigned i = 0, j = 0, sz = wlist.size();
        for (; i < sz && !is_conflict(); ++i)
            if (!propagate(lit, *wlist[i]))
                wlist[j++] = wlist[i];
        for (; i < sz; ++i)
            wlist[j++] = wlist[i];
        wlist.shrink(j);
    }

    /**
    * Propagate assignment to a pvar
    */
    void solver::propagate(pvar v) {
        LOG_H2("Propagate " << assignment_pp(*this, v, get_value(v)));
        SASSERT(!m_locked_wlist);
        DEBUG_CODE(m_locked_wlist = v;);
        auto& wlist = m_pwatch[v];
        unsigned i = 0, j = 0, sz = wlist.size();
        for (; i < sz && !is_conflict(); ++i)
            if (!propagate(v, wlist[i]))
                wlist[j++] = wlist[i];
        for (; i < sz; ++i)
            wlist[j++] = wlist[i];
        wlist.shrink(j);
        DEBUG_CODE(m_locked_wlist = std::nullopt;);
    }

    /**
     * Propagate assignment to variable v into constraint c.
     * Return true if a new watch was found; or false to keep the existing one.
     */
    bool solver::propagate(pvar v, constraint* c) {
        LOG_H3("Propagate " << m_vars[v] << " in " << constraint_pp(c, m_bvars.value(c->bvar())));
        SASSERT(is_assigned(v));
        SASSERT(!c->vars().empty());
        unsigned idx = 0;
        if (c->var(idx) != v)
            idx = 1;
        SASSERT(v == c->var(idx));
        // find other watch variable.
        for (unsigned i = c->vars().size(); i-- > 2; ) {
            unsigned other_v = c->vars()[i];
            if (!is_assigned(other_v)) {
                add_pwatch(c, other_v);
                std::swap(c->vars()[idx], c->vars()[i]);
                return true;
            }
        }
        // at most one poly variable remains unassigned.
        if (m_bvars.is_assigned(c->bvar())) {
            // constraint state: bool-propagated
            // // constraint is active, propagate it
            // SASSERT(c->is_active());   // TODO: what exactly does 'active' mean now ... use 'pwatched' and similar instead, to make meaning explicit?
            signed_constraint sc(c, m_bvars.value(c->bvar()) == l_true);
            if (c->vars().size() >= 2) {
                unsigned other_v = c->var(1 - idx);
                if (!is_assigned(other_v))
                    m_viable_fallback.push_constraint(other_v, sc);
            }
            sc.narrow(*this, false);
        } else {
            // constraint state: active but unassigned (bvalue undef, but pwatch is set and active; e.g., new constraints generated for lemmas)
            // // constraint is not yet active, try to evaluate it
            // SASSERT(!c->is_active());
            if (c->vars().size() >= 2) {
                unsigned other_v = c->var(1 - idx);
                // Wait for the remaining variable to be assigned
                // (although sometimes we would be able to evaluate constraints earlier)
                if (!is_assigned(other_v))
                    return false;
            }
            // Evaluate constraint
            signed_constraint sc(c, true);
            if (sc.is_currently_true(*this))
                assign_eval(sc.blit());
            else {
                SASSERT(sc.is_currently_false(*this));
                assign_eval(~sc.blit());
            }
        }
        return false;
    }

    /**
     * Propagate boolean assignment of literal lit into clause cl.
     * Return true if a new watch was found; or false to keep the existing one.
     */
    bool solver::propagate(sat::literal lit, clause& cl) {
        SASSERT(m_bvars.is_true(lit));
        SASSERT(cl.size() >= 2);
        unsigned idx = (cl[0] == ~lit) ? 1 : 0;
        SASSERT(cl[1 - idx] == ~lit);
        if (m_bvars.is_true(cl[idx]))
            return false;
        unsigned i = 2;
        for (; i < cl.size() && m_bvars.is_false(cl[i]); ++i);
        if (i < cl.size()) {
            // found non-false literal in cl; watch it instead
            m_bvars.watch(cl[i]).push_back(&cl);
            std::swap(cl[1 - idx], cl[i]);
            return true;
        }
        // all literals in cl are false, except possibly the other watch cl[idx]
        if (m_bvars.is_false(cl[idx]))
            set_conflict(cl);
        else
            assign_propagate(cl[idx], cl);
        return false;
    }

    void solver::linear_propagate() {
#if ENABLE_LINEAR_SOLVER
        switch (m_linear_solver.check()) {
        case l_false:
            // TODO extract conflict
            break;
        default:
            break;
        }
#endif
    }

    void solver::add_pwatch(constraint* c) {
        SASSERT(c);
        if (c->is_pwatched())
            return;
        auto& vars = c->vars();
        unsigned i = 0, j = 0, sz = vars.size();
        for (; i < sz && j < 2; ++i)
            if (!is_assigned(vars[i]))
                std::swap(vars[i], vars[j++]);
        if (vars.size() > 0)
            add_pwatch(c, vars[0]);
        if (vars.size() > 1)
            add_pwatch(c, vars[1]);
        c->set_pwatched(true);
        m_pwatch_trail.push_back(c);
        m_trail.push_back(trail_instr_t::pwatch_i);
    }

    void solver::add_pwatch(constraint* c, pvar v) {
        SASSERT(m_locked_wlist != v);  // the propagate loop will not discover the new size
        LOG_V("Watching v" << v << " in constraint " << show_deref(c));
        m_pwatch[v].push_back(c);
    }

    void solver::erase_pwatch(constraint* c) {
        if (!c->is_pwatched())
            return;
        auto const& vars = c->vars();
        if (vars.size() > 0)
            erase_pwatch(vars[0], c);
        if (vars.size() > 1)
            erase_pwatch(vars[1], c);
        c->set_pwatched(false);
    }

    void solver::erase_pwatch(pvar v, constraint* c) {
        if (v == null_var)
            return;
        SASSERT(m_locked_wlist != v);
        LOG("Unwatching v" << v << " in constraint " << show_deref(c));
        auto& wlist = m_pwatch[v];
        unsigned sz = wlist.size();
        for (unsigned i = 0; i < sz; ++i) {
            if (c == wlist[i]) {
                wlist[i] = wlist.back();
                wlist.pop_back();
                return;
            }
        }
    }

    void solver::push_level() {
        ++m_level;
        m_trail.push_back(trail_instr_t::inc_level_i);
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.push();
#endif
    }

    void solver::pop_levels(unsigned num_levels) {
        if (num_levels == 0)
            return;
        SASSERT(m_level >= num_levels);
        unsigned const target_level = m_level - num_levels;
        using replay_item = std::variant<sat::literal, pvar>;
        vector<replay_item> replay;
        LOG("Pop " << num_levels << " levels (lvl " << m_level << " -> " << target_level << ")");
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.pop(num_levels);
#endif
        while (num_levels > 0) {
            switch (m_trail.back()) {
            case trail_instr_t::qhead_i: {
                pop_qhead();
                break;
            }
            case trail_instr_t::lemma_qhead_i: {
                m_lemmas_qhead--;
                break;
            }
            case trail_instr_t::add_lemma_i: {
                m_lemmas.pop_back();
                break;
            }
            case trail_instr_t::pwatch_i: {
                constraint* c = m_pwatch_trail.back();
                erase_pwatch(c);
                c->set_active(false);   // TODO: review meaning of "active"
                m_pwatch_trail.pop_back();
                break;
            }
            case trail_instr_t::add_var_i: {
                // NOTE: currently we cannot delete variables during solving,
                // since lemmas may introduce new helper variables if they use operations like bitwise and or pseudo-inverse.
                // For easier experimentation with new lemmas, we simply keep all variables for now.
#if 0
                del_var();
#endif
                break;
            }
            case trail_instr_t::inc_level_i: {
                --m_level;
                --num_levels;
                break;
            }
            case trail_instr_t::viable_add_i: {
                m_viable.pop_viable();
                break;
            }
            case trail_instr_t::viable_rem_i: {
                m_viable.push_viable();
                break;
            }
            case trail_instr_t::viable_constraint_i: {
                m_viable_fallback.pop_constraint();
                break;
            }
            case trail_instr_t::assign_i: {
                auto v = m_search.back().var();
                LOG_V("Undo assign_i: v" << v);
                unsigned active_level = get_level(v);

                if (active_level <= target_level) {
                    SASSERT(m_justification[v].is_propagation());
                    replay.push_back(v);
                }
                else {
                    m_free_pvars.unassign_var_eh(v);
                    m_justification[v] = justification::unassigned();
                }
                m_search.pop();
                break;
            }
            case trail_instr_t::assign_bool_i: {
                sat::literal lit = m_search.back().lit();
                signed_constraint c = lit2cnstr(lit);
                LOG_V("Undo assign_bool_i: " << lit);
                unsigned active_level = m_bvars.level(lit);

                if (c->is_active())
                    deactivate_constraint(c);

                if (active_level <= target_level)
                    replay.push_back(lit);
                else
                    m_bvars.unassign(lit);
                m_search.pop();
                break;
            }
            default:
                UNREACHABLE();
            }
            m_trail.pop_back();
        }
        m_constraints.release_level(m_level + 1);
        SASSERT(m_level == target_level);
        for (unsigned j = replay.size(); j-- > 0; ) {
            replay_item item = replay[j];
            std::visit([this](auto&& arg) {
                using T = std::decay_t<decltype(arg)>;
                if constexpr (std::is_same_v<T, sat::literal>) {
                    sat::literal lit = arg;
                    m_search.push_boolean(arg);
                    m_trail.push_back(trail_instr_t::assign_bool_i);
                }
                else if constexpr (std::is_same_v<T, pvar>) {
                    pvar v = arg;
                    m_search.push_assignment(v, m_value[v]);
                    m_trail.push_back(trail_instr_t::assign_i);
                    // TODO: are the viable sets propagated properly?
                    //      when substituting polynomials, it will now take into account the replayed variables, which may itself depend on previous propagations.
                    //      will we get into trouble with cyclic dependencies?
                    //      But we do want to take into account variables that are assigned but not yet propagated.
                }
                else
                    static_assert(always_false<T>::value, "non-exhaustive visitor");
            }, item);
        }
    }

    bool solver::can_decide() const {
        return can_pdecide() || can_bdecide();
    }

    bool solver::can_pdecide() const {
        return !m_free_pvars.empty();
    }

    bool solver::can_bdecide() const {
        return m_lemmas_qhead < m_lemmas.size();
    }

    void solver::decide() {
        LOG_H2("Decide");
        SASSERT(can_decide());
        SASSERT(can_pdecide());  // if !can_pdecide(), all boolean literals have been propagated...
        if (can_bdecide())
            bdecide();
        else
            pdecide(m_free_pvars.next_var());
    }

    void solver::bdecide() {
        clause& lemma = *m_lemmas[m_lemmas_qhead++];
        on_scope_exit update_trail = [this]() {
            // must be done after push_level, but also if we return early.
            m_trail.push_back(trail_instr_t::lemma_qhead_i);
        };

        LOG_H2("Decide on non-asserting lemma: " << lemma);
        sat::literal choice = sat::null_literal;
        for (sat::literal lit : lemma) {
            switch (m_bvars.value(lit)) {
            case l_true:
                // Clause is satisfied; nothing to do here
                return;
            case l_false:
                break;
            case l_undef:
                if (choice == sat::null_literal)
                    choice = lit;
                break;
            }
        }
        LOG("Choice is " << lit_pp(*this, choice));
        // SASSERT(2 <= count_if(lemma, [this](sat::literal lit) { return !m_bvars.is_assigned(lit); });
        SASSERT(choice != sat::null_literal);
        // TODO: is the case after backtracking correct?
        //       => the backtracking code has to handle this. making sure that the decision literal is set to false.
        push_level();
        assign_decision(choice);
    }

    void solver::pdecide(pvar v) {
        LOG("Decide v" << v);
        IF_LOGGING(m_viable.log(v));
        rational val;
        justification j;
        switch (m_viable.find_viable(v, val)) {
        case dd::find_t::empty:
            // NOTE: all such cases should be discovered elsewhere (e.g., during propagation/narrowing)
            //       (fail here in debug mode so we notice if we miss some)
            DEBUG_CODE( UNREACHABLE(); );
            m_free_pvars.unassign_var_eh(v);
            set_conflict(v, false);
            return;
        case dd::find_t::singleton:
            // NOTE: this case may happen legitimately if all other possibilities were excluded by brute force search
            // NOTE 2: probably not true anymore; viable::intersect should trigger all propagations now
            DEBUG_CODE( UNREACHABLE(); );
            j = justification::propagation(m_level);
            break;
        case dd::find_t::multiple:
            j = justification::decision(m_level + 1);
            break;
        }
        assign_verify(v, val, j);
    }

    void solver::assign_propagate(pvar v, rational const& val) {
        LOG("Propagation: " << assignment_pp(*this, v, val));
        SASSERT(!is_assigned(v));
        SASSERT(m_viable.is_viable(v, val));
        m_free_pvars.del_var_eh(v);
        // NOTE:
        // The propagation v := val might depend on a lower level than the current level (m_level).
        // This can happen if the constraints that cause the propagation have been bool-propagated at an earlier level,
        // but appear later in the stack (cf. replay).
        // The level of v should then also be the earlier level instead of m_level.
        unsigned lvl = 0;
        for (signed_constraint c : m_viable.get_constraints(v)) {
            LOG("due to: " << lit_pp(*this, c));
            if (!m_bvars.is_assigned(c.blit()))   // side condition, irrelevant because all vars are already in the main condition
                continue;
            SASSERT(m_bvars.is_assigned(c.blit()));
            lvl = std::max(lvl, m_bvars.level(c.blit()));
            for (pvar w : c->vars())
                if (is_assigned(w))  // TODO: question of which variables are relevant. e.g., v1 > v0 implies v1 > 0 without dependency on v0. maybe add a lemma v1 > v0 --> v1 > 0 on the top level to reduce false variable dependencies? instead of handling such special cases separately everywhere.
                    lvl = std::max(lvl, get_level(w));
        }
        // NOTE: we do not have to check the univariate solver here.
        //       Since we propagate, this means at most the single value 'val' is viable.
        //       If it is not actually viable, the propagation loop will find out and enter the conflict state.
        //       (However, if we do check here, we might find the conflict earlier. Might be worth a try.)
        assign_core(v, val, justification::propagation(lvl));
    }

    /// Verify the value we're trying to assign against the univariate solver
    void solver::assign_verify(pvar v, rational val, justification j) {
        SASSERT(j.is_decision() || j.is_propagation());
        // First, check evaluation of the currently-univariate constraints
        // TODO: we should add a better way to test constraints under assignments, without modifying the solver state.
        m_value[v] = val;
        m_search.push_assignment(v, val);
        m_justification[v] = j;
        bool is_valid = m_viable_fallback.check_constraints(v);
        m_search.pop();
        m_justification[v] = justification::unassigned();
        if (!is_valid) {
            LOG_H2("Chosen assignment " << assignment_pp(*this, v, val) << " is not actually viable!");
            ++m_stats.m_num_viable_fallback;
            // Try to find a valid replacement value
            switch (m_viable_fallback.find_viable(v, val)) {
            case dd::find_t::singleton:
            case dd::find_t::multiple:
                LOG("Fallback solver: " << assignment_pp(*this, v, val));
                SASSERT(!j.is_propagation());  // all excluded values are true negatives, so if j.is_propagation() the univariate solver must return unsat
                j = justification::decision(m_level + 1);
                break;
            case dd::find_t::empty:
                LOG("Fallback solver: unsat");
                m_free_pvars.unassign_var_eh(v);
                set_conflict(v, true);
                return;
            }
        }
        if (j.is_decision())
            push_level();
        assign_core(v, val, j);
    }

    void solver::assign_core(pvar v, rational const& val, justification const& j) {
        if (j.is_decision())
            ++m_stats.m_num_decisions;
        else
            ++m_stats.m_num_propagations;
        LOG(assignment_pp(*this, v, val) << " by " << j);
        SASSERT(m_viable.is_viable(v, val));
        SASSERT(j.is_decision() || j.is_propagation());
        SASSERT(j.level() <= m_level);
        SASSERT(!is_assigned(v));
        SASSERT(all_of(assignment(), [v](auto p) { return p.first != v; }));
        m_value[v] = val;
        m_search.push_assignment(v, val);
        m_trail.push_back(trail_instr_t::assign_i);
        m_justification[v] = j;
        // Decision should satisfy all univariate constraints.
        // Propagation might violate some other constraint; but we will notice that in the propagation loop when v is propagated.
        // TODO: on the other hand, checking constraints here would have us discover some conflicts earlier.
        SASSERT(!j.is_decision() || m_viable_fallback.check_constraints(v));
#if ENABLE_LINEAR_SOLVER
        // TODO: convert justification into a format that can be tracked in a dependency core.
        m_linear_solver.set_value(v, val, UINT_MAX);
#endif
    }

    /**
     * Conflict resolution.
     */
    void solver::resolve_conflict() {
        LOG_H2("Resolve conflict");
        LOG("\n" << *this);
        LOG(search_state_pp(m_search, true));
        ++m_stats.m_num_conflicts;

        SASSERT(is_conflict());

        for (unsigned i = m_search.size(); i-- > 0; ) {
            auto& item = m_search[i];
            m_search.set_resolved(i);
            if (item.is_assignment()) {
                // Resolve over variable assignment
                pvar v = item.var();
                if (!m_conflict.is_relevant_pvar(v)) {
                    // m_search.pop_assignment();
                    continue;
                }
                LOG_H2("Working on " << search_item_pp(m_search, item));
                LOG(m_justification[v]);
                LOG("Conflict: " << m_conflict);
                justification& j = m_justification[v];
                if (j.level() > base_level() && !m_conflict.resolve_value(v) && j.is_decision()) {
                    revert_decision(v);
                    return;
                }
                // m_search.pop_assignment();
            }
            else {
                // Resolve over boolean literal
                SASSERT(item.is_boolean());
                sat::literal const lit = item.lit();
                sat::bool_var const var = lit.var();
                if (!m_conflict.is_relevant(lit))
                    continue;
                LOG_H2("Working on " << search_item_pp(m_search, item));
                LOG(bool_justification_pp(m_bvars, lit));
                LOG("Literal " << lit << " is " << lit2cnstr(lit));
                LOG("Conflict: " << m_conflict);
                if (m_bvars.level(var) <= base_level()) {
                    // NOTE: the levels of boolean literals on the stack aren't always ordered by level (cf. replay functionality in pop_levels).
                    //       Thus we can only skip base level literals here, instead of aborting the loop.
                    continue;
                }
                SASSERT(!m_bvars.is_assumption(var));
                if (m_bvars.is_decision(var)) {
                    revert_bool_decision(lit);
                    return;
                }
                if (m_bvars.is_bool_propagation(var))
                    m_conflict.resolve_bool(lit, *m_bvars.reason(lit));
                else {
                    SASSERT(m_bvars.is_evaluation(var));
                    m_conflict.resolve_with_assignment(lit);
                }
            }
        }
        LOG("End of resolve_conflict loop");
        m_conflict.logger().end_conflict();
        report_unsat();
    }

#if 0
    /**
     * Simple backjumping for lemmas:
     * jump to the level where the lemma can be (bool-)propagated,
     * even without reverting the last decision.
     */
    void solver::backjump_lemma() {
        clause_ref lemma = m_conflict.build_lemma();
        LOG_H2("backjump_lemma: " << show_deref(lemma));
        SASSERT(lemma);

        // find second-highest level of the literals in the lemma
        unsigned max_level = 0;
        unsigned jump_level = 0;
        for (auto lit : *lemma) {
            if (!m_bvars.is_assigned(lit))
                continue;
            unsigned lit_level = m_bvars.level(lit);
            if (lit_level > max_level) {
                jump_level = max_level;
                max_level = lit_level;
            } else if (max_level > lit_level && lit_level > jump_level) {
                jump_level = lit_level;
            }
        }

        jump_level = std::max(jump_level, base_level());
        backjump_and_learn(jump_level, *lemma);
    }
#endif

    /**
     * Revert a decision that caused a conflict.
     * Variable v was assigned by a decision at position i in the search stack.
     *
     * C & v = val is conflict.
     *
     * C => v != val
     *
     * l1 \/ l2 \/ ... \/ lk \/ v != val
     *
     */
    void solver::revert_decision(pvar v) {
        rational val = m_value[v];
        LOG_H2("Reverting decision: pvar " << v << " := " << val);
        SASSERT(m_justification[v].is_decision());

        clause_ref lemma = m_conflict.build_lemma();
        SASSERT(lemma);

        if (lemma->empty()) {
            report_unsat();
            return;
        }

        unsigned jump_level = get_level(v) - 1;
        backjump_and_learn(jump_level, *lemma);
    }

    void solver::revert_bool_decision(sat::literal const lit) {
        LOG_H2("Reverting decision: " << lit_pp(*this, lit));
        sat::bool_var const var = lit.var();

        clause_ref lemma_ref = m_conflict.build_lemma();
        SASSERT(lemma_ref);
        clause& lemma = *lemma_ref;

        SASSERT(!lemma.empty());
        SASSERT(count(lemma, ~lit) > 0);
        SASSERT(all_of(lemma, [this](sat::literal lit1) { return m_bvars.is_false(lit1); }));
        SASSERT(all_of(lemma, [this, var](sat::literal lit1) { return var == lit1.var() || m_bvars.level(lit1) < m_bvars.level(var); }));

        unsigned jump_level = m_bvars.level(var) - 1;
        backjump_and_learn(jump_level, lemma);
        // At this point, the lemma is asserting for ~lit,
        // and has been propagated by learn_lemma/add_clause.
        SASSERT(all_of(lemma, [this](sat::literal lit1) { return m_bvars.is_assigned(lit1); }));
        // so the regular propagation loop will propagate ~lit.
        // Recall that lit comes from a non-asserting lemma.
        // If there is more than one undef choice left in that lemma,
        // then the next bdecide will take care of that (after all outstanding propagations).
        SASSERT(can_bdecide());
    }

    void solver::backjump_and_learn(unsigned jump_level, clause& lemma) {
#ifndef NDEBUG
        polysat::assignment old_assignment = assignment().clone();
        sat::literal_vector lemma_invariant_todo;
        SASSERT(lemma_invariant_part1(lemma, old_assignment, lemma_invariant_todo));
        // SASSERT(lemma_invariant(lemma, old_assignment));
#endif
        clause_ref_vector side_lemmas = m_conflict.take_side_lemmas();
        sat::literal_vector narrow_queue = m_conflict.take_narrow_queue();

        m_conflict.reset();
        backjump(jump_level);

        for (sat::literal lit : narrow_queue) {
            switch (m_bvars.value(lit)) {
            case l_true:
                lit2cnstr(lit).narrow(*this, false);
                break;
            case l_false:
                lit2cnstr(~lit).narrow(*this, false);
                break;
            case l_undef:
                /* do nothing */
                break;
            default:
                UNREACHABLE();
            }
        }
        for (auto cl : side_lemmas) {
            m_simplify_clause.apply(*cl);
            add_clause(*cl);
        }
        SASSERT(lemma_invariant_part2(lemma_invariant_todo));
        learn_lemma(lemma);
    }

    void solver::learn_lemma(clause& lemma) {
        SASSERT(!lemma.empty());
        m_simplify_clause.apply(lemma);
        add_clause(lemma);  // propagates undef literals, if possible
        // At this point, all literals in lemma have been value- or bool-propated, if possible.
        // So if the lemma is/was asserting, all its literals are now assigned.
        bool is_asserting = all_of(lemma, [this](sat::literal lit) { return m_bvars.is_assigned(lit); });
        if (!is_asserting) {
            LOG("Lemma is not asserting!");
            m_lemmas.push_back(&lemma);
            m_trail.push_back(trail_instr_t::add_lemma_i);
            // TODO: currently we forget non-asserting lemmas when backjumping over them.
            //       We surely don't want to keep them in m_lemmas because then we will start doing case splits
            //       even the lemma should instead be waiting for propagations.
            //       We could instead watch its pvars and re-insert into m_lemmas when all but one are assigned.
            //       The same could even be done in general for all lemmas, instead of distinguishing between
            //       asserting and non-asserting lemmas.
            //       (Note that the same lemma can be asserting in one branch of the search but non-asserting in another,
            //       depending on which pvars are assigned.)
            SASSERT(can_bdecide());
        }
    }

    bool solver::lemma_invariant_part1(clause const& lemma, polysat::assignment const& a, sat::literal_vector& out_todo) {
        SASSERT(out_todo.empty());
        LOG("Lemma: " << lemma);
        LOG("assignment: " << a);
        // TODO: fix
#if 0
        for (sat::literal lit : lemma) {
            auto const c = lit2cnstr(lit);
            bool const currently_false = c.is_currently_false(*this, assignment);
            LOG("  " << lit_pp(*this, lit) << "    currently_false? " << currently_false);
            if (!currently_false && m_bvars.value(lit) == l_undef)
                out_todo.push_back(lit);  // undefs might only be set false after the side lemmas are propagated, so check them later.
            else
                SASSERT(m_bvars.value(lit) == l_false || currently_false);
        }
#endif
        return true;
    }

    bool solver::lemma_invariant_part2(sat::literal_vector const& todo) {
        LOG("todo: " << todo);
        // Check that undef literals are now propagated by the side lemmas.
        //
        // Unfortunately, this isn't always possible.
        // Consider if the first side lemma contains a constraint that comes from a boolean decision:
        //
        //      76: v10 + v7 + -1*v0 + -1 == 0      [ l_true decide@5 pwatched active ]
        //
        // When we now backtrack behind the decision level of the literal, then we cannot propagate the side lemma,
        // and some literals of the main lemma may still be undef at this point.
        //
        // So it seems that using constraints from a non-asserting lemma makes the new lemma also non-asserting (if it isn't already).
#if 1
        for (sat::literal lit : todo)
            SASSERT(m_bvars.value(lit) == l_false);
#endif
        return true;
    }

    bool solver::lemma_invariant(clause const& lemma, polysat::assignment const& old_assignment) {
        LOG("Lemma: " << lemma);
        // LOG("old_assignment: " << old_assignment);
        // TODO: fix
#if 0
        for (sat::literal lit : lemma) {
            auto const c = lit2cnstr(lit);
            bool const currently_false = c.is_currently_false(*this, old_assignment);
            LOG("  " << lit_pp(*this, lit) << "    currently_false? " << currently_false);
            SASSERT(m_bvars.value(lit) == l_false || currently_false);
        }
#endif
        return true;
    }

    unsigned solver::level(sat::literal lit0, clause const& cl) {
        unsigned lvl = 0;
        for (auto lit : cl) {
            if (lit == lit0)
                continue;
            SASSERT(m_bvars.is_false(lit));
            lvl = std::max(lvl, m_bvars.level(lit));
        }
        return lvl;
    }

    void solver::assign_decision(sat::literal lit) {
        m_bvars.decision(lit, m_level);
        m_trail.push_back(trail_instr_t::assign_bool_i);
        m_search.push_boolean(lit);
    }

    void solver::assign_propagate(sat::literal lit, clause& reason) {
        m_bvars.propagate(lit, level(lit, reason), reason);
        m_trail.push_back(trail_instr_t::assign_bool_i);
        m_search.push_boolean(lit);
    }

    void solver::assign_eval(sat::literal lit) {
        // SASSERT(lit2cnstr(lit).is_currently_true(*this));  // "morally" this should hold, but currently fails because of pop_assignment during resolve_conflict
        SASSERT(!lit2cnstr(lit).is_currently_false(*this));
        unsigned level = 0;
        // NOTE: constraint may be evaluated even if some variables are still unassigned (e.g., 0*x doesn't depend on x).
        // TODO: level might be too low! because pop_assignment may already have removed necessary variables (cf. comment on assertion above).
        for (auto v : lit2cnstr(lit)->vars())
            if (is_assigned(v))
                level = std::max(get_level(v), level);
        m_bvars.eval(lit, level);
        m_trail.push_back(trail_instr_t::assign_bool_i);
        m_search.push_boolean(lit);
    }

    /** Push c onto \Gamma, unless it is already true. */
    void solver::try_assign_eval(signed_constraint c) {
        sat::literal const lit = c.blit();
        if (m_bvars.is_assigned(lit))
            return;
        if (c.is_always_true())
            return;
        assign_eval(lit);
    }

    /**
    * Activate constraint immediately
    * Activation and de-activation of constraints follows the scope controlled by push/pop.
    * constraints activated within the linear solver are de-activated when the linear
    * solver is popped.
    */
    void solver::activate_constraint(signed_constraint c) {
        SASSERT(c);
        LOG("Activating constraint: " << c);
        SASSERT(m_bvars.value(c.blit()) == l_true);
        SASSERT(!c->is_active());
        c->set_active(true);
        add_pwatch(c.get());
        if (c->vars().size() == 1)
            m_viable_fallback.push_constraint(c->var(0), c);
        c.narrow(*this, true);
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.activate_constraint(c);
#endif
    }

    /// Deactivate constraint
    void solver::deactivate_constraint(signed_constraint c) {
        LOG_V("Deactivating constraint: " << c.blit());
        c->set_active(false);
    }

    void solver::backjump(unsigned new_level) {
        if (m_level != new_level) {
            LOG_H3("Backjumping to level " << new_level << " from level " << m_level);
            pop_levels(m_level - new_level);
        }
    }

    // Add clause to storage
    void solver::add_clause(clause& clause) {
        LOG((clause.is_redundant() ? "Lemma: ": "Aux: ") << clause);
        for (sat::literal lit : clause) {
            LOG("   " << lit_pp(*this, lit));
            // SASSERT(m_bvars.value(lit) != l_true);
            // it could be that such a literal has been created previously but we don't detect it when e.g. narrowing a mul_ovfl_constraint
            if (m_bvars.value(lit) == l_true) {
                // in this case the clause is useless
                LOG("   Clause is already true, skipping...");
                // SASSERT(false);  // should never happen (at least for redundant clauses)
                return;
            }
        }
        SASSERT(!clause.empty());
        m_constraints.store(&clause, true);

        if (!clause.is_redundant()) {
            // for (at least) non-redundant clauses, we also need to watch the constraints
            // so we can discover when the clause should propagate
            // TODO: check if we also need pwatch for redundant clauses
            for (sat::literal lit : clause)
                add_pwatch(m_constraints.lookup(lit.var()));
        }
    }

    void solver::add_clause(unsigned n, signed_constraint* cs, bool is_redundant) {
        clause_builder cb(*this);
        for (unsigned i = 0; i < n; ++i)
            cb.insert(cs[i]);
        clause_ref clause = cb.build();
        if (clause) {
            clause->set_redundant(is_redundant);
            add_clause(*clause);
        }
    }

    void solver::add_clause(signed_constraint c1, signed_constraint c2, bool is_redundant) {
        signed_constraint cs[2] = { c1, c2 };
        add_clause(2, cs, is_redundant);
    }

    void solver::add_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, bool is_redundant) {
        signed_constraint cs[3] = { c1, c2, c3 };
        add_clause(3, cs, is_redundant);
    }

    void solver::add_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, signed_constraint c4, bool is_redundant) {
        signed_constraint cs[4] = { c1, c2, c3, c4 };
        add_clause(4, cs, is_redundant);
    }

    void solver::push() {
        LOG_H3("Push user scope");
        push_level();
        m_base_levels.push_back(m_level);
    }

    void solver::pop(unsigned num_scopes) {
        VERIFY(m_base_levels.size() >= num_scopes);
        unsigned const base_level = m_base_levels[m_base_levels.size() - num_scopes];
        LOG_H3("Pop " << num_scopes << " user scopes");
        pop_levels(m_level - base_level + 1);
        if (m_level < m_conflict.level())
            m_conflict.reset();
        m_base_levels.shrink(m_base_levels.size() - num_scopes);
    }

    bool solver::at_base_level() const {
        return m_level == base_level();
    }

    unsigned solver::base_level() const {
        return m_base_levels.empty() ? 0 : m_base_levels.back();
    }

    bool solver::try_eval(pdd const& p, rational& out_value) const {
        pdd r = subst(p);
        if (r.is_val())
            out_value = r.val();
        return r.is_val();
    }

    /**
     * Variable activity accounting.
     * As a placeholder we increment activity
     * 1. when a variable assignment is used in a conflict.
     * 2. when a variable propagation is resolved against.
     * The hypothesis that this is useful should be tested against a
     * broader suite of benchmarks and tested with micro-benchmarks.
     * It should be tested in conjunction with restarts.
     */
    void solver::inc_activity(pvar v) {
        unsigned& act = m_activity[v];
        act += m_activity_inc;
        m_free_pvars.activity_increased_eh(v);
        if (act > (1 << 24))
            rescale_activity();
    }

    void solver::decay_activity() {
        m_activity_inc *= m_variable_decay;
        m_activity_inc /= 100;
    }

    void solver::rescale_activity() {
        for (unsigned& act : m_activity) {
            act >>= 14;
        }
        m_activity_inc >>= 14;
    }

    void solver::report_unsat() {
        backjump(base_level());
        SASSERT(!m_conflict.empty());
    }

    void solver::unsat_core(dependency_vector& deps) {
        deps.reset();
        LOG("conflict" << m_conflict);
        for (auto c : m_conflict) {
            auto d = m_bvars.dep(c.blit());
            if (d != null_dependency)
                deps.push_back(d);
        }
    }

    std::ostream& solver::display(std::ostream& out) const {
        out << "Search Stack:\n";
        for (auto item : m_search) {
            if (item.is_assignment()) {
                pvar v = item.var();
                auto const& j = m_justification[v];
                out << "\t" << assignment_pp(*this, v, get_value(v)) << " @" << j.level() << " ";
                if (j.is_propagation())
                    for (auto const& c : m_viable.get_constraints(v))
                        out << c << " ";
                out << "\n";
            }
            else {
                sat::bool_var v = item.lit().var();
                out << "\t" << item.lit() << " @" << m_bvars.level(v);
                if (m_bvars.reason(v))
                    out << " " << *m_bvars.reason(v);
                out << "\n";
            }
        }
        out << "Constraints:\n";
        for (auto c : m_constraints)
            out << "\t" << c->bvar2string() << ": " << *c << "\n";
        out << "Clauses:\n";
        for (auto const& cls : m_constraints.clauses()) {
            for (auto const& cl : cls) {
                out << "\t" << *cl << "\n";
                for (auto lit : *cl)
                    out << "\t\t" << lit << ": " << lit2cnstr(lit) << "\n";
            }
        }
        return out;
    }

    std::ostream& assignments_pp::display(std::ostream& out) const {
        return out << s.assignment();
    }

    std::ostream& assignment_pp::display(std::ostream& out) const {
        out << "v" << var << " := " << num_pp(s, var, val);
        if (with_justification)
            out << " (" << s.m_justification[var] << ")";
        return out;
    }

    std::ostream& lit_pp::display(std::ostream& out) const {
        auto c = s.lit2cnstr(lit);
        out << lpad(4, lit) << ": " << rpad(30, c);
        if (!c)
            return out;
        out << "  [ " << s.m_bvars.value(lit);
        if (s.m_bvars.is_assigned(lit)) {
            out << ' ';
            if (s.m_bvars.is_assumption(lit))
                out << "assert";
            else if (s.m_bvars.is_bool_propagation(lit))
                out << "bprop";
            else if (s.m_bvars.is_evaluation(lit))
                out << "eval";
            else if (s.m_bvars.is_decision(lit))
                out << "decide";
            out << '@' << s.m_bvars.level(lit);
        }
        if (c->is_pwatched())
            out << " pwatched";
        if (c->is_active())
            out << " active";
        if (c->is_external())
            out << " ext";
        out << " ]";
        return out;
    }

    std::ostream& num_pp::display(std::ostream& out) const {
        rational const& p = rational::power_of_two(s.size(var));
        if (val > mod(-val, p))
            out << -mod(-val, p);
        else
            out << val;
        return out;
    }

    void solver::collect_statistics(statistics& st) const {
        st.update("polysat iterations",      m_stats.m_num_iterations);
        st.update("polysat decisions",       m_stats.m_num_decisions);
        st.update("polysat conflicts",       m_stats.m_num_conflicts);
        st.update("polysat propagations",    m_stats.m_num_propagations);
        st.update("polysat restarts",        m_stats.m_num_restarts);
        st.update("polysat viable fallback", m_stats.m_num_viable_fallback);
    }

    bool solver::invariant() {
        return true;
    }

    /**
     * levels are gone
     */
    bool solver::invariant(signed_constraints const& cs) {
        return true;
    }

    /**
     * Check that two variables of each constraint are watched.
     */
    bool solver::wlist_invariant() {
#if 0
        for (pvar v = 0; v < m_value.size(); ++v) {
            std::stringstream s;
            for (constraint* c : m_pwatch[v])
                s << " " << c->bvar();
            LOG("Watch for v" << v << ": " << s.str());
        }
#endif
        // Skip boolean variables that aren't active yet
        uint_set skip;
        for (unsigned i = m_qhead; i < m_search.size(); ++i)
            if (m_search[i].is_boolean())
                skip.insert(m_search[i].lit().var());
        for (auto c : m_constraints) {
            if (skip.contains(c->bvar()))
                continue;

            lbool value = m_bvars.value(c->bvar());
            if (value == l_undef)
                continue;
            bool is_positive = value == l_true;
            int64_t num_watches = 0;
            signed_constraint sc(c, is_positive);
            for (auto const& wlist : m_pwatch) {
                auto n = count(wlist, c);
                if (n > 1)
                    std::cout << sc << "\n" << * this << "\n";
                VERIFY(n <= 1);  // no duplicates in the watchlist
                num_watches += n;
            }
            unsigned expected_watches = std::min(2u, c->vars().size());
            if (num_watches != expected_watches)
                LOG("Wrong number of watches: " << sc.blit() << ": " << sc << " (vars: " << sc->vars() << ")");
            VERIFY_EQ(num_watches, expected_watches);
        }
        return true;
    }

    pdd solver::subst(pdd const& p) const {
        return assignment().apply_to(p);
    }

    /** Check that boolean assignment and constraint evaluation are consistent */
    bool solver::assignment_invariant() {
        if (is_conflict())
            return true;
        bool ok = true;
        for (sat::bool_var v = m_bvars.size(); v-- > 0; ) {
            sat::literal lit(v);
            auto c = lit2cnstr(lit);
            if (!all_of(c->vars(), [this](auto w) { return is_assigned(w); }))
                continue;
            ok &= (m_bvars.value(lit) != l_true) || !c.is_currently_false(*this);
            ok &= (m_bvars.value(lit) != l_false) || !c.is_currently_true(*this);
            if (!ok) {
                LOG("assignment invariant is broken " << v << "\n" << *this);
                break;
            }
        }
        return ok;
    }

    /// Check that all constraints on the stack are satisfied by the current model.
    bool solver::verify_sat() {
        LOG_H1("Checking current model...");
        LOG("Assignment: " << assignments_pp(*this));
        bool all_ok = true;
        for (auto s : m_search) {
            if (s.is_boolean()) {
                bool ok = lit2cnstr(s.lit()).is_currently_true(*this);
                LOG((ok ? "PASS" : "FAIL") << ": " << s.lit());
                all_ok = all_ok && ok;
            }
        }
        for (auto clauses : m_constraints.clauses()) {
            for (auto cl : clauses) {
                bool clause_ok = false;
                for (sat::literal lit : *cl) {
                    bool ok = lit2cnstr(lit).is_currently_true(*this);
                    if (ok) {
                        clause_ok = true;
                        break;
                    }
                }
                LOG((clause_ok ? "PASS" : "FAIL") << ": " << show_deref(cl) << (cl->is_redundant() ? " (redundant)" : ""));
                all_ok = all_ok && clause_ok;
            }
        }
        if (all_ok) LOG("All good!");
        return all_ok;
    }

}
