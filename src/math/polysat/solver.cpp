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
#include "math/polysat/variable_elimination.h"
#include <variant>

// For development; to be removed once the linear solver works well enough
#define ENABLE_LINEAR_SOLVER 0

namespace polysat {

    solver::solver(reslimit& lim):
        m_lim(lim),
        m_viable(*this),
        m_viable_fallback(*this),
        m_linear_solver(*this),
        m_fixed_bits(*this),
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
        m_rand.set_seed(m_params.get_uint("random_seed", 0));
    }

    bool solver::should_search() {
        return
            m_lim.inc() &&
            (m_stats.m_num_conflicts < get_config().m_max_conflicts) &&
            (m_stats.m_num_decisions < get_config().m_max_decisions);
    }

    lbool solver::check_sat() {
#ifndef NDEBUG
        SASSERT(!m_is_solving);
        flet<bool> save_(m_is_solving, true);
#endif
        LOG("Starting");
        while (should_search()) {
            m_stats.m_num_iterations++;
            LOG_H1("Next solving loop iteration (#" << m_stats.m_num_iterations << ")");
            LOG("Free variables: " << m_free_pvars);
            LOG("Assignment:     " << assignments_pp(*this));
            if (is_conflict()) LOG("Conflict:       " << m_conflict);
            IF_LOGGING(m_viable.log());
            SASSERT(var_queue_invariant());
            if (is_conflict() && at_base_level()) { LOG_H2("UNSAT"); return l_false; }
            else if (is_conflict()) resolve_conflict();
            else if (can_repropagate_units()) repropagate_units();
            else if (should_add_pwatch()) add_pwatch();
            else if (can_propagate()) propagate();
            else if (can_repropagate()) repropagate();
            else if (!can_decide()) { LOG_H2("SAT"); VERIFY(verify_sat()); return l_true; }
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
        // This method is part of the external interface and should not be used to create internal constraints during solving.
        SASSERT(!m_is_solving);
        backjump(base_level());
        SASSERT(at_base_level());
        SASSERT(c);
        if (is_conflict())
            return;  // no need to do anything if we already have a conflict at base level
        sat::literal lit = c.blit();
        LOG("New constraint " << c << " for " << dep);
        if (m_bvars.is_true(lit)) {
            // constraint c is already asserted => ignore
            SASSERT(m_bvars.level(lit) <= m_level);
            return;
        }
        switch (c.eval()) {
        case l_false:
            // asserted an always-false constraint => conflict at base level
            set_conflict_at_base_level(dep);
            return;
        case l_true:
            // asserted an always-true constraint => ignore
            return;
        case l_undef:
            break;
        default:
            UNREACHABLE();
        }
        if (m_bvars.is_false(lit)) {
            // Input literal contradicts current boolean state (e.g., opposite literals in the input)
            // => conflict only flags the inconsistency
            set_conflict_at_base_level(dep);
            m_conflict.insert(~c);  // ~c is true in the solver, need to track its original dependencies
            return;
        }
        m_bvars.assumption(lit, m_level, dep);
        m_trail.push_back(trail_instr_t::assign_bool_i);
        m_search.push_boolean(lit);
        if (c.is_currently_false(*this))
            set_conflict(c);
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
        SASSERT(!m_is_propagating);
        flet<bool> save_(m_is_propagating, true);
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
        // VERIFY(bool_watch_invariant());
        SASSERT(eval_invariant());
    }

    bool solver::can_repropagate_units() {
        return !m_repropagate_units.empty();
    }

    void solver::repropagate_units() {
        while (!m_repropagate_units.empty() && !is_conflict()) {
            clause& cl = *m_repropagate_units.back();
            m_repropagate_units.pop_back();
            VERIFY_EQ(cl.size(), 1);
            sat::literal lit = cl[0];
            switch (m_bvars.value(lit)) {
            case l_undef:
                assign_propagate(lit, cl);
                break;
            case l_false:
                m_repropagate_units.push_back(&cl);
                set_conflict(cl);
                break;
            case l_true:
                /* ok */
                break;
            default:
                UNREACHABLE();
                break;
            }
        }
    }

    bool solver::can_repropagate() {
        return !m_repropagate_lits.empty();
    }

    // Repropagate:
    // Consider the following case:
    // 1. Literal L is decision@2
    // 2. We are at level 10, add a clause C := A & B ==> L where A@0, B@0 (i.e., L should be propagation@0 now)
    // 3. For whatever reason we now backtrack to 0 or 1.
    //    We have unassigned L but the unit propagation for C does not trigger.
    // 4. To fix that situation we explicitly "repropagate" C after backtracking.
    // NOTE: the same may happen if L is a propagation/evaluation/assumption, and there now exists a new clause that propagates L at an earlier level.
    // TODO: for assumptions this isn't implemented yet. But if we can bool-propagate an assumption from other literals,
    //       it means that the external dependency on the assumed literal is unnecessary and a resulting unsat core may be smaller.
    void solver::repropagate() {
        while (!m_repropagate_lits.empty() && !is_conflict()) {
            sat::literal lit = m_repropagate_lits.back();
            m_repropagate_lits.pop_back();
            repropagate(lit);
        }
        SASSERT(bool_watch_invariant());
    }

    /**
     * Propagate assignment to a Boolean variable
     */
    void solver::propagate(sat::literal lit) {
        LOG_H2("Propagate bool " << lit << "@" << m_bvars.level(lit) << " " << m_level << " qhead: " << m_qhead);
        LOG("Literal " << lit_pp(*this, lit));
        signed_constraint c = lit2cnstr(lit);
        activate_constraint(c);
        auto& wlist = m_bvars.watch(~lit);
        LOG("wlist[" << ~lit << "]: " << wlist);
        unsigned i = 0, j = 0, sz = wlist.size();
        for (; i < sz && !is_conflict(); ++i)
            if (!propagate(lit, *wlist[i]))
                wlist[j++] = wlist[i];
        for (; i < sz; ++i)
            wlist[j++] = wlist[i];
        wlist.shrink(j);
    }

    /**
     * Trigger boolean watchlists for the given literal
     */
    void solver::repropagate(sat::literal lit) {
        LOG_H2("Re-propagate " << lit_pp(*this, lit));
#ifndef NDEBUG
        SASSERT(!m_is_propagating);
        flet<bool> save_(m_is_propagating, true);
#endif
        if (m_bvars.is_true(lit))
            return;
        auto& wlist = m_bvars.watch(lit);
        unsigned i = 0, j = 0, sz = wlist.size();
        if (m_bvars.is_false(lit)) {
            // Here we can fall back to the regular propagation which assumes that ~lit was set to true.
            for (; i < sz && !is_conflict(); ++i)
                if (!propagate(~lit, *wlist[i]))
                    wlist[j++] = wlist[i];
        } else {
            for (; i < sz && !is_conflict(); ++i)
                if (!repropagate(lit, *wlist[i]))
                    wlist[j++] = wlist[i];
        }
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
        unsigned i = 0, j = 0;
        for (; i < m_pwatch[v].size() && !is_conflict(); ++i)
            if (!propagate(v, m_pwatch[v][i])) // propagate may change watch-list reference
                m_pwatch[v][j++] = m_pwatch[v][i];
        auto& wlist = m_pwatch[v];
        for (; i < wlist.size(); ++i) 
            wlist[j++] = wlist[i];
        wlist.shrink(j);
        if (is_conflict())
            shuffle(wlist.size(), wlist.data(), m_rand);
        DEBUG_CODE(m_locked_wlist = std::nullopt;);
    }

    /**
     * Propagate assignment to variable v into constraint c.
     * Return true if a new watch was found; or false to keep the existing one.
     */
    bool solver::propagate(pvar v, constraint* c) {
        lbool const bvalue = m_bvars.value(c->bvar());
        LOG_H3("Propagate " << m_vars[v] << " in " << constraint_pp(c, bvalue));
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
        // at most one pvar remains unassigned
        if (bvalue != l_undef) {
            // constraint state: bool-propagated
            signed_constraint sc(c, bvalue == l_true);
            if (c->vars().size() >= 2) {
                unsigned other_v = c->var(1 - idx);
                if (!is_assigned(other_v))
                    m_viable_fallback.push_constraint(other_v, sc);
            }
            sc.narrow(*this, false);
        } else {
            // constraint state: active but unassigned (bvalue undef, but pwatch is set; e.g., new constraints generated for lemmas)
#if 1
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
#else
            signed_constraint sc(c, true);
            switch (sc.eval(*this)) {
                case l_true:
                    assign_eval(sc.blit());
                    break;
                case l_false:
                    assign_eval(~sc.blit());
                    break;
                default:
                    break;
            }
#endif
        }
        return false;
    }

    /**
     * Propagate boolean assignment of literal lit into clause cl.
     * Return true if a new watch was found; or false to keep the existing one.
     */
    bool solver::propagate(sat::literal lit, clause& cl) {
        // scoped_set_log_enabled _enable(true);
#if 0
        LOG_H3("Propagate " << lit << " into " << cl);
        for (sat::literal l : cl) {
            LOG("    " << lit_pp(*this, l));
        }
#endif
        SASSERT(m_bvars.is_true(lit));
        SASSERT(cl.size() >= 2);
        unsigned idx = (cl[0] == ~lit) ? 1 : 0;
        SASSERT(cl[1 - idx] == ~lit);
        if (m_bvars.is_true(cl[idx]))
            return false;
        // Find a new watched literal:
        // - non-false literal (as usual)
        // - false literal, propagated at higher level than lit
        //   (may happen if a clause has been generated that propagated lit at a lower than current level)
        unsigned i = cl.size();
        uint64_t i_lvl = m_bvars.level(lit);
        for (unsigned j = 2; j < cl.size(); ++j) {
            uint64_t j_lvl = m_bvars.get_watch_level(cl[j]);
            if (i_lvl < j_lvl) {
                i = j;
                i_lvl = j_lvl;
            }
        }
        bool const updated_watch = i < cl.size();
        if (updated_watch) {
            // found better watch literal in cl; watch it instead
            m_bvars.watch(cl[i]).push_back(&cl);
            // LOG("Found new watch: " << cl[i]);
            std::swap(cl[1 - idx], cl[i]);
            if (!m_bvars.is_false(cl[1 - idx]))
                return true;
        }
        // all literals in cl are false, except possibly the other watch cl[idx]
        if (m_bvars.is_false(cl[idx]))
            set_conflict(cl);
        else
            assign_propagate(cl[idx], cl);
        return updated_watch;
    }

    /**
     * Check if clause propagation is triggered by literal lit.
     * Return true if a new watch was found; or false to keep the existing one.
     */
    bool solver::repropagate(sat::literal lit, clause& cl) {
        LOG("Re-propagate " << lit << " in " << cl);
        if (!m_bvars.is_undef(lit))
            return false;
        SASSERT(cl.size() >= 2);
        unsigned idx = (cl[0] == lit) ? 1 : 0;
        SASSERT(cl[1 - idx] == lit);
        if (m_bvars.is_true(cl[idx]))
            return false;
        if (m_bvars.is_undef(cl[idx]))
            return false;
        SASSERT(m_bvars.is_false(cl[idx]));
        // lit is undef, other_lit is false.
        for (unsigned i = 2; i < cl.size(); ++i) {
            // must be assigned, or we should have watched it instead of other_lit.
#if 1
            if (!m_bvars.is_assigned(cl[i])) {
                IF_VERBOSE(15, {
                    verbose_stream() << "repropagate clause " << cl << "\n";
                    verbose_stream() << "repropagate lit = " << lit_pp(*this, lit) << "\n";
                    verbose_stream() << "wrong boolean watches: " << cl << "\n";
                    for (sat::literal lit : cl) {
                        verbose_stream() << "    " << lit_pp(*this, lit);
                        if (count(m_bvars.watch(lit), &cl) != 0)
                            verbose_stream() << " (bool-watched)";
                        verbose_stream() << "\n";
                    }
                });
                // TODO: debug&fix properly; for now just skip.
                //       (unrelated clause may have propagated other_lit, and we didn't get to propagate(other_lit) yet? maybe the repropagate_queue needs to go into the main loop, with priority after standard boolean propagation.)
                return false;
            }
#endif
            VERIFY(m_bvars.is_assigned(cl[i]));
            // there may still be a true literal in the tail; if so, watch it instead.
            if (m_bvars.is_true(cl[i])) {
                m_bvars.watch(cl[i]).push_back(&cl);
                std::swap(cl[1 - idx], cl[i]);
                return true;
            }
        }
        // all literals other than lit are false
        assign_propagate(lit, cl);
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

    /** Enqueue constraint c to perform add_pwatch(c) on the next solver iteration */
    void solver::enqueue_pwatch(constraint* c) {
        SASSERT(c);
        if (c->is_pwatched())
            return;
        m_pwatch_queue.push_back(c);
    }

    bool solver::should_add_pwatch() const {
        return !m_pwatch_queue.empty();
    }

    void solver::add_pwatch() {
        for (constraint* c : m_pwatch_queue) {
            add_pwatch(c);
        }
        m_pwatch_queue.reset();
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
#if 0
        m_pwatch_trail.push_back(c);
        m_trail.push_back(trail_instr_t::pwatch_i);
#endif
    }

    void solver::add_pwatch(constraint* c, pvar v) {
        SASSERT(m_locked_wlist != v);  // the propagate loop will not discover the new size
        LOG_V(20, "Watching v" << v << " in constraint " << show_deref(c));
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
#if 0
        m_fixed_bits.push();
#endif
    }

    void solver::pop_levels(unsigned num_levels) {
        if (num_levels == 0)
            return;
        SASSERT(m_level >= num_levels);
        unsigned const target_level = m_level - num_levels;
        vector<sat::literal> replay;
        LOG("Pop " << num_levels << " levels (lvl " << m_level << " -> " << target_level << ")");
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.pop(num_levels);
#endif
#if 0
        m_fixed_bits.pop();
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
#if 0
            // NOTE: erase_pwatch should be called when the constraint is deleted from the solver.
            case trail_instr_t::pwatch_i: {
                constraint* c = m_pwatch_trail.back();
                erase_pwatch(c);
                m_pwatch_trail.pop_back();
                break;
            }
#endif
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
                LOG_V(20, "Undo assign_i: v" << v);
                m_free_pvars.unassign_var_eh(v);
                m_justification[v] = justification::unassigned();
                m_search.pop();
                break;
            }
            case trail_instr_t::assign_bool_i: {
                sat::literal lit = m_search.back().lit();
                LOG_V(20, "Undo assign_bool_i: " << lit_pp(*this, lit));
                unsigned active_level = m_bvars.level(lit);

                if (active_level <= target_level && m_bvars.is_evaluation(lit)) {
                    // Replaying evaluations is fine since all dependencies (variable assignments) are left untouched.
                    // It is also necessary because repropagate will only restore boolean propagations.
                    replay.push_back(lit);
                }
                else {
                    clause* reason = m_bvars.reason(lit);
                    if (reason && reason->size() == 1) {
                        VERIFY(m_bvars.is_bool_propagation(lit));
                        VERIFY_EQ(lit, (*reason)[0]);
                        // Unit clauses are not stored in watch lists and must be re-propagated separately.
                        m_repropagate_units.push_back(reason);
                    }
                    else
                        m_repropagate_lits.push_back(lit);
                    m_bvars.unassign(lit);
                }
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
        // Replay
        for (unsigned j = replay.size(); j-- > 0; ) {
            sat::literal lit = replay[j];
            m_search.push_boolean(lit);
            m_trail.push_back(trail_instr_t::assign_bool_i);
            LOG("Replay: " << lit);
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
#if 1
        // Simple hack to try deciding the boolean skeleton first
        if (!can_bdecide()) {
            // enqueue all not-yet-true clauses
            for (clause const& cl : m_constraints.clauses()) {
                bool is_true = any_of(cl, [&](sat::literal lit) { return m_bvars.is_true(lit); });
                if (is_true)
                    continue;
                size_t undefs = count_if(cl, [&](sat::literal lit) { return !m_bvars.is_assigned(lit); });
                if (undefs >= 2)
                    m_lemmas.push_back(&cl);
                else {
                    SASSERT_EQ(undefs, 0);  // if !is_true && undefs == 1 then we missed a propagation.
                }
            }
        }
#endif
        
        if (can_bdecide())
            bdecide();
        else
            pdecide(m_free_pvars.next_var());
    }

    void solver::bdecide() {
        clause const& lemma = *m_lemmas[m_lemmas_qhead++];
        on_scope_exit update_trail = [this]() {
            // must be done after push_level, but also if we return early.
            m_trail.push_back(trail_instr_t::lemma_qhead_i);
        };

        LOG_H2("Decide on non-asserting lemma: " << lemma);
        for (sat::literal lit : lemma) {
            LOG(lit_pp(*this, lit));
        }
        sat::literal choice = sat::null_literal;
        for (sat::literal lit : lemma) {
            switch (m_bvars.value(lit)) {
            case l_true:
                // Clause is satisfied; nothing to do here
                // Happens when all other branches of the lemma have been tried.
                // The last branch is entered due to propagation, while the lemma is still on the stack as a decision point.
                LOG("Skip decision (clause already satisfied)");
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
        SASSERT(choice != sat::null_literal);
        SASSERT(2 <= count_if(lemma, [this](sat::literal lit) { return !m_bvars.is_assigned(lit); }));
        SASSERT(can_pdecide());  // if !can_pdecide(), all boolean literals have been evaluated
        push_level();
        assign_decision(choice);
    }

    void solver::pdecide(pvar v) {
        LOG("Decide v" << v);
        IF_LOGGING(m_viable.log(v));
        rational val;
        justification j;
        switch (m_viable.find_viable(v, val)) {
        case find_t::empty:
            UNREACHABLE();  // should have been discovered earlier in viable::intersect
            return;
        case find_t::singleton:
            UNREACHABLE();  // should have been discovered earlier in viable::intersect
            return;
        case find_t::multiple:
            j = justification::decision(m_level + 1);
            break;
        case find_t::resource_out:
            verbose_stream() << "TODO: solver::pdecide got resource_out\n";
            m_lim.cancel();
            return;
        default:
            UNREACHABLE();
            return;
        }
        SASSERT(j.is_decision());
        push_level();
        assign_core(v, val, j);
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

    void solver::assign_core(pvar v, rational const& val, justification const& j) {
        VERIFY(!is_assigned(v));
        if (j.is_decision())
            ++m_stats.m_num_decisions;
        else
            ++m_stats.m_num_propagations;
        LOG(assignment_pp(*this, v, val) << " by " << j);
        SASSERT(m_viable.is_viable(v, val));
        SASSERT(j.is_decision() || j.is_propagation());
        SASSERT(j.level() <= m_level);
        SASSERT(!is_assigned(v));
        SASSERT(all_of(get_assignment(), [v](auto p) { return p.first != v; }));
        m_value[v] = val;
        m_search.push_assignment(v, val);
        m_trail.push_back(trail_instr_t::assign_i);
        m_justification[v] = j;
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
                    continue;
                }
                LOG_H2("Working on " << search_item_pp(m_search, item));
                LOG(m_justification[v]);
                LOG("Conflict: " << m_conflict);
                justification const& j = m_justification[v];
                // NOTE: propagation level may be out of order (cf. replay), but decisions are always in order
                if (j.level() <= base_level()) {
                    if (j.is_decision()) {
                        report_unsat();
                        return;
                    }
                    continue;
                }
                if (j.is_decision()) {
                    m_conflict.revert_pvar(v);
                    revert_decision(v);
                    return;
                }
                m_conflict.resolve_value(v);
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
                LOG("Literal " << lit_pp(*this, lit));
                LOG("Conflict: " << m_conflict);
                // NOTE: the levels of boolean literals on the stack aren't always ordered by level (cf. replay functionality in pop_levels).
                //       Thus we can only skip base level literals here, instead of aborting the loop.
                if (m_bvars.level(var) <= base_level()) {
                    if (m_bvars.is_decision(var)) {
                        report_unsat();  // decisions are always in order
                        return;
                    }
                    continue;
                }
                SASSERT(!m_bvars.is_assumption(var));   // TODO: "assumption" is basically "propagated by unit clause" (or "at base level"); except we do not explicitly store the unit clause.
                if (m_bvars.is_decision(var)) {
                    revert_bool_decision(lit);
                    return;
                }
                if (m_bvars.is_bool_propagation(var))
                    // TODO: this could be a propagation at an earlier level.
                    //       do we really want to resolve these eagerly?
                    m_conflict.resolve_bool(lit, *m_bvars.reason(lit));
                else
                    m_conflict.resolve_evaluated(lit);
            }
        }
        LOG("End of resolve_conflict loop");
        m_conflict.logger().end_conflict();
        report_unsat();
    }

    void solver::revert_decision(pvar v) {
        unsigned max_jump_level = get_level(v) - 1;
        backjump_and_learn(max_jump_level, false);
    }

    void solver::revert_bool_decision(sat::literal const lit) {
        unsigned max_jump_level = m_bvars.level(lit) - 1;
        backjump_and_learn(max_jump_level, true);
        SASSERT(m_level < max_jump_level || m_bvars.is_false(lit));
    }

    std::optional<lemma_score> solver::compute_lemma_score(clause const& lemma) {
        unsigned max_level = 0;             // highest level in lemma
        unsigned lits_at_max_level = 0;     // how many literals at the highest level in lemma
        unsigned snd_level = 0;             // second-highest level in lemma
        bool is_propagation = false;        // whether there is an unassigned literal (at most one)
        for (sat::literal lit : lemma) {
            if (m_bvars.is_true(lit))  // may happen if we only use the clause to justify a new constraint; it is not a real lemma
                return std::nullopt;
            if (!m_bvars.is_assigned(lit)) {
                DEBUG_CODE({
                    if (lit2cnstr(lit).eval(*this) != l_undef)
                        LOG("WARNING: missed evaluation of literal: " << lit_pp(*this, lit));
                });
                SASSERT(!is_propagation);
                is_propagation = true;
                continue;
            }

            unsigned const lit_level = m_bvars.level(lit);
            if (lit_level > max_level) {
                snd_level = max_level;
                max_level = lit_level;
                lits_at_max_level = 1;
            }
            else if (lit_level == max_level)
                lits_at_max_level++;
            else if (max_level > lit_level && lit_level > snd_level)
                snd_level = lit_level;
        }
        SASSERT(lemma.empty() || lits_at_max_level > 0);
        // The MCSAT paper distinguishes between "UIP clauses" and "semantic split clauses".
        // It is the same as our distinction between "asserting" and "non-asserting" lemmas.
        // - UIP clause: a single literal on the highest decision level in the lemma.
        //               Do the standard backjumping known from SAT solving (back to second-highest level in the lemma, propagate it there).
        // - Semantic split clause: multiple literals on the highest level in the lemma.
        //                          Backtrack to "highest level - 1" and split on the lemma there.
        // For now, we follow the same convention for computing the jump levels,
        // but we support an additional type of clause:
        // - Propagation clause: a single literal is unassigned and should be propagated after backjumping.
        //                       backjump to max_level so we can propagate
        unsigned jump_level;
        unsigned branching_factor = lits_at_max_level;
        if (is_propagation)
            jump_level = max_level, branching_factor = 1;
        else if (lits_at_max_level <= 1)
            jump_level = snd_level;
        else
            jump_level = (max_level == 0) ? 0 : (max_level - 1);
        return {{jump_level, branching_factor}};
    }

    void solver::backjump_and_learn(unsigned max_jump_level, bool force_fallback_lemma) {
        sat::literal_vector narrow_queue = m_conflict.take_narrow_queue();
        clause_ref_vector lemmas = m_conflict.take_lemmas();

        // Select the "best" lemma
        // - lowest jump level
        // - lowest number of literals at the highest level
        // We must do so before backjump() when the search stack is still intact.
        lemma_score best_score = lemma_score::max();
        clause* best_lemma = nullptr;

        auto appraise_lemma = [&](clause* lemma) {
            auto score = compute_lemma_score(*lemma);
            if (score)
                LOG("    score: "  << *score);
            else
                LOG("    score: <none>");
            if (score && *score < best_score) {
                best_score = *score;
                best_lemma = lemma;
            }
        };

        for (clause* lemma : lemmas)
            appraise_lemma(lemma);
        if (force_fallback_lemma || !best_lemma || best_score.jump_level() > max_jump_level) {
            // No (good) lemma has been found, so build the fallback lemma from the conflict state.
            lemmas.push_back(m_conflict.build_lemma());
            appraise_lemma(lemmas.back());
        }
        if (!best_lemma) {
            verbose_stream() << "conflict: " << m_conflict << "\n";
            verbose_stream() << "no lemma\n";
            for (clause* cl: lemmas) {
                verbose_stream() << *cl << "\n";
                for (sat::literal lit : *cl)
                    verbose_stream() << "    " << lit_pp(*this, lit) << "\n";
            }
        }
        SASSERT(best_score < lemma_score::max());
        VERIFY(best_lemma);

        unsigned const jump_level = std::max(best_score.jump_level(), base_level());
        SASSERT(jump_level <= max_jump_level);

        LOG("best_score: " << best_score);
        LOG("best_lemma: " << *best_lemma);
            
        m_conflict.reset();
        backjump(jump_level);

        for (sat::literal lit : narrow_queue) {
            LOG("Narrow queue: " << lit_pp(*this, lit));
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
            if (is_conflict()) {
                // The remainder of narrow_queue is forgotten at this point,
                // but keep the lemmas for later.
                for (clause* lemma : lemmas)
                    m_conflict.restore_lemma(lemma);
                return;
            }
        }

        for (auto it = lemmas.begin(); it != lemmas.end(); ++it) {
            clause& lemma = **it;
            if (!lemma.is_active())
                add_clause(lemma);
            else
                propagate_clause(lemma);
            // NOTE: currently, the backjump level is an overapproximation,
            //       since the level of evaluated constraints may not be exact (see TODO in assign_eval).
            // For this reason, we may actually get a conflict at this point
            // (because the actual jump_level of the lemma may be lower that best_level.)
            if (is_conflict()) {
                // Keep the remaining lemmas for later.
                for (; it != lemmas.end(); ++it)
                    m_conflict.restore_lemma(*it);
                return;
            }
        }

        if (best_score.branching_factor() > 1) {
            // NOTE: at this point it is possible that the best_lemma is non-asserting.
            //       We need to double-check, because the backjump level may not be exact (see comment on checking is_conflict above).
            bool const is_asserting = all_of(*best_lemma, [this](sat::literal lit) { return m_bvars.is_assigned(lit); });
            if (!is_asserting) {
                LOG_H3("Main lemma is not asserting: " << *best_lemma);
                for (sat::literal lit : *best_lemma) {
                    LOG(lit_pp(*this, lit));
                }
                m_lemmas.push_back(best_lemma);
                m_trail.push_back(trail_instr_t::add_lemma_i);
                // TODO: currently we forget non-asserting lemmas when backjumping over them.
                //       We surely don't want to keep them in m_lemmas because then we will start doing case splits
                //       even if the lemma should instead be waiting for propagations.
                //       We could instead watch its pvars and re-insert into m_lemmas when all but one are assigned.
                //       The same could even be done in general for all lemmas, instead of distinguishing between
                //       asserting and non-asserting lemmas.
                //       (Note that the same lemma can be asserting in one branch of the search but non-asserting in another,
                //       depending on which pvars are assigned.)
                SASSERT(can_bdecide());
            }
        }
    }  // backjump_and_learn

    // Explicit boolean propagation over the given clause, without relying on watch lists.
    void solver::propagate_clause(clause& cl) {
        sat::literal prop = sat::null_literal;
        for (sat::literal lit : cl) {
            if (m_bvars.is_true(lit))
                return;  // clause is true
            if (m_bvars.is_false(lit))
                continue;
            SASSERT(!m_bvars.is_assigned(lit));
            if (prop != sat::null_literal)
                return;  // two or more undef literals
            prop = lit;
        }
        if (prop == sat::null_literal)
            return;
        assign_propagate(prop, cl);
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
        SASSERT(lit != sat::null_literal);
        m_bvars.decision(lit, m_level);
        m_trail.push_back(trail_instr_t::assign_bool_i);
        m_search.push_boolean(lit);
    }

    void solver::assign_propagate(sat::literal lit, clause& reason) {
        SASSERT(lit != sat::null_literal);
        m_bvars.propagate(lit, level(lit, reason), reason);
        m_trail.push_back(trail_instr_t::assign_bool_i);
        m_search.push_boolean(lit);
    }

    void solver::assign_eval(sat::literal lit) {
        signed_constraint const c = lit2cnstr(lit);
        LOG_V(10, "Evaluate: " << lit_pp(*this, lit));
        if (!c.is_currently_true(*this)) {
            IF_VERBOSE(0, verbose_stream() << "\n" << c << " is not currently true\n");
        }
        SASSERT(c.is_currently_true(*this));
        VERIFY_EQ(c.eval(*this), l_true);
        unsigned level = 0;
        // NOTE: constraint may be evaluated even if some variables are still unassigned (e.g., 0*x doesn't depend on x).
        for (auto v : c->vars())
            if (is_assigned(v))
                level = std::max(get_level(v), level);
        // TODO: the level computed here is not exact, because evaluation of constraints may not depend on all variables that occur in the constraint.
        //       For example, consider x := 0 @ 1 and y := 0 @ 3. Then x*y == 0 eval@3, even though we can already evaluate it at level 1.
        //       To get the exact level:
        //       - consider the levels get_level(var) for var in c->vars().
        //       - the maximum of these is the estimate we start with (and which we currently use)
        //       - successively reduce the level, as long as the constraint still evaluates
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

    sat::literal solver::try_eval(sat::literal lit) {
        signed_constraint const c = lit2cnstr(lit);
        switch (c.eval(*this)) {
        case l_true:
            assign_eval(lit);
            break;
        case l_false:
            assign_eval(~lit);
            break;
        default:
            break;
        }
        return lit;
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
        SASSERT_EQ(m_bvars.value(c.blit()), l_true);
        add_pwatch(c.get());
        pvar v = null_var;
        if (c->vars().size() == 1)
            // If there is exactly one variable in c, then c is always univariate.
            v = c->vars()[0];
        else {
            // Otherwise, check if exactly one variable in c remains unassigned.
            for (pvar w : c->vars()) {
                if (is_assigned(w))
                    continue;
                if (v != null_var) {
                    // two or more unassigned vars; abort
                    v = null_var;
                    break;
                }
                v = w;
            }
        }
        if (v != null_var)
            m_viable_fallback.push_constraint(v, c);
        // TODO: we use narrow with first=true to add axioms about the constraint to the solver.
        //       However, constraints can be activated multiple times (e.g., if it comes from a lemma and is propagated at a non-base level).
        //       So the same axioms may be added multiple times.
        //       Maybe separate narrow/activate? And keep a flag in m_bvars to remember whether constraint has already been activated.
        c.narrow(*this, true);
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.activate_constraint(c);
#endif
    }

    void solver::backjump(unsigned new_level) {
        SASSERT(new_level >= base_level());
        if (m_level != new_level) {
            LOG_H3("Backjumping to level " << new_level << " from level " << m_level << " (base_level: " << base_level() << ")");
            pop_levels(m_level - new_level);
        }
    }

    void solver::add_clause(clause_ref clause) {
        VERIFY(clause);
        add_clause(*clause);
    }

    // Add clause to solver
    void solver::add_clause(clause& clause) {
        LOG((clause.is_redundant() ? "Lemma: ": "Aux: ") << clause);
        for (sat::literal lit : clause) {
            // Try to evaluate literals without boolean value.
            // (Normally this should have been done already by using clause_builder::insert_eval/insert_try_eval when constructing the clause.)
            if (!m_bvars.is_assigned(lit)) {
                lbool const status = lit2cnstr(lit).eval(*this);
                if (status == l_true)
                    assign_eval(lit);
                else if (status == l_false)
                    assign_eval(~lit);
            }
            LOG("    " << lit_pp(*this, lit));
        }
        SASSERT(!clause.empty());
        m_constraints.store(&clause);

        // Defer add_pwatch until the next solver iteration, because during propagation of a variable v the watchlist for v is locked.
        // NOTE: for non-redundant clauses, pwatching its constraints is required for soundness.
        for (sat::literal lit : clause)
            enqueue_pwatch(lit2cnstr(lit).get());
    }

    void solver::add_clause(unsigned n, signed_constraint const* cs, bool is_redundant) {
        clause_ref clause = mk_clause(n, cs, is_redundant);
        if (clause)
            add_clause(*clause);
    }

    void solver::add_clause(std::initializer_list<signed_constraint> cs, bool is_redundant) {
        add_clause(static_cast<unsigned>(cs.size()), std::data(cs), is_redundant);
    }

    void solver::add_clause(signed_constraint c1, bool is_redundant) {
        add_clause({ c1 }, is_redundant);
    }

    void solver::add_clause(signed_constraint c1, signed_constraint c2, bool is_redundant) {
        add_clause({ c1, c2 }, is_redundant);
    }

    void solver::add_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, bool is_redundant) {
        add_clause({ c1, c2, c3 }, is_redundant);
    }

    void solver::add_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, signed_constraint c4, bool is_redundant) {
        add_clause({ c1, c2, c3, c4 }, is_redundant);
    }

    clause_ref solver::mk_clause(std::initializer_list<signed_constraint> cs, bool is_redundant) {
        return mk_clause(static_cast<unsigned>(cs.size()), std::data(cs), is_redundant);
    }

    clause_ref solver::mk_clause(unsigned n, signed_constraint const* cs, bool is_redundant) {
        clause_builder cb(*this);
        for (unsigned i = 0; i < n; ++i)
            cb.insert(cs[i]);
        cb.set_redundant(is_redundant);
        return cb.build();
    }

    clause_ref solver::mk_clause(signed_constraint c1, bool is_redundant) {
        return mk_clause({ c1 }, is_redundant);
    }

    clause_ref solver::mk_clause(signed_constraint c1, signed_constraint c2, bool is_redundant) {
        return mk_clause({ c1, c2 }, is_redundant);
    }

    clause_ref solver::mk_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, bool is_redundant) {
        return mk_clause({ c1, c2, c3 }, is_redundant);
    }

    clause_ref solver::mk_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, signed_constraint c4, bool is_redundant) {
        return mk_clause({ c1, c2, c3, c4 }, is_redundant);
    }

    clause_ref solver::mk_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, signed_constraint c4, signed_constraint c5, bool is_redundant) {
        return mk_clause({ c1, c2, c3, c4, c5 }, is_redundant);
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
        VERIFY(!m_conflict.empty());
    }

    void solver::unsat_core(dependency_vector& deps) {
        VERIFY(is_conflict());
        VERIFY(at_base_level());
        deps.reset();
        m_conflict.find_deps(deps);
        IF_VERBOSE(10,
            verbose_stream() << "polysat unsat_core " << deps << "\n";
            // Print constraints involved in the unsat core for debugging.
            // NOTE: the output may look confusing since relevant op_constraints are not printed (does not affect correctness of the core).
            for (auto d : deps) {
                for (sat::bool_var b = 0; b < m_bvars.size(); ++b) {
                    if (m_bvars.dep(b) != d)
                        continue;
                    sat::literal lit(b, m_bvars.value(b) == l_false);
                    SASSERT(m_bvars.is_true(lit));
                    verbose_stream() << "    " << d << ": " << lit_pp(*this, lit) << "\n";
                }
            }
        );
    }

    std::ostream& solver::display_search(std::ostream& out) const {
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
                out << "\t" << lit_pp(*this, item.lit());
                if (m_bvars.reason(v))
                    out << "    reason " << *m_bvars.reason(v);
                out << "\n";
            }
        }
        return out;
    }

    std::ostream& solver::display(std::ostream& out) const {
        out << "Search Stack:\n";
        display_search(out);
        out << "Constraints:\n";
        for (auto c : m_constraints)
            out << "\t" << c->bvar2string() << ": " << *c << "\n";
        out << "Clauses:\n";
        for (clause const& cl : m_constraints.clauses()) {
            out << "\t" << cl << "\n";
            for (sat::literal lit : cl)
                out << "\t\t" << lit_pp(*this, lit) << "\n";
        }
        return out;
    }

    std::ostream& assignments_pp::display(std::ostream& out) const {
        return out << s.get_assignment();
    }

    std::ostream& assignment_pp::display(std::ostream& out) const {
        out << "v" << var << " := " << num_pp(s, var, val);
        if (with_justification)
            out << " (" << s.m_justification[var] << ")";
        return out;
    }

    std::ostream& lit_pp::display(std::ostream& out) const {
        signed_constraint const c = s.lit2cnstr(lit);
        out << lpad(5, lit) << ": " << rpad(30, c);
        if (!c)
            return out;
        out << "  [ b:" << rpad(7, s.m_bvars.value(lit));
        out << " p:" << rpad(7, c.eval(s));
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
        if (c->is_external())
            out << " ext";
        dependency const d = s.m_bvars.dep(lit);
        if (!d.is_null())
            out << " dep:" << d.val();
        out << " ]";
        return out;
    }

    std::ostream& num_pp::display(std::ostream& out) const {
        return out << dd::val_pp(s.var2pdd(var), val, require_parens);
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
    bool solver::wlist_invariant() const {
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
        SASSERT(is_conflict() || skip.empty());  // after propagation we either finished the queue or we are in a conflict
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

    bool solver::bool_watch_invariant() const {
        if (is_conflict())  // propagation may be unfinished if a conflict was discovered
            return true;
        // Check that exactly the first two literals are watched.
        for (clause const& cl : m_constraints.clauses()) {
            if (cl.size() <= 1)  // unit clauses aren't watched
                continue;
            size_t const count0 = count(m_bvars.watch(cl[0]), &cl);
            size_t const count1 = count(m_bvars.watch(cl[1]), &cl);
            size_t count_tail = 0;
            for (unsigned i = 2; i < cl.size(); ++i)
                count_tail += count(m_bvars.watch(cl[i]), &cl);
            if (count0 != 1 || count1 != 1 || count_tail != 0) {
                verbose_stream() << "wrong boolean watches: " << cl << "\n";
                for (sat::literal lit : cl) {
                    verbose_stream() << "    " << lit_pp(*this, lit);
                    if (count(m_bvars.watch(lit), &cl) != 0)
                        verbose_stream() << " (bool-watched)";
                    verbose_stream() << "\n";
                }
            }
            VERIFY_EQ(count0, 1);
            VERIFY_EQ(count1, 1);
            VERIFY_EQ(count_tail, 0);
        }
        // Check for missed boolean propagations:
        // - no clause should have exactly one unassigned literal, unless it is already true.
        // - no clause should be false
        for (clause const& cl : m_constraints.clauses()) {
            bool const is_true = any_of(cl, [&](auto lit) { return m_bvars.is_true(lit); });
            if (is_true)
                continue;
            size_t const undefs = count_if(cl, [&](auto lit) { return !m_bvars.is_assigned(lit); });
            if (undefs == 1) {
                verbose_stream() << "Missed boolean propagation of clause: " << cl << "\n";
                for (sat::literal lit : cl) {
                    verbose_stream() << "    " << lit_pp(*this, lit);
                    if (count(m_bvars.watch(lit), &cl) != 0)
                        verbose_stream() << " (bool-watched)";
                    verbose_stream() << "\n";
                }
            }
            VERIFY(undefs != 1);
            bool const is_false = all_of(cl, [&](auto lit) { return m_bvars.is_false(lit); });
            VERIFY(!is_false);
        }
        // Check watch literal invariant for long clauses:
        // - true literals may always be watched
        // - if at least one true literal is watched, the clause is fine
        // - otherwise, a literal may only be watched if there is no unwatched literal at higher level.
        auto const get_watch_level = [&](sat::literal lit) -> unsigned {
            return m_bvars.is_false(lit) ? m_bvars.level(lit) : UINT_MAX;
        };
        for (clause const& cl : m_constraints.clauses()) {
            if (cl.size() <= 2)
                continue;
            if (m_bvars.is_true(cl[0]))
                continue;
            if (m_bvars.is_true(cl[1]))
                continue;
            // the watched literals are cl[0] and cl[1]
            unsigned const lvl_cl0 = get_watch_level(cl[0]);
            unsigned const lvl_cl1 = get_watch_level(cl[1]);
            unsigned lvl_tail = 0;
            for (unsigned i = 2; i < cl.size(); ++i)
                lvl_tail = std::max(lvl_tail, get_watch_level(cl[i]));
            if (lvl_cl0 < lvl_tail || lvl_cl1 < lvl_tail) {
                verbose_stream() << "Broken constraint on levels of watched literals of clause: " << cl << "\n";
                for (sat::literal lit : cl) {
                    verbose_stream() << "    " << lit_pp(*this, lit);
                    if (count(m_bvars.watch(lit), &cl) != 0)
                        verbose_stream() << " (bool-watched)";
                    verbose_stream() << "\n";
                }
            }
            VERIFY(lvl_cl0 >= lvl_tail);
            VERIFY(lvl_cl1 >= lvl_tail);
        }
        return true;
    }

    pdd solver::subst(pdd const& p) const {
        return get_assignment().apply_to(p);
    }

    /** Check that boolean assignment and constraint evaluation are consistent */
    bool solver::eval_invariant() const {
        if (is_conflict())
            return true;
        for (sat::bool_var v = m_bvars.size(); v-- > 0; ) {
            sat::literal const lit(v);
            signed_constraint const c = lit2cnstr(lit);
            if (!all_of(c->vars(), [this](pvar w) { return is_assigned(w); }))
                continue;
            lbool const bvalue = m_bvars.value(lit);
            lbool const pvalue = c.eval(*this);
            if (bvalue != l_undef && pvalue != l_undef && bvalue != pvalue) {
                verbose_stream() << "missed bool/eval conflict: " << lit_pp(*this, lit) << "\n";
                return false;
            }
            if (bvalue == l_undef && pvalue != l_undef) {
                verbose_stream() << "missed evaluation: " << lit_pp(*this, lit) << "\n";
                return false;
            }
        }
        return true;
    }

    /** Check that each variable is either assigned or queued for decisions */
    bool solver::var_queue_invariant() const {
        if (is_conflict())
            return true;
        uint_set active;
        bool ok = true;
        for (pvar v : m_free_pvars)
            active.insert(v);
        for (auto const& [v, val] : get_assignment()) {
            if (active.contains(v)) {
                ok = false;
                LOG("Variable v" << v << " is in free var queue despite already assigned " << assignment_pp(*this, v, val));
            }
            active.insert(v);
        }
        for (pvar v = 0; v < num_vars(); ++v) {
            if (!active.contains(v)) {
                ok = false;
                LOG("Lost variable v" << v << " (it is neither assigned nor free)");
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
        for (clause const& cl : m_constraints.clauses()) {
            bool clause_ok = false;
            for (sat::literal lit : cl) {
                bool ok = lit2cnstr(lit).is_currently_true(*this);
                if (ok) {
                    clause_ok = true;
                    break;
                }
            }
            LOG((clause_ok ? "PASS" : "FAIL") << ": " << cl << (cl.is_redundant() ? " (redundant)" : ""));
            all_ok = all_ok && clause_ok;
        }
        if (all_ok) LOG("All good!");
        return all_ok;
    }

}
