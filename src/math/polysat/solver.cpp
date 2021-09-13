/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat

Abstract:

    Polynomial solver for modular arithmetic.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/solver.h"
#include "math/polysat/explain.h"
#include "math/polysat/log.h"
#include "math/polysat/forbidden_intervals.h"
#include "math/polysat/variable_elimination.h"

// For development; to be removed once the linear solver works well enough
#define ENABLE_LINEAR_SOLVER 0

namespace polysat {

    dd::pdd_manager& solver::sz2pdd(unsigned sz) {
        m_pdd.reserve(sz + 1);
        if (!m_pdd[sz]) 
            m_pdd.set(sz, alloc(dd::pdd_manager, 1000, dd::pdd_manager::semantics::mod2N_e, sz));
        return *m_pdd[sz];
    }

    solver::solver(reslimit& lim): 
        m_lim(lim),
        m_viable(*this),
        m_dm(m_value_manager, m_alloc),
        m_linear_solver(*this),
        m_conflict(*this),
        m_free_vars(m_activity),
        m_bvars(),
        m_constraints(m_bvars) {
    }

    solver::~solver() {
        // Need to remove any lingering clause/constraint references before the constraint manager is destructed
        m_conflict.reset();
    }

    bool solver::should_search() {
        return 
            m_lim.inc() && 
            (m_stats.m_num_conflicts < m_max_conflicts) &&
            (m_stats.m_num_decisions < m_max_decisions);
    }
   
    lbool solver::check_sat() { 
        LOG("Starting");
        m_disjunctive_lemma.reset();
        while (inc()) {
            m_stats.m_num_iterations++;
            LOG_H1("Next solving loop iteration (#" << m_stats.m_num_iterations << ")");
            LOG("Free variables: " << m_free_vars);
            LOG("Assignment:     " << assignments_pp(*this));
            if (!m_conflict.empty()) LOG("Conflict:       " << m_conflict);
            IF_LOGGING(m_viable.log());
            if (!is_conflict() && m_constraints.should_gc()) m_constraints.gc(*this);

            if (pending_disjunctive_lemma()) { LOG_H2("UNDEF (handle lemma externally)"); return l_undef; }
            else if (is_conflict() && at_base_level()) { LOG_H2("UNSAT"); return l_false; }
            else if (is_conflict()) resolve_conflict();
            else if (can_propagate()) propagate();
            else if (!can_decide()) { LOG_H2("SAT"); SASSERT(verify_sat()); return l_true; }
            else decide();
        }
        LOG_H2("UNDEF (resource limit)");
        return l_undef;
    }
        
    unsigned solver::add_var(unsigned sz) {
        pvar v = m_value.size();
        m_value.push_back(rational::zero());
        m_justification.push_back(justification::unassigned());
        m_viable.push(sz);
        m_cjust.push_back({});
        m_watch.push_back({});
        m_activity.push_back(0);
        m_vars.push_back(sz2pdd(sz).mk_var(v));
        m_size.push_back(sz);
        m_trail.push_back(trail_instr_t::add_var_i);
        m_free_vars.mk_var_eh(v);
        return v;
    }

    pdd solver::value(rational const& v, unsigned sz) {
        return sz2pdd(sz).mk_val(v);
    }

    void solver::del_var() {
        // TODO also remove v from all learned constraints.
        pvar v = m_value.size() - 1;
        m_viable.pop();
        m_cjust.pop_back();
        m_value.pop_back();
        m_justification.pop_back();
        m_watch.pop_back();
        m_activity.pop_back();
        m_vars.pop_back();
        m_size.pop_back();
        m_free_vars.del_var_eh(v);
    }

    signed_constraint solver::eq(pdd const& p) {
        return m_constraints.eq(p);
    }

    signed_constraint solver::diseq(pdd const& p) {
        return ~m_constraints.eq(p);
    }

    signed_constraint solver::ule(pdd const& p, pdd const& q) {
        return m_constraints.ule(p, q);
    }

    signed_constraint solver::ult(pdd const& p, pdd const& q) {
        return m_constraints.ult(p, q);
    }

    signed_constraint solver::sle(pdd const& p, pdd const& q) {
        return m_constraints.sle(p, q);
    }

    signed_constraint solver::slt(pdd const& p, pdd const& q) {
        return m_constraints.slt(p, q);
    }

    void solver::ext_constraint(signed_constraint c, unsigned dep, bool activate) {
        VERIFY(at_base_level());
        SASSERT(c);
        SASSERT(activate || dep != null_dependency);  // if we don't activate the constraint, we need the dependency to access it again later.
        m_constraints.ensure_bvar(c.get());
        clause* unit = m_constraints.store(clause::from_unit(m_level, c, mk_dep_ref(dep)));
        c->set_unit_clause(unit);
        if (dep != null_dependency)
            if (!c->is_external()) {
                m_constraints.register_external(c.get());
                m_trail.push_back(trail_instr_t::ext_constraint_i);
                m_ext_constraint_trail.push_back(c.get());
            }
        LOG("New constraint: " << c);

#if ENABLE_LINEAR_SOLVER
        m_linear_solver.new_constraint(*c.get());
#endif
        // TODO: there is an issue when the input contains both c and ~c. (see test_ineq_basic2)
        if (activate && !is_conflict())
            propagate_bool(c.blit(), unit);
    }

    void solver::assign_eh(unsigned dep, bool is_true) {
        VERIFY(at_base_level());
        NOT_IMPLEMENTED_YET();
        /*
        constraint* c = m_constraints.lookup_external(dep);
        if (!c) {
            LOG("WARN: there is no constraint for dependency " << dep);
            return;
        }
        if (is_conflict())
            return;
        // TODO: this is wrong. (e.g., if the external constraint was negative) we need to store signed_constraints
        signed_constraint cl{c, is_true};
        activate_constraint_base(cl);
        */
    }


    bool solver::can_propagate() {
        return m_qhead < m_search.size() && !is_conflict();
    }

    void solver::propagate() {
        push_qhead();
        while (can_propagate()) {
            auto const& item = m_search[m_qhead++];
            if (item.is_assignment())
                propagate(item.var());
            else
                propagate(item.lit());
        }
        linear_propagate();
        SASSERT(wlist_invariant());
        if (!is_conflict())
            SASSERT(assignment_invariant());
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

    void solver::propagate(sat::literal lit) {
        LOG_H2("Propagate bool " << lit);
        signed_constraint c = m_constraints.lookup(lit);
        SASSERT(c);
        activate_constraint(c);
    }

    void solver::propagate(pvar v) {
        LOG_H2("Propagate v" << v);
        auto& wlist = m_watch[v];
        unsigned i = 0, j = 0, sz = wlist.size();
        for (; i < sz && !is_conflict(); ++i) 
            if (!wlist[i].propagate(*this, v))
                wlist[j++] = wlist[i];
        for (; i < sz; ++i)
            wlist[j++] = wlist[i];
        wlist.shrink(j);
    }

    void solver::propagate(pvar v, rational const& val, signed_constraint c) {
        LOG("Propagation: " << assignment_pp(*this, v, val) << ", due to " << c);
        if (m_viable.is_viable(v, val)) {
            m_free_vars.del_var_eh(v);
            assign_core(v, val, justification::propagation(m_level));        
        }
        else 
            set_conflict(c);
    }

    void solver::push_level() {
        ++m_level;
        m_trail.push_back(trail_instr_t::inc_level_i);
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.push();
#endif
    }

    void solver::pop_levels(unsigned num_levels) {
        SASSERT(m_level >= num_levels);
        unsigned const target_level = m_level - num_levels;
        vector<sat::literal> replay;
        LOG("Pop " << num_levels << " levels (lvl " << m_level << " -> " << target_level << ")");
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.pop(num_levels);
#endif
        while (num_levels > 0) {
            switch (m_trail.back()) {
            case trail_instr_t::qhead_i: {
                pop_qhead();
                for (unsigned i = m_search.size(); i-- > m_qhead; )
                    if (m_search[i].is_boolean()) {
                        auto c = m_constraints.lookup(m_search[i].lit());
                        deactivate_constraint(c);
                    }
                break;
            }
            case trail_instr_t::add_var_i: {
                del_var();
                break;
            }
            case trail_instr_t::inc_level_i: {
                --m_level;
                --num_levels;
                break;
            }
            case trail_instr_t::viable_i: {
                m_viable.pop_viable();
                break;
            }
            case trail_instr_t::assign_i: {
                auto v = m_search.back().var();
                LOG_V("Undo assign_i: v" << v);
                m_free_vars.unassign_var_eh(v);
                m_justification[v] = justification::unassigned();
                m_search.pop();
                break;
            }
            case trail_instr_t::assign_bool_i: {
                sat::literal lit = m_search.back().lit();
                LOG_V("Undo assign_bool_i: " << lit);
                unsigned active_level = m_bvars.level(lit);
                if (active_level <= target_level)
                    replay.push_back(lit);
                else
                    m_bvars.unassign(lit);
                m_search.pop();
                break;
            }
            case trail_instr_t::just_i: {
                auto v = m_cjust_trail.back();
                LOG_V("Undo just_i");
                m_cjust[v].pop_back();
                m_cjust_trail.pop_back();
                break;
            }
            case trail_instr_t::ext_constraint_i: {
                constraint* c = m_ext_constraint_trail.back();
                m_constraints.unregister_external(c);
                m_ext_constraint_trail.pop_back();
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
            auto lit = replay[j];
            m_trail.push_back(trail_instr_t::assign_bool_i);
            m_search.push_boolean(lit);
        }
    }


    void solver::add_watch(signed_constraint c) {
        SASSERT(c);
        auto const& vars = c->vars();
        if (vars.size() > 0)
            add_watch(c, vars[0]);
        if (vars.size() > 1)
            add_watch(c, vars[1]);
    }

    void solver::add_watch(signed_constraint c, pvar v) {
        SASSERT(c);
        LOG("Watching v" << v << " in constraint " << c);
        m_watch[v].push_back(c);
    }

    void solver::erase_watch(signed_constraint c) {
        auto const& vars = c->vars();
        if (vars.size() > 0)
            erase_watch(vars[0], c);
        if (vars.size() > 1)
            erase_watch(vars[1], c);
    }

    void solver::erase_watch(pvar v, signed_constraint c) {
        if (v == null_var)
            return;
        auto& wlist = m_watch[v];
        unsigned sz = wlist.size();
        for (unsigned i = 0; i < sz; ++i) {
            if (c == wlist[i]) {
                wlist[i] = wlist.back();
                wlist.pop_back();
                return;
            }
        }
    }

    void solver::decide() {
        LOG_H2("Decide");
        SASSERT(can_decide());
        decide(m_free_vars.next_var());
    }

    void solver::decide(pvar v) {
        LOG("Decide v" << v);
        IF_LOGGING(m_viable.log(v));
        rational val;
        switch (m_viable.find_viable(v, val)) {
        case dd::find_t::empty:
            // NOTE: all such cases should be discovered elsewhere (e.g., during propagation/narrowing)
            //       (fail here in debug mode so we notice if we miss some)
            DEBUG_CODE( UNREACHABLE(); );
            m_free_vars.unassign_var_eh(v);
            set_conflict(v);
            break;
        case dd::find_t::singleton:
            // NOTE: this case may happen legitimately if all other possibilities were excluded by brute force search
            assign_core(v, val, justification::propagation(m_level));
            break;
        case dd::find_t::multiple:
            push_level();
            assign_core(v, val, justification::decision(m_level));
            break;
        }
    }

    void solver::assign_core(pvar v, rational const& val, justification const& j) {
        if (j.is_decision()) 
            ++m_stats.m_num_decisions;
        else 
            ++m_stats.m_num_propagations;
        LOG(assignment_pp(*this, v, val) << " by " << j);
        SASSERT(m_viable.is_viable(v, val));
        SASSERT(std::all_of(assignment().begin(), assignment().end(), [v](auto p) { return p.first != v; }));
        m_value[v] = val;
        m_search.push_assignment(v, val);
        m_trail.push_back(trail_instr_t::assign_i);
        m_justification[v] = j; 
#if ENABLE_LINEAR_SOLVER
        // TODO: convert justification into a format that can be tracked in a depdendency core.
        m_linear_solver.set_value(v, val, UINT_MAX);
#endif
    }

    void solver::set_conflict(signed_constraint c) {
        m_conflict.set(c);
    }

    void solver::set_conflict(pvar v) {
        m_conflict.set(v);
    }

    /**
     * Conflict resolution.
     * - m_conflict are constraints that are infeasible in the current assignment.
     * 1. walk m_search from top down until last variable in m_conflict.
     * 2. resolve constraints in m_cjust to isolate lowest degree polynomials
     *    using variable.
     *    Use Olm-Seidl division by powers of 2 to preserve invertibility.
     * 3. resolve conflict with result of resolution.
     * 4. If the resulting lemma is still infeasible continue, otherwise bail out
     *    and undo the last assignment by accumulating conflict trail (but without resolution).
     * 5. When hitting the last decision, determine whether conflict polynomial is asserting,
     *    If so, apply propagation.
     * 6. Otherwise, add accumulated constraints to explanation for the next viable solution, prune
     *    viable solutions by excluding the previous guess.
     *
     */
    void solver::resolve_conflict() {
        IF_VERBOSE(1, verbose_stream() << "resolve conflict\n");
        LOG_H2("Resolve conflict");
        LOG("\n" << *this);
        LOG("search state: " << m_search);
        for (pvar v = 0; v < m_cjust.size(); ++v)
            LOG("cjust[v" << v << "]: " << m_cjust[v]);
        ++m_stats.m_num_conflicts;

        SASSERT(is_conflict());

        // TODO: subsequent changes to the conflict should update the marks incrementally

        if (m_conflict.conflict_var() != null_var) {
            // This case corresponds to a propagation of conflict_var, except it's not explicitly on the stack.
            resolve_value(m_conflict.conflict_var());
        }

        search_iterator search_it(m_search);
        while (search_it.next()) {
            LOG("Conflict: " << m_conflict);
            auto const& item = *search_it;
            LOG_H2("Working on " << item);
            if (item.is_assignment()) {
                // Resolve over variable assignment
                pvar v = item.var();
                if (!m_conflict.is_pmarked(v))
                    continue;
                justification& j = m_justification[v];
                LOG("Justification: " << j);
                if (j.level() <= base_level())
                    break;
                if (j.is_decision()) {
                    revert_decision(v);
                    return;
                }
                SASSERT(j.is_propagation());
                resolve_value(v);
            }
            else {
                // Resolve over boolean literal
                SASSERT(item.is_boolean());
                sat::literal const lit = item.lit();
                sat::bool_var const var = lit.var();
                if (!m_conflict.is_bmarked(var))
                    continue;
                if (m_bvars.level(var) <= base_level())
                    break;
                if (m_bvars.is_decision(var)) {
                    revert_bool_decision(lit);
                    return;
                }
                
                SASSERT(m_bvars.is_propagation(var));
                resolve_bool(lit);
            }
        }
        report_unsat();
    }

    /** Conflict resolution case where propagation 'v := ...' is on top of the stack */
    void solver::resolve_value(pvar v) {
        m_conflict.resolve_value(v, m_cjust[v]);
    }

    /** Conflict resolution case where boolean literal 'lit' is on top of the stack */
    void solver::resolve_bool(sat::literal lit) {
        LOG_H3("resolve_bool: " << lit);
        sat::bool_var const var = lit.var();
        SASSERT(m_bvars.is_propagation(var));
        // NOTE: boolean resolution should work normally even in bailout mode.
        clause* other = m_bvars.reason(var);
        m_conflict.resolve(m_constraints, var, *other);
    }

    void solver::report_unsat() {
        backjump(base_level());
        SASSERT(!m_conflict.empty());
    }

    void solver::unsat_core(unsigned_vector& deps) {
        NOT_IMPLEMENTED_YET();   // TODO: needs to be fixed to work with conflict_core
        /*
        deps.reset();
        p_dependency_ref conflict_dep(m_dm);
        for (auto& c : m_conflict.units())
            if (c)
                conflict_dep = m_dm.mk_join(c->unit_dep(), conflict_dep);
        for (auto& c : m_conflict.clauses())
            conflict_dep = m_dm.mk_join(c->dep(), conflict_dep);
        m_dm.linearize(conflict_dep, deps);
        */
    }

    void solver::learn_lemma(pvar v, clause_ref lemma) {
        LOG("Learning: " << show_deref(lemma));
        if (!lemma)
            return;
        SASSERT(lemma->size() > 0);
        lemma->set_justified_var(v);
        add_lemma(lemma);
        sat::literal lit = decide_bool(*lemma);
        SASSERT(lit != sat::null_literal);
    }

    // Guess a literal from the given clause; returns the guessed constraint
    sat::literal solver::decide_bool(clause& lemma) {
        LOG_H3("Guessing literal in lemma: " << lemma);
        IF_LOGGING(m_viable.log());
        LOG("Boolean assignment: " << m_bvars);

        // To make a guess, we need to find an unassigned literal that is not false in the current model.
        auto is_suitable = [this](sat::literal lit) -> bool {
            if (m_bvars.value(lit) == l_false)  // already assigned => cannot decide on this (comes from either lemma LHS or previously decided literals that are now changed to propagation)
                return false;
            SASSERT(m_bvars.value(lit) != l_true);  // cannot happen in a valid lemma
            signed_constraint c = m_constraints.lookup(lit);
            SASSERT(!c.is_currently_true(*this));  // should not happen in a valid lemma
            return !c.is_currently_false(*this);
        };

        sat::literal choice = sat::null_literal;
        unsigned num_choices = 0;  // TODO: should probably cache this? (or rather the suitability of each literal... it won't change until we backtrack beyond the current point)

        for (sat::literal lit : lemma) {
            if (is_suitable(lit)) {
                num_choices++;
                if (choice == sat::null_literal)
                    choice = lit;
            }
        }
        LOG_V("num_choices: " << num_choices);

        signed_constraint c = m_constraints.lookup(choice);
        push_cjust(lemma.justified_var(), c);

        if (num_choices == 0) {
            // This case may happen when all undefined literals are false under the current variable assignment.
            // TODO: The question is whether such lemmas should be generated? Check test_monot() for such a case.
            // set_conflict(lemma);
            NOT_IMPLEMENTED_YET();
        } else if (num_choices == 1)
            propagate_bool(choice, &lemma);
        else
            decide_bool(choice, lemma);
        return choice;
    }

    /**
     * Revert a decision that caused a conflict.
     * Variable v was assigned by a decision at position i in the search stack.
     */
    void solver::revert_decision(pvar v) {
        rational val = m_value[v];
        LOG_H3("Reverting decision: pvar " << v << " := " << val);
        SASSERT(m_justification[v].is_decision());

        clause_ref lemma = m_conflict.build_lemma().build();
        m_conflict.reset();

        backjump(m_justification[v].level() - 1);

        // The justification for this restriction is the guessed constraint from the lemma.
        // cjust[v] will be updated accordingly by decide_bool.
        m_viable.add_non_viable(v, val);
        learn_lemma(v, std::move(lemma));

        if (is_conflict()) {
            LOG_H1("Conflict during revert_decision/learn_lemma!");
            return;
        }

        narrow(v);

        if (m_justification[v].is_unassigned()) {
            m_free_vars.del_var_eh(v);
            decide(v);
        }
    }

    bool solver::is_decision(search_item const& item) const {
        if (item.is_assignment())
            return m_justification[item.var()].is_decision();
        else
            return m_bvars.is_decision(item.lit().var());
    }

    void solver::revert_bool_decision(sat::literal lit) {
        sat::bool_var const var = lit.var();
        LOG_H3("Reverting boolean decision: " << lit);
        SASSERT(m_bvars.is_decision(var));

        // Current situation: we have a decision for boolean literal L on top of the stack, and a conflict core.
        //
        // In a CDCL solver, this means ~L is in the lemma (actually, as the asserting literal). We drop the decision and replace it by the propagation (~L)^lemma.
        //
        // - we know L must be false
        // - if L isn't in the core, we can still add it (weakening the lemma) to obtain "core => ~L"
        // - then we can add the propagation (~L)^lemma and continue with the next guess

        // Note that if we arrive at this point, the variables in L are "relevant" to the conflict (otherwise we would have skipped L).
        // So the subsequent steps must have contained one of these:
        // - propagation of some variable v from L (and maybe other constraints)
        //      (v := val)^{L, ...}
        //      this means L is in core, unless we core-reduced it away
        // - propagation of L' from L
        //      (L')^{L' \/ ¬L \/ ...}
        //      again L is in core, unless we core-reduced it away

        clause_builder reason_builder = m_conflict.build_lemma();
        m_conflict.reset();

        bool contains_lit = std::find(reason_builder.begin(), reason_builder.end(), ~lit);
        if (!contains_lit) {
            // At this point, we do not have ~lit in the reason.
            // For now, we simply add it (thus weakening the reason)
            //
            // Alternative (to be considered later):
            // - 'reason' itself (without ~L) would already be an explanation for ~L
            // - however if it doesn't contain ~L, it breaks the boolean resolution invariant
            // - would need to check what we can gain by relaxing that invariant
            // - drawback: might have to bail out at boolean resolution
            // Also: maybe we can skip ~L in some cases? but in that case it shouldn't be marked.
            //
            reason_builder.push(~lit);
        }
        clause_ref reason = reason_builder.build();

        // The lemma where 'lit' comes from.
        // Currently, boolean decisions always come from guessing a literal of a learned non-unit lemma.
        clause* lemma = m_bvars.lemma(var);  // need to grab this while 'lit' is still assigned
        SASSERT(lemma);

        backjump(m_bvars.level(var) - 1);

        add_lemma(reason);
        propagate_bool(~lit, reason.get());
        if (is_conflict()) {
            LOG_H1("Conflict during revert_bool_decision/propagate_bool!");
            return;
        }
        decide_bool(*lemma);
    }

    void solver::decide_bool(sat::literal lit, clause& lemma) {
        push_level();
        LOG_H2("Decide boolean literal " << lit << " @ " << m_level);
        assign_bool(m_level, lit, nullptr, &lemma);
    }

    void solver::propagate_bool(sat::literal lit, clause* reason) {
        propagate_bool_at(m_level, lit, reason);
    }

    void solver::propagate_bool_at(unsigned level, sat::literal lit, clause* reason) {
        LOG("Propagate boolean literal " << lit << " @ " << level << " by " << show_deref(reason));
        SASSERT(reason);
        SASSERT(level <= m_level);
        assign_bool(level, lit, reason, nullptr);
    }

    /// Assign a boolean literal and put it on the search stack,
    /// and activate the corresponding constraint.
    void solver::assign_bool(unsigned level, sat::literal lit, clause* reason, clause* lemma) {
        LOG("Assigning boolean literal: " << lit);
        m_bvars.assign(lit, level, reason, lemma);
        m_trail.push_back(trail_instr_t::assign_bool_i);
        m_search.push_boolean(lit);
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
        add_watch(c);
        c.narrow(*this);
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.activate_constraint(c);
#endif
    }

    /// Deactivate constraint
    void solver::deactivate_constraint(signed_constraint c) {
        LOG("Deactivating constraint: " << c);
        erase_watch(c);
    }

    void solver::backjump(unsigned new_level) {
        LOG_H3("Backjumping to level " << new_level << " from level " << m_level);
        unsigned num_levels = m_level - new_level;
        if (num_levels > 0) 
            pop_levels(num_levels);        
    }

    /**
     * placeholder for factoring/gcd common factors
     */
    void solver::narrow(pvar v) {

    }

    // Add lemma to storage but do not activate it
    void solver::add_lemma(clause_ref lemma) {
        if (!lemma)
            return;
        LOG("Lemma: " << show_deref(lemma));
        for (sat::literal lit : *lemma) {
            LOG("   Literal " << lit << " is: " << m_constraints.lookup(lit));
            // TODO: fully evaluated constraints must be put onto the stack as propagations.
            signed_constraint c = m_constraints.lookup(lit);
            SASSERT(m_bvars.is_assigned(lit) && !c.is_currently_false(*this));
            SASSERT(m_bvars.is_assigned(lit) && !c.is_currently_true(*this));
        }
        SASSERT(lemma->size() > 0);
        clause* cl = m_constraints.store(std::move(lemma));
        m_redundant_clauses.push_back(cl);
        if (cl->size() == 1) {
            signed_constraint c = m_constraints.lookup((*cl)[0]);
            c->set_unit_clause(cl);
        }
    }

    void solver::insert_constraint(signed_constraints& cs, signed_constraint c) {
        SASSERT(c);
        LOG_V("INSERTING: " << c);
        cs.push_back(c);
        SASSERT(invariant(cs)); 
    }   

    void solver::push() {
        LOG("Push user scope");
        push_level();
        m_base_levels.push_back(m_level);
    }

    void solver::pop(unsigned num_scopes) {
        unsigned base_level = m_base_levels[m_base_levels.size() - num_scopes];
        LOG("Pop " << num_scopes << " user scopes; lowest popped level = " << base_level << "; current level = " << m_level);
        pop_levels(m_level - base_level + 1);
        m_conflict.reset();   // TODO: maybe keep conflict if level of all constraints is lower than base_level?
    }

    bool solver::at_base_level() const {
        return m_level == base_level();
    }
    
    unsigned solver::base_level() const {
        return m_base_levels.empty() ? 0 : m_base_levels.back();
    }

    bool solver::try_eval(pdd const& p, rational& out_value) const {
        pdd r = p.subst_val(assignment());
        if (r.is_val())
            out_value = r.val();
        return r.is_val();
    }

    std::ostream& solver::display(std::ostream& out) const {
        out << "Assignment:\n";
        for (auto [v, val] : assignment()) {
            auto j = m_justification[v];
            out << "\t" << assignment_pp(*this, v, val) << " @" << j.level();
            if (j.is_propagation())
                out << " " << m_cjust[v];
            out << "\n";
            // out << m_viable[v] << "\n";
        }
        out << "Boolean assignment:\n\t" << m_bvars << "\n";
        out << "Constraints:\n";
        for (auto c : m_constraints)
            out << "\t" << c << "\n";
        out << "Redundant clauses:\n";
        for (auto* cl : m_redundant_clauses) {
            out << "\t" << *cl << "\n";
            for (auto lit : *cl) {
                auto c = m_constraints.lookup(lit.var());
                out << "\t\t" << lit.var() << ": " << *c << "\n";
            }
        }
        return out;
    }

    std::ostream& assignments_pp::display(std::ostream& out) const {
        for (auto [var, val] : s.assignment())
            out << assignment_pp(s, var, val) << " ";
        return out;
    }

    std::ostream& assignment_pp::display(std::ostream& out) const {
        out << "v" << var << " := ";
        rational const& p = rational::power_of_two(s.size(var));
        if (val > mod(-val, p))
            return out << -mod(-val, p);
        else 
            return out << val;
    }
    

    void solver::collect_statistics(statistics& st) const {
        st.update("polysat iterations",   m_stats.m_num_iterations);
        st.update("polysat decisions",    m_stats.m_num_decisions);
        st.update("polysat conflicts",    m_stats.m_num_conflicts);
        st.update("polysat bailouts",     m_stats.m_num_bailouts);
        st.update("polysat propagations", m_stats.m_num_propagations);
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
        // Skip boolean variables that aren't active yet
        uint_set skip;
        for (unsigned i = m_qhead; i < m_search.size(); ++i)
            if (m_search[i].is_boolean())
                skip.insert(m_search[i].lit().var());
        for (auto c : m_constraints) {
            if (!c->has_bvar())
                continue;
            if (skip.contains(c->bvar()))
                continue;

            lbool value = m_bvars.value(c->bvar());
            if (value == l_undef)
                continue;
            bool is_positive = value == l_true;
            int64_t num_watches = 0;
            signed_constraint sc(c, is_positive);
            for (auto const& wlist : m_watch) {
                auto n = std::count(wlist.begin(), wlist.end(), sc);
                VERIFY(n <= 1);  // no duplicates in the watchlist
                num_watches += n;
            }
            unsigned expected_watches = std::min(2u, c->vars().size());
            if (num_watches != expected_watches)
                LOG("wrong number of watches: " << c);
            SASSERT_EQ(num_watches, expected_watches);
        }
        return true;
    }

    /** Check that boolean assignment and constraint evaluation are consistent */
    bool solver::assignment_invariant() {
        for (sat::bool_var v = m_bvars.size(); v-- > 0; ) {
            sat::literal lit(v);
            if (m_bvars.value(lit) == l_true)
                SASSERT(!m_constraints.lookup(lit).is_currently_false(*this));
            if (m_bvars.value(lit) == l_false)
                SASSERT(!m_constraints.lookup(lit).is_currently_true(*this));
        }
        return true;
    }

    /// Check that all original constraints are satisfied by the current model.
    bool solver::verify_sat() {
        LOG_H1("Checking current model...");
        LOG("Assignment: " << assignments_pp(*this));
        bool all_ok = true;
        for (auto s : m_search) {
            if (s.is_boolean()) {
                bool ok = m_bvars.value(s.lit()) == l_true;
                LOG((ok ? "PASS" : "FAIL") << ": " << s.lit());
                all_ok = all_ok && ok;
            }
        }
        if (all_ok) LOG("All good!");
        return true;
    }
}


