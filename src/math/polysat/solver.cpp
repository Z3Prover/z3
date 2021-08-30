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
        while (m_lim.inc()) {
            m_stats.m_num_iterations++;
            LOG_H1("Next solving loop iteration (#" << m_stats.m_num_iterations << ")");
            LOG("Free variables: " << m_free_vars);
            LOG("Assignment:     " << assignments_pp(*this));
            if (!m_conflict.empty()) LOG("Conflict:       " << m_conflict);
            IF_LOGGING(m_viable.log());

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

    scoped_signed_constraint solver::mk_eq(pdd const& p) {
        return m_constraints.eq(m_level, p);
    }

    scoped_signed_constraint solver::mk_diseq(pdd const& p) {
        return ~m_constraints.eq(m_level, p);
    }

    scoped_signed_constraint solver::mk_ule(pdd const& p, pdd const& q) {
        return m_constraints.ule(m_level, p, q);
    }

    scoped_signed_constraint solver::mk_ult(pdd const& p, pdd const& q) {
        return m_constraints.ult(m_level, p, q);
    }

    scoped_signed_constraint solver::mk_sle(pdd const& p, pdd const& q) {
        return m_constraints.sle(m_level, p, q);
    }

    scoped_signed_constraint solver::mk_slt(pdd const& p, pdd const& q) {
        return m_constraints.slt(m_level, p, q);
    }

    void solver::new_constraint(scoped_signed_constraint sc, unsigned dep, bool activate) {
        VERIFY(at_base_level());
        SASSERT(sc);
        SASSERT(activate || dep != null_dependency);  // if we don't activate the constraint, we need the dependency to access it again later.
        signed_constraint c = sc.get_signed();
        m_constraints.store(sc.detach());
        clause* unit = m_constraints.store(clause::from_unit(c, mk_dep_ref(dep)));
        c->set_unit_clause(unit);
        if (dep != null_dependency)
            m_constraints.register_external(c.get());
        LOG("New constraint: " << c);
        m_original.push_back(c);
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.new_constraint(*c.get());
#endif
        if (activate && !is_conflict())
            activate_constraint_base(c);
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
        LOG_H2("Propagate boolean literal " << lit);
        signed_constraint c = m_constraints.lookup(lit);
        (void)c;
        SASSERT(c);
        // c->narrow(*this);
    }

    void solver::propagate(pvar v) {
        LOG_H2("Propagate pvar " << v);
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
        (void)target_level;
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
                signed_constraint c = m_constraints.lookup(lit);
                deactivate_constraint(c);
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
            default:
                UNREACHABLE();
            }
            m_trail.pop_back();
        }
        pop_constraints(m_original);
        pop_constraints(m_redundant);
        m_constraints.release_level(m_level + 1);
        SASSERT(m_level == target_level);
    }

    void solver::pop_constraints(signed_constraints& cs) {
        VERIFY(invariant(cs));
        while (!cs.empty() && cs.back()->level() > m_level) {
            deactivate_constraint(cs.back());
            cs.pop_back();
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
        m_conflict.set(v, m_cjust[v]);
    }

    void solver::set_marks(conflict_core const& cc) {
        for (auto c : cc.constraints())
            if (c)
                set_marks(*c);
    }

    void solver::set_marks(constraint const& c) {
        if (c.bvar() != sat::null_bool_var)
            m_bvars.set_mark(c.bvar());
        for (auto v : c.vars())
            set_mark(v);
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
        ++m_stats.m_num_conflicts;

        SASSERT(is_conflict());

        NOT_IMPLEMENTED_YET();  // TODO: needs to be refactored to use conflict_core, will be moved to conflict_explainer

        /*
        if (m_conflict.units().size() == 1 && !m_conflict.units()[0]) {
            report_unsat();
            return;
        }

        pvar conflict_var = null_var;
        clause_ref lemma;
        for (auto v : m_conflict.vars(m_constraints))
            if (!m_viable.has_viable(v)) {
                SASSERT(conflict_var == null_var || conflict_var == v);  // at most one variable can be empty
                conflict_var = v;
            }
        reset_marks();
        m_bvars.reset_marks();
        set_marks(m_conflict);

        if (m_conflict.clauses().empty() && conflict_var != null_var) {
            LOG_H2("Conflict due to empty viable set for pvar " << conflict_var);
            clause_ref new_lemma;
            if (forbidden_intervals::explain(*this, m_conflict.units(), conflict_var, new_lemma)) {
                SASSERT(new_lemma);
                clause& cl = *new_lemma.get();
                LOG_H3("Lemma from forbidden intervals (size: " << cl.size() << ")");
                for (sat::literal lit : cl) {
                    LOG("Literal: " << lit);
                    constraint* c = m_constraints.lookup(lit.var());
                    for (auto v : c->vars())
                        set_mark(v);
                }
                SASSERT(cl.size() > 0);
                lemma = std::move(new_lemma);
                m_conflict.reset();
                m_conflict.push_back(lemma);
                reset_marks();
                m_bvars.reset_marks();
                set_marks(*lemma.get());
            }
            else {
                conflict_explainer cx(*this, m_conflict);
                lemma = cx.resolve(conflict_var, {});
                LOG("resolved: " << show_deref(lemma));
                // SASSERT(false && "pause on explanation");
            }
        }

        for (unsigned i = m_search.size(); i-- > 0; ) {
            auto const& item = m_search[i];
            if (item.is_assignment()) {
                // Resolve over variable assignment
                pvar v = item.var();
                LOG_H2("Working on pvar " << v);
                if (!is_marked(v))
                    continue;
                justification& j = m_justification[v];
                LOG("Justification: " << j);
                if (j.level() <= base_level()) {
                    report_unsat();
                    return;
                }
                if (j.is_decision()) {
                    revert_decision(v, lemma);
                    return;
                }
                SASSERT(j.is_propagation());
                LOG("Lemma: " << show_deref(lemma));
                clause_ref new_lemma = resolve(v);
                LOG("New Lemma: " << show_deref(new_lemma));
                // SASSERT(new_lemma); // TODO: only for debugging, to have a breakpoint on resolution failure
                if (!new_lemma) {
                    backtrack(i, lemma);
                    return;
                }
                if (new_lemma->is_always_false(*this)) {
                    clause* cl = new_lemma.get();
                    learn_lemma(v, std::move(new_lemma));
                    m_conflict.reset();
                    m_conflict.push_back(cl);
                    report_unsat();
                    return;
                }
                if (!new_lemma->is_currently_false(*this)) {
                    backtrack(i, lemma);
                    return;
                }
                lemma = std::move(new_lemma);
                reset_marks();
                m_bvars.reset_marks();
                set_marks(*lemma.get());
                m_conflict.reset();
                m_conflict.push_back(lemma.get());
            }
            else {
                // Resolve over boolean literal
                SASSERT(item.is_boolean());
                sat::literal const lit = item.lit();
                LOG_H2("Working on boolean literal " << lit);
                sat::bool_var const var = lit.var();
                if (!m_bvars.is_marked(var))
                    continue;
                if (m_bvars.level(var) <= base_level()) {
                    report_unsat();
                    return;
                }
                if (m_bvars.is_decision(var)) {
                    // SASSERT(std::count(lemma->begin(), lemma->end(), ~lit) > 0);
                    revert_bool_decision(lit, lemma);
                    return;
                }
                SASSERT(m_bvars.is_propagation(var));
                LOG("Lemma: " << show_deref(lemma));
                clause_ref new_lemma = resolve_bool(lit);
                if (!new_lemma) {
                    backtrack(i, lemma);
                    return;
                }
                SASSERT(new_lemma);
                LOG("new_lemma: " << show_deref(new_lemma));
                LOG("new_lemma is always false: " << new_lemma->is_always_false(*this));
                if (new_lemma->is_always_false(*this)) {
                    // learn_lemma(v, new_lemma);
                    m_conflict.reset();
                    m_conflict.push_back(std::move(new_lemma));
                    report_unsat();
                    return;
                }
                LOG("new_lemma is currently false: " << new_lemma->is_currently_false(*this));
                // if (!new_lemma->is_currently_false(*this)) {
                //     backtrack(i, lemma);
                //     return;
                // }
                lemma = std::move(new_lemma);
                reset_marks();
                m_bvars.reset_marks();
                set_marks(*lemma.get());
                m_conflict.reset();
                m_conflict.push_back(lemma.get());
            }
        }
        report_unsat();
        */
    }

    clause_ref solver::resolve_bool(sat::literal lit) {
        NOT_IMPLEMENTED_YET();  return nullptr;
        /*
        if (m_conflict.size() != 1)
            return nullptr;
        if (m_conflict.clauses().size() != 1)
            return nullptr;
        LOG_H3("resolve_bool");
        clause* lemma = m_conflict.clauses()[0];
        SASSERT(lemma);
        SASSERT(m_bvars.is_propagation(lit.var()));
        clause* other = m_bvars.reason(lit.var());
        SASSERT(other);
        LOG("lemma: " << show_deref(lemma));
        LOG("other: " << show_deref(other));
        VERIFY(lemma->resolve(lit.var(), *other));
        LOG("resolved: " << show_deref(lemma));

        // unassign constraints whose current value does not agree with their occurrence in the lemma
        for (sat::literal lit : *lemma) {
            constraint *c = m_constraints.lookup(lit.var());
            if (!c->is_undef() && c ->blit() != lit) {
                LOG("unassigning: " << show_deref(c));
                c->unassign();
            }
        }

        return lemma;  // currently modified in-place
        */
    }

    void solver::backtrack(unsigned i, clause_ref lemma) {
        NOT_IMPLEMENTED_YET();
        /*
        do {
            auto const& item = m_search[i];
            if (item.is_assignment()) {
                // Backtrack over variable assignment
                auto v = item.var();
                LOG_H2("Working on pvar " << v);
                if (!is_marked(v))
                    continue;
                justification& j = m_justification[v];
                if (j.level() <= base_level())
                    break;
                if (j.is_decision()) {
                    revert_decision(v, lemma);
                    return;
                }
                // retrieve constraint used for propagation
                // add variables to COI
                SASSERT(j.is_propagation());
                for (auto* c : m_cjust[v]) {
                    for (auto w : c->vars())
                        set_mark(w);
                    if (c->bvar() != sat::null_bool_var)
                        m_bvars.set_mark(c->bvar());
                    m_conflict.push_back(c);
                }
            }
            else {
                // Backtrack over boolean literal
                SASSERT(item.is_boolean());
                sat::literal lit = item.lit();
                LOG_H2("Working on boolean literal " << lit);
                sat::bool_var var = lit.var();
                SASSERT(m_bvars.is_assigned(var));
                if (!m_bvars.is_marked(var))
                    continue;
                if (m_bvars.level(var) <= base_level())
                    break;
                if (m_bvars.is_decision(var)) {
                    revert_bool_decision(lit, lemma);
                    return;
                }
                SASSERT(m_bvars.is_propagation(var));
                clause* other = m_bvars.reason(var);
                set_marks(*other);
                m_conflict.push_back(other);
            }
        }
        while (i-- > 0);
        add_lemma(lemma);  // TODO: this lemma is stored but otherwise "lost" because it will not be activated / not added to any watch data structures
        report_unsat();
        */
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
        if (!lemma)
            return;
        LOG("Learning: " << show_deref(lemma));
        SASSERT(lemma->size() > 0);
        SASSERT(m_conflict_level <= m_justification[v].level());
        clause* cl = lemma.get();
        add_lemma(std::move(lemma));
        if (cl->size() == 1) {
            sat::literal lit = cl->literals()[0];
            signed_constraint c = m_constraints.lookup(lit);
            c->set_unit_clause(cl);
            push_cjust(v, c);
            activate_constraint_base(c);
        }
        else {
            sat::literal lit = decide_bool(*cl);
            SASSERT(lit != sat::null_literal);
            signed_constraint c = m_constraints.lookup(lit);
            push_cjust(v, c);
        }
    }

    // Guess a literal from the given clause; returns the guessed constraint
    sat::literal solver::decide_bool(clause& lemma) {
        LOG_H3("Guessing literal in lemma: " << lemma);
        IF_LOGGING(m_viable.log());
        LOG("Boolean assignment: " << m_bvars);
        SASSERT(lemma.size() >= 2);

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
        unsigned num_choices = 0;  // TODO: should probably cache this?

        for (sat::literal lit : lemma) {
            if (is_suitable(lit)) {
                num_choices++;
                if (choice == sat::null_literal)
                    choice = lit;
            }
        }
        LOG_V("num_choices: " << num_choices);

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
     *
     * TODO: we could resolve constraints in cjust[v] against each other to 
     * obtain stronger propagation. Example:
     *  (x + 1)*P = 0 and (x + 1)*Q = 0, where gcd(P,Q) = 1, then we have x + 1 = 0.
     * We refer to this process as narrowing.
     * In general form it can rely on factoring.
     * Root finding can further prune viable.
     */
    void solver::revert_decision(pvar v, clause_ref reason) {
        rational val = m_value[v];
        LOG_H3("Reverting decision: pvar " << v << " := " << val);
        NOT_IMPLEMENTED_YET();
        /*
        SASSERT(m_justification[v].is_decision());
        backjump(m_justification[v].level()-1);

        m_viable.add_non_viable(v, val);

        auto confl = std::move(m_conflict);
        m_conflict.reset();

        for (constraint* c : confl.units()) {
            // Add the conflict as justification for the exclusion of 'val'
            push_cjust(v, c);
            // NOTE: in general, narrow may change the conflict.
            //       But since we just backjumped, narrowing should not result in an additional conflict.
            // TODO: this call to "narrow" may still lead to a conflict,
            //       because we do not detect all conflicts immediately.
            //       Consider:
            //       - Assert constraint zx > yx, watching y and z.
            //       - Guess x = 0.
            //       - We have a conflict but we don't know. It will be discovered when y and z are assigned,
            //         and then may lead to an assertion failure through this call to narrow.
            // TODO: what to do with "unassigned" constraints at this point? (we probably should have resolved those away, even in the 'backtrack' case.)
            //       NOTE: they are constraints from clauses that were added to cjust… how to deal with that? should we add the whole clause to cjust?
            SASSERT(!c->is_undef());
            // if (!c->is_undef())  // TODO: this check to be removed once this is fixed properly.
                c->narrow(*this);
            if (is_conflict()) {
                LOG_H1("Conflict during revert_decision/narrow!");
                return;
            }
        }
        // m_conflict.reset();

        learn_lemma(v, std::move(reason));

        if (is_conflict()) {
            LOG_H1("Conflict during revert_decision/learn_lemma!");
            return;
        }

        narrow(v);
        if (m_justification[v].is_unassigned()) {
            m_free_vars.del_var_eh(v);
            decide(v);
        }
        */
    }
    
    void solver::revert_bool_decision(sat::literal lit, clause_ref reason) {
        sat::bool_var const var = lit.var();
        LOG_H3("Reverting boolean decision: " << lit);
        SASSERT(m_bvars.is_decision(var));

        NOT_IMPLEMENTED_YET();
        /*

        if (reason) {
            LOG("Reason: " << show_deref(reason));
            bool contains_var = std::any_of(reason->begin(), reason->end(), [var](sat::literal reason_lit) { return reason_lit.var() == var; });
            if (!contains_var) {
                // TODO: in this case, we got here via 'backtrack'. What to do if the reason does not contain lit?
                // * 'reason' is still a perfectly good lemma and a summary of the conflict (the lemma roughly corresponds to ~conflict)
                // * the conflict is the reason for flipping 'lit'
                // * thus we just add '~lit' to 'reason' and see it as "conflict => ~lit".
                auto lits = reason->literals();
                lits.push_back(~lit);
                reason = clause::from_literals(reason->level(), {reason->dep(), m_dm}, lits, reason->new_constraints());
            }
            SASSERT(std::any_of(reason->begin(), reason->end(), [lit](sat::literal reason_lit) { return reason_lit == ~lit; }));
        }
        else {
            LOG_H3("Empty reason");
            LOG("Conflict: " << m_conflict);
            // TODO: what to do when reason is NULL?
            // * this means we were unable to build a lemma for the current conflict.
            // * the reason for reverting this decision then needs to be the (negation of the) conflicting literals. Or we give up on resolving this lemma?
            SASSERT(m_conflict.clauses().empty());  // not sure how to handle otherwise
            clause_builder clause(*this);
            // unsigned reason_lvl = m_constraints.lookup(lit.var())->level();
            // p_dependency_ref reason_dep(m_constraints.lookup(lit.var())->dep(), m_dm);
            clause.push_literal(~lit);  // propagated literal
            for (auto c : m_conflict.units()) {
                if (c->bvar() == var)
                    continue;
                if (c->is_undef())  // TODO: see revert_decision for a note on this.
                    continue;
                // reason_lvl = std::max(reason_lvl, c->level());
                // reason_dep = m_dm.mk_join(reason_dep, c->dep());
                clause.push_literal(c->blit());
            }
            reason = clause.build();
            LOG("Made-up reason: " << show_deref(reason));
        }

        clause* lemma = m_bvars.lemma(var);  // need to grab this while 'lit' is still assigned
        SASSERT(lemma);

        backjump(m_bvars.level(var) - 1);

        for (constraint* c : m_conflict.units()) {
            if (c->bvar() == var)
                continue;
            // NOTE: in general, narrow may change the conflict.
            //       But since we just backjumped, narrowing should not result in an additional conflict.
            if (c->is_undef())  // TODO: see revert_decision for a note on this.
                continue;
            c->narrow(*this);
            if (is_conflict()) {
                LOG_H1("Conflict during revert_bool_decision/narrow!");
                return;
            }
        }
        m_conflict.reset();

        clause* reason_cl = reason.get();
        add_lemma(std::move(reason));
        propagate_bool(~lit, reason_cl);
        if (is_conflict()) {
            LOG_H1("Conflict during revert_bool_decision/propagate_bool!");
            return;
        }

        decide_bool(*lemma);
        */
    }

    void solver::decide_bool(sat::literal lit, clause& lemma) {
        push_level();
        LOG_H2("Decide boolean literal " << lit << " @ " << m_level);
        assign_bool_backtrackable(lit, nullptr, &lemma);
    }

    void solver::propagate_bool(sat::literal lit, clause* reason) {
        LOG("Propagate boolean literal " << lit << " @ " << m_level << " by " << show_deref(reason));
        SASSERT(reason);
        if (reason->literals().size() == 1) {
            SASSERT(reason->literals()[0] == lit);
            signed_constraint c = m_constraints.lookup(lit);
            // m_redundant.push_back(c);
            activate_constraint_base(c);
        }
        else
            assign_bool_backtrackable(lit, reason, nullptr);
    }

    /// Assign a boolean literal and put it on the search stack,
    /// and activate the corresponding constraint.
    void solver::assign_bool_backtrackable(sat::literal lit, clause* reason, clause* lemma) {
        assign_bool_core(lit, reason, lemma);

        m_trail.push_back(trail_instr_t::assign_bool_i);
        m_search.push_boolean(lit);

        signed_constraint c = m_constraints.lookup(lit);
        activate_constraint(c);
    }

    /// Activate a constraint at the base level.
    /// Used for external unit constraints and unit consequences.
    void solver::activate_constraint_base(signed_constraint c) {
        SASSERT(c);
        LOG("\n" << *this);
        // c must be in m_original or m_redundant so it can be deactivated properly when popping the base level
        SASSERT_EQ(std::count(m_original.begin(), m_original.end(), c) + std::count(m_redundant.begin(), m_redundant.end(), c), 1);
        assign_bool_core(c.blit(), nullptr, nullptr);
        activate_constraint(c);
    }

    /// Assign a boolean literal
    void solver::assign_bool_core(sat::literal lit, clause* reason, clause* lemma) {
        LOG("Assigning boolean literal: " << lit);
        m_bvars.assign(lit, m_level, reason, lemma);
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
        m_linear_solver.activate_constraint(c.is_positive(), c.get());   // TODO: linear solver should probably take a signed_constraint
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
        SASSERT(lemma->size() > 0);
        clause* cl = m_constraints.store(std::move(lemma));
        m_redundant_clauses.push_back(cl);
        if (cl->size() == 1) {
            signed_constraint c = m_constraints.lookup(cl->literals()[0]);
            insert_constraint(m_redundant, c);
        }
    }

    void solver::insert_constraint(signed_constraints& cs, signed_constraint c) {
        SASSERT(c);
        LOG_V("INSERTING: " << c);
        cs.push_back(c);
        for (unsigned i = cs.size() - 1; i-- > 0; ) {
            auto c1 = cs[i + 1];
            auto c2 = cs[i];
            if (c1->level() >= c2->level())
                break;
            std::swap(cs[i], cs[i+1]);
        }
        SASSERT(invariant(cs)); 
    }
    
    void solver::reset_marks() {
        LOG_V("-------------------------- (reset variable marks)");
        m_marks.reserve(m_vars.size());
        m_clock++;
        if (m_clock != 0)
            return;
        m_clock++;
        m_marks.fill(0);        
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

    // bool solver::active_at_base_level(sat::bool_var bvar) const {
    //     // NOTE: this active_at_base_level is actually not what we want!!!
    //     //          first of all, it might not really be a base level: could be a non-base level between previous base levels.
    //     //          in that case, how do we determine the right dependencies???
    //     //          secondly, we are interested in "unit clauses", not as much whether we assigned something on the base level...
    //     //          TODO: however, propagating stuff at the base level... need to be careful with dependencies there... might need to turn all base-level propagations into unit clauses...
    //     VERIFY(false);
    //     // bool res = m_bvars.is_assigned(bvar) && m_bvars.level(bvar) <= base_level();
    //     // SASSERT_EQ(res, !!m_constraints.lookup(bvar)->unit_clause());
    //     // return res;
    // }

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
        out << "Original:\n";
        for (auto c : m_original)
            out << "\t" << c << "\n";
        out << "Redundant:\n";
        for (auto c : m_redundant)
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
        st.update("polysat propagations", m_stats.m_num_propagations);
    }

    bool solver::invariant() {
        invariant(m_original);
        invariant(m_redundant);
        return true;
    }

    /**
     * constraints are sorted by levels so they can be removed when levels are popped.
     */
    bool solver::invariant(signed_constraints const& cs) {
        unsigned sz = cs.size();
        for (unsigned i = 0; i + 1 < sz; ++i) 
            VERIFY(cs[i]->level() <= cs[i + 1]->level());
        return true;
    }

    /**
     * Check that two variables of each constraint are watched.
     */
    bool solver::wlist_invariant() {
        signed_constraints cs;
        cs.append(m_original.size(), m_original.data());
        cs.append(m_redundant.size(), m_redundant.data());
        for (auto c : cs) {
            int64_t num_watches = 0;
            for (auto const& wlist : m_watch) {
                auto n = std::count(wlist.begin(), wlist.end(), c);
                VERIFY(n <= 1);  // no duplicates in the watchlist
                num_watches += n;
            }
            switch (c->vars().size()) {
                case 0:  VERIFY(num_watches == 0); break;
                case 1:  VERIFY(num_watches == 1); break;
                default: VERIFY(num_watches == 2); break;
            }
        }
        return true;
    }

    /// Check that all original constraints are satisfied by the current model.
    bool solver::verify_sat() {
        LOG_H1("Checking current model...");
        LOG("Assignment: " << assignments_pp(*this));
        bool all_ok = true;
        for (auto c : m_original) {
            bool ok = c.is_currently_true(*this);
            LOG((ok ? "PASS" : "FAIL") << ": " << c);
            all_ok = all_ok && ok;
        }
        if (all_ok) LOG("All good!");
        return true;
    }
}


