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
            LOG_H1("Next solving loop iteration");
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
        m_cjust.push_back(constraints());
        m_watch.push_back(ptr_vector<constraint>());
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

    constraint_literal solver::mk_eq(pdd const& p) {
        return m_constraints.eq(m_level, p);
    }

    constraint_literal solver::mk_diseq(pdd const& p) {
        return ~m_constraints.eq(m_level, p);
    }

    constraint_literal solver::mk_ule(pdd const& p, pdd const& q) {
        return m_constraints.ule(m_level, p, q);
    }

    constraint_literal solver::mk_ult(pdd const& p, pdd const& q) {
        return m_constraints.ult(m_level, p, q);
    }

    constraint_literal solver::mk_sle(pdd const& p, pdd const& q) {
        return m_constraints.sle(m_level, p, q);
    }

    constraint_literal solver::mk_slt(pdd const& p, pdd const& q) {
        return m_constraints.slt(m_level, p, q);
    }

    void solver::new_constraint(constraint_literal cl, unsigned dep, bool activate) {
        VERIFY(at_base_level());
        SASSERT(cl);
        SASSERT(activate || dep != null_dependency);  // if we don't activate the constraint, we need the dependency to access it again later.
        sat::literal lit = cl.literal();
        constraint* c = cl.constraint();
        clause* unit = m_constraints.store(clause::from_unit(std::move(cl), mk_dep_ref(dep)));
        c->set_unit_clause(unit);
        if (dep != null_dependency)
            m_constraints.register_external(c);
        LOG("New constraint: " << *c);
        m_original.push_back(c);
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.new_constraint(*c);
#endif
        if (activate && !is_conflict())
            activate_constraint_base(c, !lit.sign());
    }

    void solver::assign_eh(unsigned dep, bool is_true) {
        VERIFY(at_base_level());
        constraint* c = m_constraints.lookup_external(dep);
        if (!c) {
            LOG("WARN: there is no constraint for dependency " << dep);
            return;
        }
        if (is_conflict())
            return;
        activate_constraint_base(c, is_true);
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
        constraint* c = m_constraints.lookup(lit.var());
        SASSERT(c);
        SASSERT(!c->is_undef());
        // c->narrow(*this);
    }

    void solver::propagate(pvar v) {
        LOG_H2("Propagate pvar " << v);
        auto& wlist = m_watch[v];
        unsigned i = 0, j = 0, sz = wlist.size();
        for (; i < sz && !is_conflict(); ++i) 
            if (!wlist[i]->propagate(*this, v))
                wlist[j++] = wlist[i];
        for (; i < sz; ++i)
            wlist[j++] = wlist[i];
        wlist.shrink(j);
    }

    void solver::propagate(pvar v, rational const& val, constraint& c) {
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
                constraint* c = m_constraints.lookup(lit.var());
                deactivate_constraint(*c);
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

    void solver::pop_constraints(ptr_vector<constraint>& cs) {
        VERIFY(invariant(cs));
        while (!cs.empty() && cs.back()->level() > m_level) {
            deactivate_constraint(*cs.back());
            cs.pop_back();
        }        
    }

    void solver::add_watch(constraint& c) {
        auto const& vars = c.vars();
        if (vars.size() > 0)
            add_watch(c, vars[0]);
        if (vars.size() > 1)
            add_watch(c, vars[1]);
    }

    void solver::add_watch(constraint &c, pvar v) {
        LOG("Watching v" << v << " in constraint " << c);
        m_watch[v].push_back(&c);
    }

    void solver::erase_watch(constraint& c) {
        auto const& vars = c.vars();
        if (vars.size() > 0)
            erase_watch(vars[0], c);
        if (vars.size() > 1)
            erase_watch(vars[1], c);
    }

    void solver::erase_watch(pvar v, constraint& c) {
        if (v == null_var)
            return;
        auto& wlist = m_watch[v];
        unsigned sz = wlist.size();
        for (unsigned i = 0; i < sz; ++i) {
            if (&c == wlist[i]) {
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
        m_linear_solver.set_value(v, val);
#endif
    }

    void solver::set_conflict(constraint& c) { 
        LOG("Conflict: " << c);
        LOG(*this);
        SASSERT(!is_conflict());
        m_conflict.push_back(&c); 
    }

    void solver::set_conflict(clause& cl) {
        LOG("Conflict: " << cl);
        SASSERT(!is_conflict());
        m_conflict.push_back(&cl);
    }

    void solver::set_conflict(pvar v) {
        SASSERT(!is_conflict());
        m_conflict.append(m_cjust[v]);
        if (m_cjust[v].empty())
            m_conflict.push_back(nullptr);
        LOG("Conflict for v" << v << ": " << m_conflict);
    }

    void solver::set_marks(constraint const& c) {
        LOG_V("Marking in: " << c);
        if (c.bvar() != sat::null_bool_var)
            m_bvars.set_mark(c.bvar());
        for (auto v : c.vars())
            set_mark(v);
    }

    void solver::set_marks(clause const& cl) {
        LOG_V("Marking in: " << cl);
        for (auto lit : cl)
            set_marks(*m_constraints.lookup(lit.var()));
    }

    void solver::set_marks(constraints_and_clauses const& cc) {
        for (auto c : cc.units())
            if (c)
                set_marks(*c);
        for (auto cl : cc.clauses())
            set_marks(*cl);
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
        LOG(*this);
        LOG("search state: " << m_search);
        ++m_stats.m_num_conflicts;

        SASSERT(is_conflict());

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
    }

    clause_ref solver::resolve_bool(sat::literal lit) {
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
    }

    void solver::backtrack(unsigned i, clause_ref lemma) {
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
        add_lemma_clause(lemma);  // TODO: handle units correctly
        report_unsat();
    }

    void solver::report_unsat() {
        backjump(base_level());
        SASSERT(!m_conflict.empty());
    }

    void solver::unsat_core(unsigned_vector& deps) {
        deps.reset();
        p_dependency_ref conflict_dep(m_dm);
        for (auto& c : m_conflict.units())
            if (c)
                conflict_dep = m_dm.mk_join(c->unit_dep(), conflict_dep);
        for (auto& c : m_conflict.clauses())
            conflict_dep = m_dm.mk_join(c->dep(), conflict_dep);
        m_dm.linearize(conflict_dep, deps);
    }

    /**
     * The polynomial p encodes an equality that the decision was infeasible.
     * The effect of this function is that the assignment to v is undone and replaced 
     * by a new decision or unit propagation or conflict.
     * We add 'p == 0' as a lemma. The lemma depends on the dependencies used
     * to derive p, and the level of the lemma is the maximal level of the dependencies.
     */
    void solver::learn_lemma(pvar v, clause_ref lemma) {
        if (!lemma)
            return;
        LOG("Learning: " << show_deref(lemma));
        SASSERT(m_conflict_level <= m_justification[v].level());
        if (lemma->size() == 1) {
            constraint_ref c;
            if (lemma->new_constraints().size() > 0) {
                SASSERT_EQ(lemma->new_constraints().size(), 1);
                c = lemma->new_constraints()[0];
            }
            else {
                c = m_constraints.lookup(lemma->literals()[0].var());
            }
            SASSERT_EQ(lemma->literals()[0].var(), c->bvar());
            SASSERT(c);
            add_lemma_unit(c);
            push_cjust(v, c.get());
            activate_constraint_base(c.get(), !lemma->literals()[0].sign());
        }
        else
            learn_lemma_clause(v, std::move(lemma));
    }

    void solver::learn_lemma_clause(pvar v, clause_ref lemma) {
        SASSERT(lemma);
        sat::literal lit = decide_bool(*lemma);
        SASSERT(lit != sat::null_literal);
        constraint* c = m_constraints.lookup(lit.var());
        push_cjust(v, c);
        add_lemma_clause(std::move(lemma));
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
            constraint* c = m_constraints.lookup(lit.var());
            tmp_assign _t(c, lit);
            SASSERT(!c->is_currently_true(*this));  // should not happen in a valid lemma
            return !c->is_currently_false(*this);
        };

        // constraint *choice = nullptr;
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

        if (num_choices == 0)
            // This case may happen when all undefined literals are false under the current variable assignment.
            // TODO: The question is whether such lemmas should be generated? Check test_monot() for such a case.
            set_conflict(lemma);
        else if (num_choices == 1)
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
        SASSERT(m_justification[v].is_decision());
        constraints just(m_cjust[v]);
        backjump(m_justification[v].level()-1);
        // Since decision "v -> val" caused a conflict, we may keep all
        // viability restrictions on v and additionally exclude val.
        // TODO: viability restrictions on 'v' must have happened before decision on 'v'. Do we really need to save/restore m_viable here?
        SASSERT(m_cjust[v] == just);  // check this with assertion

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
            if (!c->is_undef())  // TODO: this check to be removed once this is fixed properly.
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
    }
    
    void solver::revert_bool_decision(sat::literal lit, clause_ref reason) {
        sat::bool_var const var = lit.var();
        LOG_H3("Reverting boolean decision: " << lit);
        SASSERT(m_bvars.is_decision(var));

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
            bool contains_opp = std::any_of(reason->begin(), reason->end(), [lit](sat::literal reason_lit) { return reason_lit == ~lit; });
            SASSERT(contains_opp);
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
        add_lemma_clause(std::move(reason));
        propagate_bool(~lit, reason_cl);
        if (is_conflict()) {
            LOG_H1("Conflict during revert_bool_decision/propagate_bool!");
            return;
        }

        decide_bool(*lemma);
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
            constraint* c = m_constraints.lookup(lit.var());
            m_redundant.push_back(c);
            activate_constraint_base(c, !lit.sign());
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

        constraint* c = m_constraints.lookup(lit.var());
        SASSERT(c);
        bool is_true = !lit.sign();
        activate_constraint(*c, is_true);
    }

    /// Activate a constraint at the base level.
    /// Used for external unit constraints and unit consequences.
    void solver::activate_constraint_base(constraint* c, bool is_true) {
        SASSERT(c);
        // c must be in m_original or m_redundant so it can be deactivated properly when popping the base level
        SASSERT_EQ(std::count(m_original.begin(), m_original.end(), c) + std::count(m_redundant.begin(), m_redundant.end(), c), 1);
        sat::literal lit(c->bvar(), !is_true);
        assign_bool_core(lit, nullptr, nullptr);
        activate_constraint(*c, is_true);
    }

    /// Assign a boolean literal
    void solver::assign_bool_core(sat::literal lit, clause* reason, clause* lemma) {
        LOG("Assigning boolean literal: " << lit);
        m_bvars.assign(lit, m_level, reason, lemma);
    }

    /// Activate constraint immediately
    void solver::activate_constraint(constraint& c, bool is_true) {
        LOG("Activating constraint: " << c << " ; is_true = " << is_true);
        SASSERT(m_bvars.value(c.bvar()) == to_lbool(is_true));
        c.assign(is_true);
        add_watch(c);
        c.narrow(*this);
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.activate_constraint(c);
#endif
    }

    /// Deactivate constraint immediately
    void solver::deactivate_constraint(constraint& c) {
        LOG("Deactivating constraint: " << c);
        erase_watch(c);
        c.unassign();
#if ENABLE_LINEAR_SOLVER
        m_linear_solver.deactivate_constraint(c);  // TODO add this method to linear solver?
#endif
    }

    void solver::backjump(unsigned new_level) {
        LOG_H3("Backjumping to level " << new_level << " from level " << m_level);
        unsigned num_levels = m_level - new_level;
        if (num_levels > 0) 
            pop_levels(num_levels);        
    }
        
    /**
     * Return residue of superposing p and q with respect to v.
     */
    clause_ref solver::resolve(pvar v) {
        LOG_H3("Resolve v" << v);
        SASSERT(!m_cjust[v].empty());
        SASSERT(m_justification[v].is_propagation());
        LOG("Conflict: " << m_conflict);
        LOG("cjust[v" << v << "]: " << m_cjust[v]);

        conflict_explainer cx(*this, m_conflict);
        clause_ref res = cx.resolve(v, m_cjust[v]);
        LOG("resolved: " << show_deref(res));
        // SASSERT(false && "pause on explanation");
        return res;
    }

    /**
     * placeholder for factoring/gcd common factors
     */
    void solver::narrow(pvar v) {

    }

    // Add lemma to storage but do not activate it
    void solver::add_lemma_unit(constraint_ref lemma) {
        if (!lemma)
            return;
        LOG("Lemma: " << show_deref(lemma));
        constraint* c = m_constraints.store(std::move(lemma));
        insert_constraint(m_redundant, c);
        // TODO: create unit clause
    }

    // Add lemma to storage but do not activate it
    void solver::add_lemma_clause(clause_ref lemma) {
        if (!lemma)
            return;
        // TODO: check for unit clauses!
        LOG("Lemma: " << show_deref(lemma));
        if (lemma->size() < 2) {
            LOG_H1("TODO: this should be treated as unit constraint and asserted at the base level!");
        }
        // SASSERT(lemma->size() > 1);
        clause* cl = m_constraints.store(std::move(lemma));
        m_redundant_clauses.push_back(cl);
    }

    void solver::insert_constraint(ptr_vector<constraint>& cs, constraint* c) {
        cs.push_back(c);
        for (unsigned i = cs.size() - 1; i-- > 0; ) {
            auto* c1 = cs[i + 1];
            auto* c2 = cs[i];
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

    bool solver::active_at_base_level(sat::bool_var bvar) const {
        // NOTE: this active_at_base_level is actually not what we want!!!
        //          first of all, it might not really be a base level: could be a non-base level between previous base levels.
        //          in that case, how do we determine the right dependencies???
        //          secondly, we are interested in "unit clauses", not as much whether we assigned something on the base level...
        //          TODO: however, propagating stuff at the base level... need to be careful with dependencies there... might need to turn all base-level propagations into unit clauses...
        VERIFY(false);
        // bool res = m_bvars.is_assigned(bvar) && m_bvars.level(bvar) <= base_level();
        // SASSERT_EQ(res, !!m_constraints.lookup(bvar)->unit_clause());
        // return res;
    }

    bool solver::try_eval(pdd const& p, rational& out_value) const {
        pdd r = p.subst_val(assignment());
        if (r.is_val())
            out_value = r.val();
        return r.is_val();
    }

    std::ostream& solver::display(std::ostream& out) const {
        for (auto [v, val] : assignment()) {
            auto j = m_justification[v];
            out << assignment_pp(*this, v, val) << " @" << j.level();
            if (j.is_propagation())
                out << " " << m_cjust[v];
            out << "\n";
            // out << m_viable[v] << "\n";
        }
        out << "Original:\n";
        for (auto* c : m_original)
            out << "\t" << *c << "\n";
        out << "Redundant:\n";
        for (auto* c : m_redundant)
            out << "\t" << *c << "\n";
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
    bool solver::invariant(ptr_vector<constraint> const& cs) {
        unsigned sz = cs.size();
        for (unsigned i = 0; i + 1 < sz; ++i) 
            VERIFY(cs[i]->level() <= cs[i + 1]->level());
        return true;
    }

    /**
     * Check that two variables of each constraint are watched.
     */
    bool solver::wlist_invariant() {
        constraints cs;
        cs.append(m_original.size(), m_original.data());
        cs.append(m_redundant.size(), m_redundant.data());
        for (auto* c : cs) {
            if (c->is_undef())
                continue;
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
        for (auto* c : m_original) {
            bool ok = c->is_currently_true(*this);
            LOG((ok ? "PASS" : "FAIL") << ": " << show_deref(c));
            if (!ok) return false;
        }
        LOG("All good!");
        return true;
    }
}


