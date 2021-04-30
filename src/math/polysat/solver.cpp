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
#include "math/polysat/log.h"
#include "math/polysat/fixplex_def.h"
#include "math/polysat/forbidden_intervals.h"

namespace polysat {

    
    dd::pdd_manager& solver::sz2pdd(unsigned sz) {
        m_pdd.reserve(sz + 1);
        if (!m_pdd[sz]) 
            m_pdd.set(sz, alloc(dd::pdd_manager, 1000, dd::pdd_manager::semantics::mod2N_e, sz));
        return *m_pdd[sz];
    }

    dd::fdd const& solver::sz2bits(unsigned sz) {
        m_bits.reserve(sz + 1);
        auto* bits = m_bits[sz];
        if (!bits) {
            m_bits.set(sz, alloc(dd::fdd, m_bdd, sz));
            bits = m_bits[sz];
        }
        return *bits;
    }

    bool solver::has_viable(pvar v) {
        return !m_viable[v].is_false();
    }

    bool solver::is_viable(pvar v, rational const& val) {
        return var2bits(v).contains(m_viable[v], val);
    }

    void solver::add_non_viable(pvar v, rational const& val) {
        LOG("pvar " << v << " /= " << val);
        TRACE("polysat", tout << "v" << v << " /= " << val << "\n";);
        SASSERT(is_viable(v, val));
        auto const& bits = var2bits(v);
        intersect_viable(v, bits.var() != val);
    }

    void solver::intersect_viable(pvar v, bdd vals) {
        push_viable(v);
        m_viable[v] &= vals;
        if (m_viable[v].is_false())
            set_conflict(v);
    }

    dd::find_t solver::find_viable(pvar v, rational & val) {
        return var2bits(v).find_hint(m_viable[v], m_value[v], val);
    }
    
    solver::solver(reslimit& lim): 
        m_lim(lim),
        m_bdd(1000),
        m_fixplex(m_lim),
        m_dm(m_value_manager, m_alloc),
        m_free_vars(m_activity) {
    }

    solver::~solver() {}

#if POLYSAT_LOGGING_ENABLED
    void solver::log_viable(pvar v) {
        if (size(v) <= 5) {
            vector<rational> xs;
            for (rational x = rational::zero(); x < rational::power_of_two(size(v)); x += 1) {
                if (is_viable(v, x)) {
                    xs.push_back(x);
                }
            }
            LOG("Viable for pvar " << v << ": " << xs);
        } else {
            LOG("Viable for pvar " << v << ": <range too big>");
        }
    }
#endif

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
            LOG_H1("Next solving loop iteration");
            LOG("Free variables: " << m_free_vars);
            LOG("Assignments:    " << m_search);
            LOG("Conflict:       " << m_conflict);
            IF_LOGGING({
                for (pvar v = 0; v < m_viable.size(); ++v) {
                    log_viable(v);
                }
            });

            if (pending_disjunctive_lemma()) { LOG_H2("UNDEF (handle lemma externally)"); return l_undef; }
            else if (is_conflict() && at_base_level()) { LOG_H2("UNSAT"); return l_false; }
            else if (is_conflict()) resolve_conflict();
            else if (can_propagate()) propagate();
            else if (!can_decide()) { LOG_H2("SAT"); return l_true; }
            else decide();
        }
        return l_undef;
    }
        
    unsigned solver::add_var(unsigned sz) {
        pvar v = m_viable.size();
        m_value.push_back(rational::zero());
        m_justification.push_back(justification::unassigned());
        m_viable.push_back(m_bdd.mk_true());
        m_cjust.push_back(constraints());
        m_watch.push_back(ptr_vector<constraint>());
        m_activity.push_back(0);
        m_vars.push_back(sz2pdd(sz).mk_var(v));
        m_size.push_back(sz);
        m_trail.push_back(trail_instr_t::add_var_i);
        m_free_vars.mk_var_eh(v);
        return v;
    }

    void solver::del_var() {
        // TODO also remove v from all learned constraints.
        pvar v = m_viable.size() - 1;
        m_viable.pop_back();
        m_cjust.pop_back();
        m_value.pop_back();
        m_justification.pop_back();
        m_watch.pop_back();
        m_activity.pop_back();
        m_vars.pop_back();
        m_size.pop_back();
        m_free_vars.del_var_eh(v);
    }

    void solver::new_constraint(constraint* c) {
        SASSERT(c);
        LOG("New constraint: " << *c);
        m_constraints.push_back(c);
        SASSERT(!get_bv2c(c->bvar()));
        insert_bv2c(c->bvar(), c);
    }

    bool_var solver::new_eq(pdd const& p, unsigned dep) {
        p_dependency_ref d(mk_dep(dep), m_dm);
        constraint* c = constraint::eq(m_level, m_next_bvar++, pos_t, p, d);
        new_constraint(c);
        return c->bvar();
    }

    bool_var solver::new_diseq(pdd const& p, unsigned dep) {
        // if (p.is_val()) {
        //     if (!p.is_zero())
        //         return;
        //     // set conflict.
        //     NOT_IMPLEMENTED_YET();   // TODO: not here, only when activated
        //     return;
        // }
        unsigned sz = size(p.var());
        auto slack = add_var(sz);
        auto q = p + var(slack);
        add_eq(q, dep);
        auto non_zero = sz2bits(sz).non_zero();
        p_dependency_ref d(mk_dep(dep), m_dm);        
        constraint* c = constraint::viable(m_level, m_next_bvar++, pos_t, slack, non_zero, d);
        new_constraint(c);
        return c->bvar();
    }

    bool_var solver::new_ule(pdd const& p, pdd const& q, unsigned dep, csign_t sign) {
        p_dependency_ref d(mk_dep(dep), m_dm);
        constraint* c = constraint::ule(m_level, m_next_bvar++, sign, p, q, d);
        new_constraint(c);
        return c->bvar();
    }

    bool_var solver::new_sle(pdd const& p, pdd const& q, unsigned dep, csign_t sign) {
        auto shift = rational::power_of_two(p.power_of_2() - 1);
        return new_ule(p + shift, q + shift, dep, sign);
    }

    bool_var solver::new_ult(pdd const& p, pdd const& q, unsigned dep) {
        return new_ule(q, p, dep, neg_t);
    }

    bool_var solver::new_slt(pdd const& p, pdd const& q, unsigned dep) {
        return new_sle(q, p, dep, neg_t);
    }

    void solver::add_eq(pdd const& p, unsigned dep) { assign_eh(new_eq(p, dep), true); }
    void solver::add_diseq(pdd const& p, unsigned dep) { assign_eh(new_diseq(p, dep), true); }
    void solver::add_ule(pdd const& p, pdd const& q, unsigned dep) { assign_eh(new_ule(p, q, dep), true); }
    void solver::add_ult(pdd const& p, pdd const& q, unsigned dep) { assign_eh(new_ult(p, q, dep), true); }
    void solver::add_sle(pdd const& p, pdd const& q, unsigned dep) { assign_eh(new_sle(p, q, dep), true); }
    void solver::add_slt(pdd const& p, pdd const& q, unsigned dep) { assign_eh(new_slt(p, q, dep), true); }

    void solver::assign_eh(bool_var v, bool is_true) {
        constraint* c = get_bv2c(v);
        if (!c) {
            LOG("WARN: there is no constraint for bool_var " << v);
            return;
        }
        c->assign_eh(is_true);
        add_watch(*c);
        m_assign_eh_history.push_back(v);
        m_trail.push_back(trail_instr_t::assign_eh_i);
        c->narrow(*this);
    }


    bool solver::can_propagate() {
        return m_qhead < m_search.size() && !is_conflict();
    }

    void solver::propagate() {
        push_qhead();
        while (can_propagate()) 
            propagate(m_search[m_qhead++].first);
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
        if (is_viable(v, val)) {
            m_free_vars.del_var_eh(v);
            assign_core(v, val, justification::propagation(m_level));        
        }
        else 
            set_conflict(c);
    }

    void solver::push_level() {
        ++m_level;
        m_trail.push_back(trail_instr_t::inc_level_i);
    }

    void solver::pop_levels(unsigned num_levels) {
        LOG("Pop " << num_levels << " levels; current level is " << m_level);
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
                auto p = m_viable_trail.back();
                m_viable[p.first] = p.second;
                m_viable_trail.pop_back();
                break;
            }
            case trail_instr_t::assign_i: {
                auto v = m_search.back().first;
                m_free_vars.unassign_var_eh(v);
                m_justification[v] = justification::unassigned();
                m_search.pop_back();
                break;
            }
            case trail_instr_t::just_i: {
                auto v = m_cjust_trail.back();
                m_cjust[v].pop_back();
                m_cjust_trail.pop_back();
                break;
            }
            case trail_instr_t::assign_eh_i: {
                auto bvar = m_assign_eh_history.back();
                constraint* c = get_bv2c(bvar);
                erase_watch(*c);
                c->unassign_eh();
                m_assign_eh_history.pop_back();
                break;
            }
            default:
                UNREACHABLE();
            }
            m_trail.pop_back();
        }
        pop_constraints(m_constraints);
        pop_constraints(m_redundant);
    }

    void solver::pop_constraints(scoped_ptr_vector<constraint>& cs) {
        VERIFY(invariant(cs));
        while (!cs.empty() && cs.back()->level() > m_level) {
            erase_watch(*cs.back());
            cs.pop_back();
        }        
    }

    void solver::add_watch(constraint& c) {
        auto const& vars = c.vars();
        if (vars.size() > 0) 
            m_watch[vars[0]].push_back(&c);
        if (vars.size() > 1) 
            m_watch[vars[1]].push_back(&c);
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
        IF_LOGGING(log_viable(v));
        rational val;
        switch (find_viable(v, val)) {
        case dd::find_t::empty:
            LOG("Conflict: no value for pvar " << v);
            set_conflict(v);
            break;
        case dd::find_t::singleton:
            LOG("Propagation: pvar " << v << " := " << val << " (due to unique value)");
            assign_core(v, val, justification::propagation(m_level));
            break;
        case dd::find_t::multiple:
            LOG("Decision: pvar " << v << " := " << val);
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
        LOG("pvar " << v << " := " << val << " by " << j);
        SASSERT(is_viable(v, val));
        m_value[v] = val;
        m_search.push_back(std::make_pair(v, val));
        m_trail.push_back(trail_instr_t::assign_i);
        m_justification[v] = j; 
    }

    void solver::set_conflict(constraint& c) { 
        LOG("conflict: " << c);
        SASSERT(m_conflict.empty());
        m_conflict.push_back(&c); 
    }

    void solver::set_conflict(pvar v) {
        SASSERT(m_conflict.empty());
        m_conflict.append(m_cjust[v]);
        LOG("conflict for pvar " << v << ": " << m_conflict);
        if (m_cjust[v].empty())
            m_conflict.push_back(nullptr);
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
        LOG_H2("Resolve conflict");
        ++m_stats.m_num_conflicts;

        SASSERT(!m_conflict.empty());

        if (m_conflict.size() == 1 && !m_conflict[0]) {
            report_unsat();
            return;
        }

        pvar conflict_var = null_var;
        scoped_ptr<constraint> lemma;
        reset_marks();
        for (constraint* c : m_conflict) 
            for (auto v : c->vars()) {
                set_mark(v);
                if (!has_viable(v)) {
                    SASSERT(conflict_var == null_var || conflict_var == v);  // at most one variable can be empty
                    conflict_var = v;
                }
            }

        if (conflict_var != null_var) {
            LOG_H2("Conflict due to empty viable set for pvar " << conflict_var);
            clause new_lemma;
            if (forbidden_intervals::explain(*this, m_conflict, conflict_var, new_lemma)) {
                LOG_H3("Learning disjunctive lemma");
                SASSERT(new_lemma.size() > 0);
                if (new_lemma.size() == 1) {
                    lemma = new_lemma.detach()[0];
                    // TODO: continue normally?
                } else {
                    SASSERT(m_disjunctive_lemma.empty());
                    reset_marks();
                    for (constraint* c : new_lemma) {
                        m_disjunctive_lemma.push_back(c->bvar());
                        insert_bv2c(c->bvar(), c);
                        for (auto v : c->vars())
                            set_mark(v);
                    }
                    m_redundant_clauses.push_back(std::move(new_lemma));
                    backtrack(m_search.size()-1, lemma);
                    SASSERT(pending_disjunctive_lemma());
                    m_conflict.reset();
                    return;
                }
            }
        }
        
        for (unsigned i = m_search.size(); i-- > 0; ) {
            pvar v = m_search[i].first;
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
                learn_lemma(v, lemma.detach());
                revert_decision(v);
                return;
            }
            SASSERT(j.is_propagation());
            scoped_ptr<constraint> new_lemma = resolve(v);
            if (!new_lemma) {
                backtrack(i, lemma);
                return;
            }
            if (new_lemma->is_always_false()) {
                learn_lemma(v, new_lemma.get());
                m_conflict.reset();
                m_conflict.push_back(new_lemma.detach());
                report_unsat();
                return;
            }
            if (!new_lemma->is_currently_false(*this)) {
                backtrack(i, lemma);
                return;
            }
            lemma = new_lemma.detach();
            reset_marks();
            for (auto w : lemma->vars())
                set_mark(w);
            m_conflict.reset();
            m_conflict.push_back(lemma.get());
        }
        report_unsat();
    }

    void solver::backtrack(unsigned i, scoped_ptr<constraint>& lemma) {
        add_lemma(lemma.detach());
        do {
            auto v = m_search[i].first;
            if (!is_marked(v))
                continue;
            justification& j = m_justification[v];
            if (j.level() <= base_level()) 
                break;
            if (j.is_decision()) {
                revert_decision(v);
                return;
            }
            // retrieve constraint used for propagation
            // add variables to COI
            SASSERT(j.is_propagation());
            for (auto* c : m_cjust[v]) {
                for (auto w : c->vars())
                    set_mark(w);
                m_conflict.push_back(c);
            }
        }
        while (i-- > 0);        
        report_unsat();
    }

    void solver::report_unsat() {
        backjump(base_level());
        SASSERT(!m_conflict.empty());
    }

    void solver::unsat_core(unsigned_vector& deps) {
        deps.reset();
        p_dependency_ref conflict_dep(m_dm);
        for (auto* c : m_conflict) {
            if (c)
                conflict_dep = m_dm.mk_join(c->dep(), conflict_dep);
        }
        m_dm.linearize(conflict_dep, deps);
    }

    /**
     * The polynomial p encodes an equality that the decision was infeasible.
     * The effect of this function is that the assignment to v is undone and replaced 
     * by a new decision or unit propagation or conflict.
     * We add 'p == 0' as a lemma. The lemma depends on the dependencies used
     * to derive p, and the level of the lemma is the maximal level of the dependencies.
     */
    void solver::learn_lemma(pvar v, constraint* c) {
        if (!c)
            return;
        SASSERT(m_conflict_level <= m_justification[v].level());
        push_cjust(v, c);
        add_lemma(c);
    }

    /**
     * variable v was assigned by a decision at position i in the search stack.
     * TODO: we could resolve constraints in cjust[v] against each other to 
     * obtain stronger propagation. Example:
     *  (x + 1)*P = 0 and (x + 1)*Q = 0, where gcd(P,Q) = 1, then we have x + 1 = 0.
     * We refer to this process as narrowing.
     * In general form it can rely on factoring.
     * Root finding can further prune viable.
     */
    void solver::revert_decision(pvar v) {
        rational val = m_value[v];
        SASSERT(m_justification[v].is_decision());
        bdd viable = m_viable[v];
        constraints just(m_cjust[v]);
        backjump(m_justification[v].level()-1);
        for (unsigned i = m_cjust[v].size(); i < just.size(); ++i) 
            push_cjust(v, just[i]);
        for (constraint* c : m_conflict) {
            push_cjust(v, c);
            c->narrow(*this);
        }
        m_conflict.reset();
        push_viable(v);
        m_viable[v] = viable;
        add_non_viable(v, val);
        m_free_vars.del_var_eh(v);
        narrow(v);
        decide(v);
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
    constraint* solver::resolve(pvar v) {
        SASSERT(!m_cjust[v].empty());
        SASSERT(m_justification[v].is_propagation());
        if (m_cjust[v].size() != 1)
            return nullptr;
        constraint* d = m_cjust[v].back();
        return d->resolve(*this, v);
    }

    /**
     * placeholder for factoring/gcd common factors
     */
    void solver::narrow(pvar v) {

    }

    void solver::add_lemma(constraint* c) {
        if (!c)
            return;
        LOG("Lemma: " << *c);
        SASSERT(!get_bv2c(c->bvar()));
        insert_bv2c(c->bvar(), c);
        add_watch(*c);
        m_redundant.push_back(c);
        for (unsigned i = m_redundant.size() - 1; i-- > 0; ) {
            auto* c1 = m_redundant[i + 1];
            auto* c2 = m_redundant[i];
            if (c1->level() >= c2->level())
                break;
            m_redundant.swap(i, i + 1);
        }
        SASSERT(invariant(m_redundant)); 
    }
    
    void solver::reset_marks() {
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
    }

    bool solver::at_base_level() const {
        return m_level == base_level();
    }
    
    unsigned solver::base_level() const {
        return m_base_levels.empty() ? 0 : m_base_levels.back();
    }
        
    std::ostream& solver::display(std::ostream& out) const {
        for (auto p : m_search) {
            auto v = p.first;
            auto lvl = m_justification[v].level();
            out << "v" << v << " := " << p.second << " @" << lvl << "\n";
            out << m_viable[v] << "\n";
        }
        for (auto* c : m_constraints)
            out << *c << "\n";
        for (auto* c : m_redundant)
            out << *c << "\n";
        return out;
    }

    void solver::collect_statistics(statistics& st) const {
        st.update("polysat decisions",    m_stats.m_num_decisions);
        st.update("polysat conflicts",    m_stats.m_num_conflicts);
        st.update("polysat propagations", m_stats.m_num_propagations);
    }

    bool solver::invariant() {
        invariant(m_constraints);
        invariant(m_redundant);
        return true;
    }

    /**
     * constraints are sorted by levels so they can be removed when levels are popped.
     */
    bool solver::invariant(scoped_ptr_vector<constraint> const& cs) {
        unsigned sz = cs.size();
        for (unsigned i = 0; i + 1 < sz; ++i) 
            VERIFY(cs[i]->level() <= cs[i + 1]->level());
        return true;
    }

}


