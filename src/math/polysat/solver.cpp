/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat

Abstract:

    Polynomial solver for modular arithmetic.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/

#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    
    dd::pdd_manager& solver::sz2pdd(unsigned sz) {
        m_pdd.reserve(sz + 1);
        if (!m_pdd[sz])
            m_pdd.set(sz, alloc(dd::pdd_manager, 1000, dd::pdd_manager::semantics::mod2N_e, sz));
        return *m_pdd[sz];
    }

    bool solver::is_viable(pvar v, rational const& val) {
        bdd b = m_viable[v];
        for (unsigned k = size(v); k-- > 0 && !b.is_false(); ) 
            b &= val.get_bit(k) ? m_bdd.mk_var(k) : m_bdd.mk_nvar(k);
        return !b.is_false();
    }

    void solver::add_non_viable(pvar v, rational const& val) {
        LOG("pvar " << v << " /= " << val);
        TRACE("polysat", tout << "v" << v << " /= " << val << "\n";);
        bdd value = m_bdd.mk_true();
        for (unsigned k = size(v); k-- > 0; ) 
            value &= val.get_bit(k) ? m_bdd.mk_var(k) : m_bdd.mk_nvar(k);
        SASSERT((value && !m_viable[v]).is_false());
        m_viable[v] &= !value;        
    }

    lbool solver::find_viable(pvar v, rational & val) {
        val = 0;
        bdd viable = m_viable[v];
        if (viable.is_false())
            return l_false;
        bool is_unique = true;
        unsigned num_vars = 0;
        while (!viable.is_true()) {
            ++num_vars;
            if (!viable.lo().is_false() && !viable.hi().is_false())
                is_unique = false;
            if (viable.lo().is_false()) {
                val += rational::power_of_two(viable.var());
                viable = viable.hi();
            }
            else 
                viable = viable.lo();
        }
        is_unique &= num_vars == size(v);
        TRACE("polysat", tout << "v" << v << " := " << val << " unique " << is_unique << "\n";);
        return is_unique ? l_true : l_undef;
    }

    struct solver::t_del_var : public trail {
        solver& s;
        t_del_var(solver& s): s(s) {}
        void undo() override { s.del_var(); }
    };
    
    solver::solver(trail_stack& s, reslimit& lim): 
        m_trail(s),
        m_lim(lim),
        m_bdd(1000),
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
    
    lbool solver::check_sat() { 
        TRACE("polysat", tout << "check\n";);
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

            if (is_conflict() && at_base_level()) { LOG_H2("UNSAT"); return l_false; }
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
        m_trail.push(t_del_var(*this));
        m_free_vars.mk_var_eh(v);
        return v;
    }

    void solver::del_var() {
        // TODO also remove v from all learned constraints.
        pvar v = m_viable.size() - 1;
        m_free_vars.del_var_eh(v);
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

    void solver::add_eq(pdd const& p, unsigned dep) {
        p_dependency_ref d(mk_dep(dep), m_dm);
        constraint* c = constraint::eq(m_level, p, d);
        LOG("Adding constraint: " << *c);
        m_constraints.push_back(c);
        add_watch(*c);
    }

    void solver::add_diseq(pdd const& p, unsigned dep) {
#if 0
        // Basically: 
        auto slack = add_var(p.size());
        p = p + var(slack);
        add_eq(p, dep);
        m_viable[slack] &= slack != 0;
#endif
    }

    void solver::add_ule(pdd const& p, pdd const& q, unsigned dep) {
        // save for later
    }

    void solver::add_sle(pdd const& p, pdd const& q, unsigned dep) {
        // save for later
    }

    void solver::add_ult(pdd const& p, pdd const& q, unsigned dep) {
        // save for later
    }

    void solver::add_slt(pdd const& p, pdd const& q, unsigned dep) {
        // save for later
    }


    bool solver::can_propagate() {
        return m_qhead < m_search.size() && !is_conflict();
    }

    void solver::propagate() {
        m_trail.push(value_trail(m_qhead));
        while (can_propagate()) 
            propagate(m_search[m_qhead++].first);
    }

    void solver::propagate(pvar v) {
        LOG_H2("Propagate pvar " << v);
        auto& wlist = m_watch[v];
        unsigned i = 0, j = 0, sz = wlist.size();
        for (; i < sz && !is_conflict(); ++i) 
            if (!propagate(v, *wlist[i]))
                wlist[j++] = wlist[i];
        for (; i < sz; ++i)
            wlist[j++] = wlist[i];
        wlist.shrink(j);
    }

    /**
     * Return true iff the constraint should be removed from the current watch list.
     */
    bool solver::propagate(pvar v, constraint& c) {
        switch (c.kind()) {
        case ckind_t::eq_t:
            return propagate_eq(v, c);
        case ckind_t::ule_t:
        case ckind_t::sle_t:
            NOT_IMPLEMENTED_YET();
            return false;
        }
        UNREACHABLE();
        return false;
    }

    bool solver::propagate_eq(pvar v, constraint& c) {
        LOG_H3("Propagate " << m_vars[v] << " in " << c);
        SASSERT(c.kind() == ckind_t::eq_t);
        SASSERT(!c.vars().empty());
        auto var = m_vars[v].var();
        auto& vars = c.vars();
        unsigned idx = 0;
        if (vars[idx] != v)
            idx = 1;
        SASSERT(v == vars[idx]);
        // find other watch variable.
        for (unsigned i = vars.size(); i-- > 2; ) {
            if (!is_assigned(vars[i])) {
                std::swap(vars[idx], vars[i]);
                return true;
            }
        }        
        

        LOG("Assignments: " << m_search);
        auto p = c.p().subst_val(m_search);
        LOG("Substituted: " << c.p() << " := " << p);
        TRACE("polysat", tout << c.p() << " := " << p << "\n";);
        if (p.is_zero()) 
            return false;
        if (p.is_never_zero()) {
            LOG("Conflict (never zero under current assignment)");
            // we could tag constraint to allow early substitution before 
            // swapping watch variable in case we can detect conflict earlier.
            set_conflict(c);
            return false;
        }

        // at most one variable remains unassigned.
        auto other_var = vars[1 - idx];
        // SASSERT(!is_assigned(other_var));

        // Detect and apply unit propagation.
            
        if (!p.is_linear())
            return false;

        // a*x + b == 0
        rational a = p.hi().val();
        rational b = p.lo().val();
        rational inv_a;
        if (a.is_odd()) {
            // v1 = -b * inverse(a)
            unsigned sz = p.power_of_2();
            VERIFY(a.mult_inverse(sz, inv_a)); 
            rational val = mod(inv_a * -b, rational::power_of_two(sz));
            m_cjust[other_var].push_back(&c);
            propagate(other_var, val, c);
            return false;
        }

        SASSERT(!b.is_odd());  // otherwise p.is_never_zero() would have been true above

        // TBD
        // constrain viable using condition on x
        // 2*x + 2 == 0 mod 4 => x is odd
        //
        // We have:
        // 2^j*a'*x + 2^j*b' == 0 mod m, where a' is odd (but not necessarily b')
        // <=> 2^j*(a'*x + b') == 0 mod m
        // <=> a'*x + b' == 0 mod (m-j)
        // <=> x == -b' * inverse_{m-j}(a') mod (m-j)
        // ( <=> 2^j*x == 2^j * -b' * inverse_{m-j}(a') mod m )
        //
        // x == c mod (m-j)
        // Which x in 2^m satisfy this?
        // => x \in { c + k * 2^(m-j) | k = 0, ..., 2^j - 1 }
        unsigned rank_a = a.trailing_zeros();  // j
        SASSERT(b == 0 || rank_a <= b.trailing_zeros());
        rational aa = a / rational::power_of_two(rank_a);  // a'
        rational bb = b / rational::power_of_two(rank_a);  // b'
        rational inv_aa;
        unsigned small_sz = p.power_of_2() - rank_a;  // m - j
        VERIFY(aa.mult_inverse(small_sz, inv_aa));
        rational cc = mod(inv_aa * -bb, rational::power_of_two(small_sz));
        LOG(m_vars[other_var] << " = " << cc << " + k * 2^" << small_sz);
        // Bit representation of the remaining values:
        //   k*2^(m-j) +         c'
        // ????????????000000000000000000000000   (0 = bits of cc; ? = any value)
        // |- rank_a -||---- small_sz bits ---|
        // |-------- p.power_of_2() ----------|
        // So we just force all lower bits in the bdd to be the same as in cc
        for (unsigned k = small_sz; k-- > 0; )
            m_viable[other_var] &= cc.get_bit(k) ? m_bdd.mk_var(k) : m_bdd.mk_nvar(k);
        // keep this for debugging, for now
        IF_LOGGING({
            vector<rational> viable;
            for (rational k = rational::zero(); k < rational::power_of_two(rank_a); k += 1) {
                rational val = cc + k * rational::power_of_two(small_sz);
                viable.push_back(val);
            }
            LOG_V("still viable: " << viable);
            log_viable(other_var);
        });
        m_cjust[other_var].push_back(&c);
        
        return false;
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
        m_trail.push_scope();
    }

    void solver::pop_levels(unsigned num_levels) {
        m_trail.pop_scope(num_levels);        
        m_level -= num_levels;
        pop_constraints(m_constraints);
        pop_constraints(m_redundant);
        pop_assignment();
    }

    void solver::pop_constraints(scoped_ptr_vector<constraint>& cs) {
        VERIFY(invariant(cs));
        while (!cs.empty() && cs.back()->level() > m_level) {
            erase_watch(*cs.back());
            cs.pop_back();
        }        
    }

    /**
     * TBD: rewrite for proper backtracking where variable levels don't follow scope level.
     * use a marker into m_search for level as in SAT solver.
     */
    void solver::pop_assignment() {
        while (!m_search.empty() && m_justification[m_search.back().first].level() > m_level) {
            undo_var(m_search.back().first);
            m_search.pop_back();
        }
    }

    // Base approach just clears all assignments.
    // TBD approach allows constraints to constrain bits of v. They are 
    // added to cjust and affect viable outside of search.
    void solver::undo_var(pvar v) {
        m_justification[v] = justification::unassigned();
        m_free_vars.unassign_var_eh(v);
        m_cjust[v].reset();
        m_viable[v] = m_bdd.mk_true(); 
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
        case l_false:
            LOG("Conflict: no value for pvar " << v);
            set_conflict(v);
            break;
        case l_true:
            LOG("Propagation: pvar " << v << " := " << val << " (due to unique value)");
            assign_core(v, val, justification::propagation(m_level));
            break;
        case l_undef:
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
        TRACE("polysat", tout << "v" << v << " := " << val << " " << j << "\n";);
        LOG("pvar " << v << " := " << val << " by " << j);
        SASSERT(is_viable(v, val));
        m_value[v] = val;
        m_search.push_back(std::make_pair(v, val));
        m_justification[v] = j; 
    }

    void solver::set_conflict(constraint& c) { 
        SASSERT(m_conflict.empty());
        TRACE("polysat", tout << "conflict " << c << "\n";);
        m_conflict.push_back(&c); 
    }

    void solver::set_conflict(pvar v) {
        SASSERT(m_conflict.empty());
        m_conflict.append(m_cjust[v]);
        TRACE("polysat", tout << "conflict "; for (auto* c : m_conflict) tout << *c << "\n";);
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
     * todos: replace accumulation of sub by something more incremental.
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

        scoped_ptr<constraint> lemma;
        reset_marks();
        for (constraint* c : m_conflict) {
            SASSERT(c);
            LOG("Conflicting: " << *c);
            for (auto v : c->vars()) 
                set_mark(v);
        }
        
        for (unsigned i = m_search.size(); i-- > 0; ) {
            pvar v = m_search[i].first;
            if (!is_marked(v))
                continue;
            justification& j = m_justification[v];
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
            if (is_always_false(*new_lemma)) {
                learn_lemma(v, new_lemma.get());
                m_conflict.reset();
                m_conflict.push_back(new_lemma.detach());
                report_unsat();
                return;
            }
            if (!eval_to_false(*new_lemma)) {
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
        m_cjust[v].push_back(c);        
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
        m_conflict.append(m_cjust[v]);
        backjump(m_justification[v].level()-1);
        SASSERT(m_cjust[v].empty());
        m_cjust[v].append(m_conflict);
        m_conflict.reset();
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
        if (m_conflict.size() > 1)
            return nullptr;
        if (m_cjust[v].size() > 1)
            return nullptr;
        constraint* c = m_conflict[0];
        constraint* d = m_cjust[v].back();
        if (c->is_eq() && d->is_eq()) {
            pdd p = c->p();
            pdd q = d->p();
            pdd r = p;
            if (!p.resolve(v, q, r)) 
                return nullptr;
            p_dependency_ref dep(m_dm);
            dep = m_dm.mk_join(c->dep(), d->dep());
            unsigned level = std::max(c->level(), d->level());
            return constraint::eq(level, r, dep);             
        }
        return nullptr;
    }

    /**
     * placeholder for factoring/gcd common factors
     */
    void solver::narrow(pvar v) {

    }


    bool solver::is_always_false(constraint& c) {
        if (c.is_eq()) 
            return c.p().is_never_zero();
        return false;
    }

    bool solver::eval_to_false(constraint& c) {
        if (c.is_eq()) {
            pdd r = c.p().subst_val(m_search);
            return r.is_never_zero();
        }
        return false;
    }

    void solver::add_lemma(constraint* c) {
        if (!c)
            return;
        LOG("Lemma: " << *c);
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
        push_level();
        m_base_levels.push_back(m_level);
    }

    void solver::pop(unsigned num_scopes) {
        unsigned base_level = m_base_levels[m_base_levels.size() - num_scopes];
        pop_levels(m_level - base_level - 1);
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


