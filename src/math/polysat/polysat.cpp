/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat

Abstract:

    Polynomial solver for modular arithmetic.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/

#include "math/polysat/polysat.h"

namespace polysat {

    std::ostream& constraint::display(std::ostream& out) const {
        switch (kind()) {
        case ckind_t::eq_t:
            return out << p() << " == 0";
        case ckind_t::ule_t:
            return out << lhs() << " <=u " << rhs();
        case ckind_t::sle_t:
            return out << lhs() << " <=s " << rhs();
        }
        return out;
    }
    
    dd::pdd_manager& solver::sz2pdd(unsigned sz) {
        m_pdd.reserve(sz + 1);
        if (!m_pdd[sz])
            m_pdd.set(sz, alloc(dd::pdd_manager, 1000));
        return *m_pdd[sz];
    }

    bool solver::is_viable(pvar v, rational const& val) {
        bdd b = m_viable[v];
        for (unsigned k = size(v); k-- > 0 && !b.is_false(); ) 
            b &= val.get_bit(k) ? m_bdd.mk_var(k) : m_bdd.mk_nvar(k);
        return !b.is_false();
    }

    void solver::add_non_viable(pvar v, rational const& val) {
        bdd value = m_bdd.mk_true();
        for (unsigned k = size(v); k-- > 0; ) 
            value &= val.get_bit(k) ? m_bdd.mk_var(k) : m_bdd.mk_nvar(k);
        m_viable[v] &= !value;        
    }

    lbool solver::find_viable(pvar v, rational & val) {
        val = 0;
        bdd viable = m_viable[v];
        if (viable.is_false())
            return l_false;
        unsigned num_vars = 0;
        while (!viable.is_true()) {
            unsigned k = viable.var();
            if (viable.lo().is_false()) {
                val += rational::power_of_two(k);
                viable = viable.hi();
            }
            else 
                viable = viable.lo();
            ++num_vars;
        }
        if (num_vars == size(v))
            return l_true;
        return l_undef;
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
        m_vdeps(m_dm),
        m_conflict_dep(nullptr, m_dm),
        m_stash_dep(nullptr, m_dm),
        m_free_vars(m_activity) {
    }

    solver::~solver() {}
    
    lbool solver::check_sat() { 
        while (m_lim.inc()) {
            if (is_conflict() && at_base_level()) return l_false;
            else if (is_conflict()) resolve_conflict();
            else if (can_propagate()) propagate();
            else if (!can_decide()) return l_true;
            else decide();
        }
        return l_undef;
    }
        
    unsigned solver::add_var(unsigned sz) {
        pvar v = m_viable.size();
        m_value.push_back(rational::zero());
        m_justification.push_back(justification::unassigned());
        m_viable.push_back(m_bdd.mk_true());
        m_vdeps.push_back(m_dm.mk_empty());
        m_cjust.push_back(constraints());
        m_watch.push_back(ptr_vector<constraint>());
        m_activity.push_back(0);
        m_vars.push_back(sz2pdd(sz).mk_var(v));
        m_size.push_back(sz);
        m_trail.push(t_del_var(*this));
        return v;
    }

    void solver::del_var() {
        // TODO also remove v from all learned constraints.
        pvar v = m_viable.size() - 1;
        m_free_vars.del_var_eh(v);
        m_viable.pop_back();
        m_vdeps.pop_back();
        m_cjust.pop_back();
        m_value.pop_back();
        m_justification.pop_back();
        m_watch.pop_back();
        m_activity.pop_back();
        m_vars.pop_back();
        m_size.pop_back();
    }

    void solver::add_eq(pdd const& p, unsigned dep) {
        p_dependency_ref d(mk_dep(dep), m_dm);
        constraint* c = constraint::eq(m_level, p, d);
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

    void solver::assign(pvar v, unsigned index, bool value, unsigned dep) {
        m_viable[v] &= value ? m_bdd.mk_var(index) : m_bdd.mk_nvar(index);
        add_viable_dep(v, mk_dep(dep));
        if (m_viable[v].is_false()) {
            // TBD: set conflict
        }
    }

    void solver::add_viable_dep(pvar v, p_dependency* dep) {
        if (dep)
            m_vdeps[v] = m_dm.mk_join(m_vdeps.get(v), dep);
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
        auto& wlist = m_watch[v];
        unsigned i = 0, j = 0, sz = wlist.size();
        for (; i < sz && !is_conflict(); ++i) 
            if (!propagate(v, *wlist[i]))
                wlist[j++] = wlist[i];
        for (; i < sz; ++i)
            wlist[j++] = wlist[i];
        wlist.shrink(j);
    }

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


        auto p = c.p().subst_val(m_search);
        if (p.is_zero()) 
            return false;
        if (p.is_never_zero()) {
            // we could tag constraint to allow early substitution before 
            // swapping watch variable in case we can detect conflict earlier.
            set_conflict(c);
            return false;
        }

        // one variable remains unassigned.
        auto other_var = vars[1 - idx];
        SASSERT(!is_assigned(other_var));

        // Detect and apply unit propagation.
            
        if (!p.is_linear())
            return false;

        // a*x + b == 0
        rational a = p.hi().val();
        rational b = p.lo().val();
        rational inv_a;
        if (p.lo().val().is_odd()) {
            // v1 = -b * inverse(a)
            unsigned sz = p.power_of_2();
            VERIFY(a.mult_inverse(sz, inv_a)); 
            rational val = mod(inv_a * -b, rational::power_of_two(sz));
            m_cjust[other_var].push_back(&c);
            propagate(other_var, val, c);
            return false;
        }

        // TBD
        // constrain viable using condition on x
        // 2*x + 2 == 0 mod 4 => x is odd
        
        return false;
    }

    void solver::propagate(pvar v, rational const& val, constraint& c) {
        if (is_viable(v, val)) 
            assign_core(v, val, justification::propagation(m_level));        
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
    
    void solver::undo_var(pvar v) {
        m_justification[v] = justification::unassigned();
        m_free_vars.unassign_var_eh(v);
        m_cjust[v].reset();
        m_vdeps[v] = nullptr;
        m_viable[v] = m_bdd.mk_true(); // TBD does not work with external bit-assignments
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
        SASSERT(can_decide());
        decide(m_free_vars.next_var());
    }

    void solver::decide(pvar v) {
        rational val;
        switch (find_viable(v, val)) {
        case l_false:
            set_conflict(v);
            break;
        case l_true:
            assign_core(v, val, justification::propagation(m_level));
            break;
        case l_undef:
            push_level();
            assign_core(v, val, justification::decision(m_level));
            break;
        }
    }

    void solver::assign_core(pvar v, rational const& val, justification const& j) {
        SASSERT(is_viable(v, val));
        m_value[v] = val;
        m_search.push_back(std::make_pair(v, val));
        m_justification[v] = j; 
    }

    void solver::set_conflict(constraint& c) { 
        SASSERT(m_conflict_cs.empty());
        m_conflict_cs.push_back(&c); 
        m_conflict_dep = nullptr;
    }

    void solver::set_conflict(pvar v) {
        SASSERT(m_conflict_cs.empty());
        m_conflict_cs.append(m_cjust[v]);
        m_conflict_dep = m_vdeps.get(v);
        if (m_cjust[v].empty())
            m_conflict_cs.push_back(nullptr);
    }

        
    /**
     * Conflict resolution.
     * - m_conflict_cs are constraints that are infeasible in the current assignment.
     * - m_conflict_dep are dependencies for infeasibility
     * 1. walk m_search from top down until last variable in m_conflict_cs.
     * 2. resolve constraints in m_cjust to isolate lowest degree polynomials
     *    using variable.
     *    Use Olm-Seidl division by powers of 2 to preserve invertibility.
     * 3. resolve conflict with result of resolution.
     * 4. If the resulting equality is still infeasible continue, otherwise bail out
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

        vector<pdd> ps = init_conflict();

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
                if (ps.size() == 1)
                    learn_lemma(v, ps[0]);
                revert_decision(i);
                return;
            }
            pdd r = resolve(v, ps);
            pdd rval = r.subst_val(m_search);
            if (r.is_val() && rval.is_never_zero()) {
                report_unsat();
                return;
            }
            if (!rval.is_never_zero()) {
                backtrack(i);
                return;
            }
            SASSERT(j.is_propagation());
            reset_marks();
            for (auto w : r.free_vars())
                set_mark(w);
            ps.shrink(1);
            ps[0] = r;
        }
        report_unsat();
    }

    vector<pdd> solver::init_conflict() {
        SASSERT(!m_conflict_cs.empty());
        m_conflict_level = 0;
        vector<pdd> ps;
        reset_marks();
        for (auto* c : m_conflict_cs) {
            if (!c)
                continue;
            for (auto v : c->vars())
                set_mark(v);
            ps.push_back(c->p());
            m_conflict_level = std::max(m_conflict_level, c->level());        
            m_conflict_dep = m_dm.mk_join(m_conflict_dep, c->dep());
        }
        m_conflict_cs.reset();
        return ps;
    }

    void solver::backtrack(unsigned i) {
        do {
            auto v = m_search[i].first;
            justification& j = m_justification[v];
            if (j.level() <= base_level()) 
                break;
            if (j.is_decision()) {
                revert_decision(i);
                return;
            }
        }
        while (i-- > 0);        
        report_unsat();
    }

    void solver::report_unsat() {
        backjump(base_level());
        SASSERT(m_conflict_cs.empty());
        m_conflict_cs.push_back(nullptr);
    }

    void solver::unsat_core(unsigned_vector& deps) {
        deps.reset();
        for (auto* c : m_conflict_cs) {
            if (c)
                m_conflict_dep = m_dm.mk_join(c->dep(), m_conflict_dep);
        }
        m_dm.linearize(m_conflict_dep, deps);
    }


    /**
     * The polynomial p encodes an equality that the decision was infeasible.
     * The effect of this function is that the assignment to v is undone and replaced 
     * by a new decision or unit propagation or conflict.
     * We add 'p == 0' as a lemma. The lemma depends on the dependencies used
     * to derive p, and the level of the lemma is the maximal level of the dependencies.
     */
    void solver::learn_lemma(pvar v, pdd const& p) {
        SASSERT(m_conflict_level <= m_justification[v].level());
        constraint* c = constraint::eq(m_conflict_level, p, m_conflict_dep);
        m_cjust[v].push_back(c);        
        add_lemma(c);
    }

    /**
     * variable v was assigned by a decision at position i in the search stack.
     */
    void solver::revert_decision(unsigned i) {
        auto v = m_search[i].first;
        SASSERT(m_justification[v].is_decision());
        stash_deps(v);
        backjump(m_justification[v].level()-1);
        unstash_deps(v);
        add_non_viable(v, m_value[v]);
        add_viable_dep(v, m_conflict_dep);
        decide(v);
    }

    void solver::stash_deps(pvar v) {
        m_stash_dep = m_vdeps.get(v);
        std::swap(m_stash_just, m_cjust[v]);
    }

    void solver::unstash_deps(pvar v) {
        m_vdeps[v] = m_stash_dep;
        std::swap(m_stash_just, m_cjust[v]);
    }
    
    void solver::backjump(unsigned new_level) {
        unsigned num_levels = m_level - new_level;
        if (num_levels > 0) 
            pop_levels(num_levels);        
    }
    
    /**
     * resolve polynomials associated with unit propagating on v
     * producing polynomial that isolates v to lowest degree
     * and lowest power of 2.     
     */
    pdd solver::isolate(pvar v, vector<pdd> const& ps) {
        pdd p = ps[0];
        for (unsigned i = ps.size(); i-- > 1; ) {
            // TBD reduce with respect to v
        }
        return p;
    }
    
    /**
     * Return residue of superposing p and q with respect to v.
     */
    pdd solver::resolve(pvar v, vector<pdd> const& ps) {
        auto const& cs = m_cjust[v];
        pdd r = isolate(v, ps);
        auto degree = r.degree(v);
        m_conflict_dep = m_dm.mk_join(m_conflict_dep, m_vdeps.get(v));
        while (degree > 0) {
            for (auto * c : cs) {
                if (degree >= c->p().degree(v)) {
                    // TODO binary resolve, update r using result
                    // add parity condition to presere falsification
                    degree = r.degree(v);
                    m_conflict_level = std::max(m_conflict_level, c->level());
                    m_conflict_dep = m_dm.mk_join(m_conflict_dep.get(), c->dep());
                }
            }
        }
        return r;
    }

    void solver::add_lemma(constraint* c) {
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
            out << "v" << p.first << " := " << p.second << "\n";
            out << m_viable[p.first] << "\n";
        }
        for (auto* c : m_constraints)
            out << *c << "\n";
        for (auto* c : m_redundant)
            out << *c << "\n";
        return out;
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


