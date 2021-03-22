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
        return out << "constraint";
    }
    
    std::ostream& linear::display(std::ostream& out) const {
        return out << "linear";
    }

    std::ostream& mono::display(std::ostream& out) const {
        return out << "mono";
    }

    dd::pdd_manager& solver::sz2pdd(unsigned sz) {
        m_pdd.reserve(sz + 1);
        if (!m_pdd[sz])
            m_pdd.set(sz, alloc(dd::pdd_manager, 1000));
        return *m_pdd[sz];
    }

    bool solver::is_viable(unsigned var, rational const& val) {
        bdd b = m_viable[var];
        for (unsigned k = size(var); k-- > 0 && !b.is_false(); ) 
            b &= val.get_bit(k) ? m_bdd.mk_var(k) : m_bdd.mk_nvar(k);
        return !b.is_false();
    }

    struct solver::del_var : public trail {
        solver& s;
        del_var(solver& s): s(s) {}
        void undo() override { s.do_del_var(); }
    };

    struct solver::del_constraint : public trail {
        solver& s;
        del_constraint(solver& s): s(s) {}
        void undo() override { s.do_del_constraint(); }
    };

    struct solver::var_unassign : public trail {
        solver& s;
        var_unassign(solver& s): s(s) {}
        void undo() override { s.do_var_unassign(); }
    };

    
    solver::solver(trail_stack& s): 
        m_trail(s),
        m_bdd(1000),
        m_free_vars(m_activity) {
    }

    solver::~solver() {}
    
    lbool solver::check_sat() { 
        return l_undef;
    }
        
    unsigned solver::add_var(unsigned sz) {
        unsigned v = m_viable.size();
        m_value.push_back(rational::zero());
        m_justification.push_back(justification::unassigned());
        m_viable.push_back(m_bdd.mk_true());
        m_vdeps.push_back(m_dep_manager.mk_empty());
        m_cjust.push_back(constraints());
        m_watch.push_back(ptr_vector<constraint>());
        m_activity.push_back(0);
        m_vars.push_back(sz2pdd(sz).mk_var(v));
        m_size.push_back(sz);
        m_trail.push(del_var(*this));
        return v;
    }

    void solver::do_del_var() {
        // TODO also remove v from all learned constraints.
        unsigned v = m_viable.size() - 1;
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

    void solver::do_del_constraint() {
        // TODO rewrite to allow for learned constraints
        // so have to gc these.
        constraint& c = *m_constraints.back();
        if (c.vars().size() > 0)
            erase_watch(c.vars()[0], c);
        if (c.vars().size() > 1)
            erase_watch(c.vars()[1], c);
        m_constraints.pop_back();
    }

    void solver::do_var_unassign() {
        unsigned v = m_search.back();
        m_justification[v] = justification::unassigned();
        m_free_vars.unassign_var_eh(v);
    }

    void solver::add_eq(pdd const& p, unsigned dep) {
        //
        // TODO reduce p using assignment (at current level, 
        // assuming constraint is removed also at current level).
        // 
        constraint* c = constraint::eq(p, m_dep_manager.mk_leaf(dep));
        m_constraints.push_back(c);
        auto const& vars = c->vars();
        if (vars.size() > 0) 
            m_watch[vars[0]].push_back(c);
        if (vars.size() > 1) 
            m_watch[vars[1]].push_back(c);
        m_trail.push(del_constraint(*this));
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

    void solver::assign(unsigned var, unsigned index, bool value, unsigned dep) {
        m_viable[var] &= value ? m_bdd.mk_var(index) : m_bdd.mk_nvar(index);
        m_trail.push(vector_value_trail<u_dependency*, false>(m_vdeps, var));
        m_vdeps[var] = m_dep_manager.mk_join(m_vdeps[var], m_dep_manager.mk_leaf(dep));
        if (m_viable[var].is_false()) {
            // TBD: set conflict
        }
    }

    bool solver::can_propagate() {
        return m_qhead < m_search.size() && !is_conflict();
    }

    void solver::propagate() {
        m_trail.push(value_trail(m_qhead));
        while (can_propagate()) 
            propagate(m_search[m_qhead++]);
    }

    void solver::propagate(unsigned v) {
        auto& wlist = m_watch[v];
        unsigned i = 0, j = 0, sz = wlist.size();
        for (; i < sz && !is_conflict(); ++i) 
            if (!propagate(v, *wlist[i]))
                wlist[j++] = wlist[i];
        for (; i < sz; ++i)
            wlist[j++] = wlist[i];
        wlist.shrink(j);
    }

    bool solver::propagate(unsigned v, constraint& c) {
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

    bool solver::propagate_eq(unsigned v, constraint& c) {
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

        vector<std::pair<unsigned, rational>> sub;
        for (auto w : vars) 
            if (is_assigned(w))
                sub.push_back(std::make_pair(w, m_value[w]));

        auto p = c.p().subst_val(sub);
        if (p.is_zero()) 
            return false;
        if (p.is_non_zero()) {
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
            m_trail.push(push_back_vector(m_cjust[other_var]));
            propagate(other_var, val, justification::propagation(m_level));
            return false;
        }

        // TBD
        // constrain viable using condition on x
        // 2*x + 2 == 0 mod 4 => x is odd
        
        return false;
    }

    void solver::propagate(unsigned var, rational const& val, justification const& j) {
        SASSERT(j.is_propagation());
        if (is_viable(var, val)) 
            assign_core(var, val, j);        
        else 
            set_conflict(*m_cjust[var].back());
}

    void solver::inc_level() {
        m_trail.push(value_trail(m_level));
        ++m_level;
    }

    void solver::erase_watch(unsigned v, constraint& c) {
        if (v == UINT_MAX)
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

    void solver::decide(rational & val, unsigned& var) {
        SASSERT(can_decide());
        inc_level();
        var = m_free_vars.next_var();
        auto viable = m_viable[var];
        SASSERT(!viable.is_false());
        // TBD, choose some value from viable and construct val.
        assign_core(var, val, justification::decision(m_level));
    }

    void solver::assign_core(unsigned var, rational const& val, justification const& j) {
        SASSERT(is_viable(var, val));
        m_trail.push(var_unassign(*this));
        m_search.push_back(var);
        m_value[var] = val;
        m_justification[var] = j; 
    }
        
    /**
     * Conflict resolution.
     * - m_conflict is a constraint infeasible in the current assignment.
     * 1. walk m_search from top down until last variable in m_conflict.
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
     */
    unsigned solver::resolve_conflict(unsigned_vector& deps) {
        SASSERT(m_conflict);
        constraint& c = *m_conflict;
        m_conflict = nullptr;
        pdd p = c.p();
        reset_marks();
        for (auto v : c.vars())
            set_mark(v);
        unsigned v = UINT_MAX;
        unsigned i = m_search.size();
        vector<std::pair<unsigned, rational>> sub;
        for (auto w : m_search) 
            sub.push_back(std::make_pair(w, m_value[w]));

        for (; i-- > 0; ) {
            v = m_search[i];
            if (!is_marked(v))
                continue;
            pdd q = isolate(v);
            pdd r = resolve(v, q, p);
            pdd rval = r.subst_val(sub);
            if (!rval.is_non_zero())
                goto backtrack;
            if (r.is_val()) {
                SASSERT(!r.is_zero());
                // TBD: UNSAT, set conflict
                return 0;
            }
            justification& j = m_justification[v];
            if (j.is_decision()) {
                // TBD: revert value and add constraint
                // propagate if new value is given uniquely
                // set conflict if viable set is empty
                // adding r and reverting last decision.
                break;
            }
            SASSERT(j.is_propagation());
            for (auto w : r.free_vars())
                set_mark(w);
            p = r;
        }
        UNREACHABLE();
        
    backtrack:
        do {
            v = m_search[i];
            justification& j = m_justification[v];
            if (j.is_decision()) {
                // TBD: flip last decision.
            }
        }
        while (i-- > 0);
        
        return 0;
    }
    
    /**
     * resolve polynomials associated with unit propagating on v
     * producing polynomial that isolates v to lowest degree
     * and lowest power of 2.     
     */
    pdd solver::isolate(unsigned v) {
        if (m_cjust[v].empty()) 
            return sz2pdd(m_size[v]).zero();
        pdd p = m_cjust[v][0]->p();
        for (unsigned i = m_cjust[v].size(); i-- > 1; ) {
            // TBD reduce with respect to v
        }
        return p;
    }
    
    /**
     * Return residue of superposing p and q with respect to v.
     */
    pdd solver::resolve(unsigned v, pdd const& p, pdd const& q) {
        // TBD remove as much trace of v as possible.
        return p;
    }
    
    void solver::reset_marks() {
        m_marks.reserve(m_vars.size());
        m_clock++;
        if (m_clock != 0)
            return;
        m_clock++;
        m_marks.fill(0);        
    }
        
    bool solver::can_learn() {
        return false;
    }

    void solver::learn(constraint& c, unsigned_vector& deps) {

    } 

    void solver::learn(vector<constraint>& cs, unsigned_vector& deps) {

    }

    std::ostream& solver::display(std::ostream& out) const {
        return out;
    }


}


