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

    std::ostream& poly::display(std::ostream& out) const {
        return out;
    }

    std::ostream& constraint::display(std::ostream& out) const {
        return out;
    }
    
    std::ostream& linear::display(std::ostream& out) const {
        return out;
    }

    std::ostream& mono::display(std::ostream& out) const {
        return out;
    }

    unsigned solver::poly2size(poly const& p) const {
        return 0;
    }

    bool solver::is_viable(unsigned var, rational const& val) const {
        return false;
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
        m_region(s.get_region()),
        m_pdd(1000),
        m_bdd(1000),
        m_free_vars(m_activity) {
    }

    solver::~solver() {}
    
    lbool solver::check_sat() { 
        return l_undef;
    }
        
    unsigned solver::add_var(unsigned sz) {
        unsigned v = m_viable.size();
        // TODO: set var size sz into m_pdd.
        m_value.push_back(rational::zero());
        m_justification.push_back(justification::unassigned());
        m_viable.push_back(m_bdd.mk_true());
        m_vdeps.push_back(m_dep_manager.mk_empty());
        m_pdeps.push_back(vector<poly>());
        m_watch.push_back(unsigned_vector());
        m_activity.push_back(0);
        m_vars.push_back(m_pdd.mk_var(v));
        m_trail.push(del_var(*this));
        return v;
    }

    void solver::do_del_var() {
        unsigned v = m_viable.size() - 1;
        m_free_vars.del_var_eh(v);
        m_viable.pop_back();
        m_vdeps.pop_back();
        m_pdeps.pop_back();
        m_value.pop_back();
        m_justification.pop_back();
        m_watch.pop_back();
        m_activity.pop_back();
        m_vars.pop_back();
    }

    void solver::do_del_constraint() {
        // TODO remove variables from watch lists
        m_constraints.pop_back();
        m_cdeps.pop_back();
    }

    void solver::do_var_unassign() {

    }

    poly solver::var(unsigned v) {
        return poly(*this, m_vars[v]);
    }

    vector<mono> solver::poly2monos(poly const& p) const {
        return vector<mono>();
    }

    void solver::add_eq(poly const& p, unsigned dep) {
        m_constraints.push_back(constraint::eq(p));
        m_cdeps.push_back(m_dep_manager.mk_leaf(dep));
        // TODO init watch list
        m_trail.push(del_constraint(*this));
    }

    void solver::add_diseq(poly const& p, unsigned dep) {
#if 0
        // Basically: 
        auto slack = add_var(p.size());
        p = p + var(slack);
        add_eq(p, dep);
        m_viable[slack] &= slack != 0;
#endif
    }

    void solver::add_ule(poly const& p, poly const& q, unsigned dep) {
        // save for later
    }

    void solver::add_sle(poly const& p, poly const& q, unsigned dep) {
        // save for later
    }

    void solver::assign(unsigned var, unsigned index, bool value, unsigned dep) {

    }

    bool  solver::can_propagate() {
        return false;
    }

    lbool solver::propagate() {
        return l_false;
    }

    bool solver::can_decide() {
        return false;
    }

    void solver::decide(rational & val, unsigned& var) {

    }

    void solver::assign(unsigned var, rational const& val) {

    }
        
    bool solver::is_conflict() {
        return false;
    }

    unsigned resolve_conflict(unsigned_vector& deps) {
        return 0;
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


