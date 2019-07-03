#include "math/lp/nla_core.h"
#include "math/interval/interval_def.h"
#include "math/lp/nla_intervals.h"
#include "util/mpq.h"

namespace nla {
/*
// create a product of interval signs together with the depencies
intervals::interval intervals::mul_signs_with_deps(const svector<lpvar>& vars) const {
    interval a, b, c;
    m_imanager.set(a, mpq(1));
    for (lpvar v : vars) {
        set_var_interval_signs_with_deps(v, b);
        interval_deps deps;
        m_imanager.mul(a, b, c, deps);
        m_imanager.set(a, c);
        m_config.add_deps(a, b, deps, a);
        if (m_imanager.is_zero(a))
            return a;
    }
    return a;    
}

rational sign(const rational& v) { return v.is_zero()? v : (rational(v.is_pos()? 1 : -1)); }

void intervals::set_var_interval_signs(lpvar v, interval& b) const {
    lp::constraint_index ci;
    rational val;
    bool is_strict;
    if (ls().has_lower_bound(v, ci, val, is_strict)) {            
        m_config.set_lower(b, sign(val));
        m_config.set_lower_is_open(b, is_strict);
        m_config.set_lower_is_inf(b, false);
    }
    else {
        m_config.set_lower_is_open(b, true);
        m_config.set_lower_is_inf(b, true);
    }
    if (ls().has_upper_bound(v, ci, val, is_strict)) {
        m_config.set_upper(b, sign(val));
        m_config.set_upper_is_open(b, is_strict);
        m_config.set_upper_is_inf(b, false);
    }
    else {
        m_config.set_upper_is_open(b, true);
        m_config.set_upper_is_inf(b, true);
    }
}
*/
void intervals::set_var_interval_with_deps(lpvar v, interval& b) {
    lp::constraint_index ci;
    rational val;
    bool is_strict;
    if (ls().has_lower_bound(v, ci, val, is_strict)) {            
        m_config.set_lower(b, val);
        m_config.set_lower_is_open(b, is_strict);
        m_config.set_lower_is_inf(b, false);
        b.m_lower_dep = mk_dep(ci);
    }
    else {
        m_config.set_lower_is_open(b, true);
        m_config.set_lower_is_inf(b, true);
        b.m_lower_dep = nullptr;
    }
    if (ls().has_upper_bound(v, ci, val, is_strict)) {
        m_config.set_upper(b, val);
        m_config.set_upper_is_open(b, is_strict);
        m_config.set_upper_is_inf(b, false);
        b.m_upper_dep = mk_dep(ci);
    }
    else {
        m_config.set_upper_is_open(b, true);
        m_config.set_upper_is_inf(b, true);
        b.m_upper_dep = nullptr;
    }
}

void intervals::check_interval_for_conflict_on_zero(const interval & i) {
    if (check_interval_for_conflict_on_zero_lower(i))
        return;
    check_interval_for_conflict_on_zero_upper(i);    
}

bool intervals::check_interval_for_conflict_on_zero_upper(const interval & i) {
    if (upper_is_inf(i))
        return false;
    if (unsynch_mpq_manager::is_pos(upper(i)))
        return false;
    if (unsynch_mpq_manager::is_zero(upper(i)) && !m_config.upper_is_open(i))
        return false;
     add_empty_lemma();
     svector<lp::constraint_index> expl;
     m_dep_manager.linearize(i.m_upper_dep, expl); 
     _().current_expl().add_expl(expl);
     return true;
}

bool intervals::check_interval_for_conflict_on_zero_lower(const interval & i) {
    if (lower_is_inf(i))
        return false;
    if (unsynch_mpq_manager::is_pos(lower(i)))
        return false;
    if (unsynch_mpq_manager::is_zero(lower(i)) && !m_config.lower_is_open(i))
        return false;
     add_empty_lemma();
     svector<lp::constraint_index> expl;
     m_dep_manager.linearize(i.m_lower_dep, expl); 
     _().current_expl().add_expl(expl);
     return true;
}

intervals::ci_dependency *intervals::mk_dep(lp::constraint_index ci) const {
    return m_dep_manager.mk_leaf(ci);
}
    

std::ostream& intervals::display(std::ostream& out, const interval& i) const {
    if (m_imanager.lower_is_inf(i)) {
        out << "(-oo";
    } else {
        out << (m_imanager.lower_is_open(i)? "(":"[") << rational(m_imanager.lower(i));        
    }
    out << ",";
    if (m_imanager.upper_is_inf(i)) {
        out << "oo)";
    } else {
        out << rational(m_imanager.upper(i)) << (m_imanager.lower_is_open(i)? ")":"]");         
    }
    return out;
}

lp::lar_solver& intervals::ls() { return m_core->m_lar_solver; }

const lp::lar_solver& intervals::ls() const { return m_core->m_lar_solver; }

std::ostream& intervals::print_explanations(const svector<lp::constraint_index> &expl , std::ostream& out) const {
    out << "interv expl:\n ";
    for (auto ci : expl)
        m_core->m_lar_solver.print_constraint_indices_only(ci, out);
    return out;
}

} // end of nla namespace

// instantiate the template
template class interval_manager<nla::intervals::im_config>;
