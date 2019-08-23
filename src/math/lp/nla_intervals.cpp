#include "math/lp/nla_core.h"
#include "math/interval/interval_def.h"
#include "math/lp/nla_intervals.h"
#include "util/mpq.h"

namespace nla {
void intervals::set_var_interval_with_deps(lpvar v, interval& b) const {
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

void intervals::set_var_interval(lpvar v, interval& b) const {
    lp::constraint_index ci;
    rational val;
    bool is_strict;
    if (ls().has_lower_bound(v, ci, val, is_strict)) {            
        m_config.set_lower(b, val);
        m_config.set_lower_is_open(b, is_strict);
        m_config.set_lower_is_inf(b, false);
    }
    else {
        m_config.set_lower_is_open(b, true);
        m_config.set_lower_is_inf(b, true);
    }
    if (ls().has_upper_bound(v, ci, val, is_strict)) {
        m_config.set_upper(b, val);
        m_config.set_upper_is_open(b, is_strict);
        m_config.set_upper_is_inf(b, false);
    }
    else {
        m_config.set_upper_is_open(b, true);
        m_config.set_upper_is_inf(b, true);
    }
}

void intervals::set_zero_interval_with_explanation(interval& i, const lp::explanation& exp) const {
    auto val = rational(0);
    m_config.set_lower(i, val);
    m_config.set_lower_is_open(i, false);
    m_config.set_lower_is_inf(i, false);
    m_config.set_upper(i, val);
    m_config.set_upper_is_open(i, false);
    m_config.set_upper_is_inf(i, false);
    i.m_lower_dep = i.m_upper_dep = mk_dep(exp);
}

void intervals::set_zero_interval(interval& i) const {
    auto val = rational(0);
    m_config.set_lower(i, val);
    m_config.set_lower_is_open(i, false);
    m_config.set_lower_is_inf(i, false);
    m_config.set_upper(i, val);
    m_config.set_upper_is_open(i, false);
    m_config.set_upper_is_inf(i, false);
}

void intervals::set_zero_interval_deps_for_mult(interval& a) {
    a.m_lower_dep = m_dep_manager.mk_join(a.m_lower_dep, a.m_upper_dep);
    a.m_upper_dep = a.m_lower_dep;
}

bool intervals::separated_from_zero_on_lower(const interval& i) const {
    if (lower_is_inf(i))
        return false;
    if (unsynch_mpq_manager::is_neg(lower(i)))
        return false;
    if (unsynch_mpq_manager::is_zero(lower(i)) && !m_config.lower_is_open(i))
        return false;
    return true;
}

bool intervals::separated_from_zero_on_upper(const interval& i) const {
    if (upper_is_inf(i))
        return false;
    if (unsynch_mpq_manager::is_pos(upper(i)))
        return false;
    if (unsynch_mpq_manager::is_zero(upper(i)) && !m_config.upper_is_open(i))
        return false;
    return true;
}


bool intervals::check_interval_for_conflict_on_zero(const interval & i) {
    return check_interval_for_conflict_on_zero_lower(i) || check_interval_for_conflict_on_zero_upper(i);
}

bool intervals::check_interval_for_conflict_on_zero_upper(const interval & i) {
    if (!separated_from_zero_on_upper(i))
        return false;
        
     add_empty_lemma();
     svector<lp::constraint_index> expl;
     m_dep_manager.linearize(i.m_upper_dep, expl); 
     _().current_expl().add_expl(expl);
     TRACE("nla_solver", print_lemma(tout););
     return true;
}

bool intervals::check_interval_for_conflict_on_zero_lower(const interval & i) {
    if (!separated_from_zero_on_lower(i))
        return false;
     add_empty_lemma();
     svector<lp::constraint_index> expl;
     m_dep_manager.linearize(i.m_lower_dep, expl); 
     _().current_expl().add_expl(expl);
     TRACE("nla_solver", print_lemma(tout););
     return true;
}

intervals::ci_dependency *intervals::mk_dep(lp::constraint_index ci) const {
    return m_dep_manager.mk_leaf(ci);
}

intervals::ci_dependency *intervals::mk_dep(const lp::explanation& expl) const {
    intervals::ci_dependency * r = nullptr;
    for (auto p : expl) {
        if (r == nullptr) {
            r = m_dep_manager.mk_leaf(p.second);
        } else {
            r = m_dep_manager.mk_join(r, m_dep_manager.mk_leaf(p.second));
        }
    }
    return r;
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
        out << rational(m_imanager.upper(i)) << (m_imanager.upper_is_open(i)? ")":"]");         
    }
    svector<lp::constraint_index> expl;
    m_dep_manager.linearize(i.m_lower_dep, expl);
    {
        lp::explanation e(expl);
        if (!expl.empty()) {
            out << "\nlower constraints\n";
            m_core->print_explanation(e, out);
            expl.clear();
        } else {
            out << "\nno lower constraints\n";
        }
    }
    m_dep_manager.linearize(i.m_upper_dep, expl);   
    {
        lp::explanation e(expl);
        if (!expl.empty()) {
            out << "upper constraints\n";    
            m_core->print_explanation(e, out);
        }else {
            out << "no upper constraints\n";
        }
    }
    return out;
}

lp::lar_solver& intervals::ls() { return m_core->m_lar_solver; }

const lp::lar_solver& intervals::ls() const { return m_core->m_lar_solver; }


} // end of nla namespace

// instantiate the template
template class interval_manager<nla::intervals::im_config>;
