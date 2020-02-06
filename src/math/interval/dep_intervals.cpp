/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

    dep_intervals.cpp

  Abstract:

    intervals with depedency tracking.

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:

   extracted from nla_intervals.cpp

  --*/

#include "math/interval/interval_def.h"
#include "math/interval/dep_intervals.h"
#include "util/mpq.h"


typedef enum dep_intervals::with_deps_t e_with_deps;

void dep_intervals::set_interval_for_scalar(interval& a, const rational& v) {
    set_lower(a, v);
    set_upper(a, v);
    set_lower_is_open(a, false);
    set_lower_is_inf(a, false);
    set_upper_is_open(a, false);
    set_upper_is_inf(a, false);
}





void dep_intervals::set_zero_interval(interval& i, u_dependency* dep) const {
    auto val = rational(0);
    m_config.set_lower(i, val);
    m_config.set_lower_is_open(i, false);
    m_config.set_lower_is_inf(i, false);
    m_config.set_upper(i, val);
    m_config.set_upper_is_open(i, false);
    m_config.set_upper_is_inf(i, false);
    i.m_lower_dep = i.m_upper_dep = dep;
}

void dep_intervals::set_zero_interval_deps_for_mult(interval& a) {
    a.m_lower_dep = mk_join(a.m_lower_dep, a.m_upper_dep);
    a.m_upper_dep = a.m_lower_dep;
}



void dep_intervals::add(const rational& r, interval& a) const {
    if (!a.m_lower_inf) {
        m_config.set_lower(a, a.m_lower + r);
    }
    if (!a.m_upper_inf) {
        m_config.set_upper(a, a.m_upper + r);
    }
}

bool dep_intervals::separated_from_zero_on_lower(const interval& i) const {
    if (lower_is_inf(i))
        return false;
    if (unsynch_mpq_manager::is_neg(lower(i)))
        return false;
    if (unsynch_mpq_manager::is_zero(lower(i)) && !m_config.lower_is_open(i))
        return false;
    return true;
}

bool dep_intervals::separated_from_zero_on_upper(const interval& i) const {
    if (upper_is_inf(i))
        return false;
    if (unsynch_mpq_manager::is_pos(upper(i)))
        return false;
    if (unsynch_mpq_manager::is_zero(upper(i)) && !m_config.upper_is_open(i))
        return false;
    return true;
}

std::ostream& dep_intervals::display(std::ostream& out, const interval& i) const {
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
    if (i.m_lower_dep) {
        out << "\nlower deps\n";
        // TBD: print_dependencies(i.m_lower_dep, out);
    }
    if (i.m_upper_dep) {
        out << "\nupper deps\n";
        // TBD: print_dependencies(i.m_upper_dep, out);   
    }
    return out;
}


bool dep_intervals::is_empty(interval const& a) const {
    if (a.m_lower_inf || a.m_upper_inf)
        return false;
    if (m_num_manager.gt(a.m_lower, a.m_upper))
        return true;
    if (m_num_manager.lt(a.m_lower, a.m_upper))
        return false;
    if (a.m_lower_open || a.m_upper_open)
        return true;
    return false;
}

template class interval_manager<dep_intervals::im_config>;
