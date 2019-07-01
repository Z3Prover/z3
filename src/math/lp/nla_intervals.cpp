#include "math/lp/nla_core.h"
#include "math/interval/interval_def.h"
#include "math/lp/nla_intervals.h"

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

void intervals::set_var_interval_signs_with_deps(lpvar v, interval& b) const {
    lp::constraint_index ci;
    rational val;
    bool is_strict;
    if (ls().has_lower_bound(v, ci, val, is_strict)) {            
        m_config.set_lower(b, sign(val));
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
        m_config.set_upper(b, sign(val));
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
    
intervals::ci_dependency *intervals::mk_dep(lp::constraint_index ci) const {
    return m_dep_manager.mk_leaf(ci);
}
    
*/
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

/*
intervals::interval intervals::mul(const svector<lpvar>& vars) const {
    interval a;
    m_imanager.set(a, mpq(1));
    
    for (lpvar j : vars) {
        interval b, c;
        set_var_interval(j, b);
        if (m_imanager.is_zero(b)) {
            return b;
        }
        m_imanager.mul(a, b, c);
        m_imanager.set(a, c);
    }
    return a;
}

intervals::interval intervals::mul_signs(const svector<lpvar>& vars) const {
    interval a;
    m_imanager.set(a, mpq(1));
    
    for (lpvar j : vars) {
        interval b, c;
        set_var_interval_signs(j, b);
        if (m_imanager.is_zero(b)) {
            return b;
        }
        m_imanager.mul(a, b, c);
        m_imanager.set(a, c);
    }
    return a;
}

bool intervals::product_has_upper_bound(int sign, const svector<lpvar>& vars) const {
    interval a = mul_signs(vars);
    SASSERT(sign == 1 || sign == -1);
    return sign == 1 ? !m_imanager.upper_is_inf(a) : !m_imanager.lower_is_inf(a);
}
*/
}

// instantiate the template
template class interval_manager<nla::intervals::im_config>;
