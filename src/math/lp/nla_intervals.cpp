#include "math/lp/nla_core.h"
#include "math/interval/interval_def.h"
#include "math/lp/nla_intervals.h"
namespace nla {

bool intervals::check() {
    // m_region.reset();
    // for (auto const& m : m_core->emons()) {
    //     if (!check(m)) {
    //         return false;
    //     }
    // }
    // for (auto const& t : ls().terms()) {
    //     if (!check(*t)) {
    //         return false;
    //     }
    // }
    return true;
}
// create a product of interval signs together with the depencies
intervals::interval intervals::mul_signs_with_deps(const svector<lpvar>& vars) const {
    interval a, b, c;
    m_imanager.set(a, mpq(1));
    for (lpvar v : vars) {
         set_var_interval_signs_with_deps(v, b);
         if (m_imanager.is_zero(b))
             return b;
         interval_deps deps;
         m_imanager.mul(a, b, c, deps);
         m_imanager.set(a, c);
         m_config.add_deps(a, b, deps, a);
    }
    return a;
    
}

// bool intervals::check(monomial const& m) {
//     interval a, b, c, d;
//     m_imanager.set(a, mpq(1));
//     set_var_interval(m.var(), d);
//     if (m_imanager.lower_is_inf(d) && m_imanager.upper_is_inf(d)) {
//         return true;
//     }
//     for (lpvar v : m.vars()) {
//         // TBD allow for division to get range of a
//         // m = a*b*c, where m and b*c are bounded, then interval for a is m/b*c
//         if (m_imanager.lower_is_inf(a) && m_imanager.upper_is_inf(a)) {
//             return true;
//         }
//         // TBD: deal with powers v^n interval instead of multiplying v*v .. * v
//         set_var_interval(v, b);
//         interval_deps deps;
//         m_imanager.mul(a, b, c, deps);
//         m_imanager.set(a, c);
//         m_config.add_deps(a, b, deps, a);
//     }
//     if (m_imanager.before(a, d)) {
//         svector<lp::constraint_index> cs;
//         m_dep_manager.linearize(a.m_upper_dep, cs);
//         m_dep_manager.linearize(d.m_lower_dep, cs);
//         for (auto ci : cs) {
//             (void)ci;
//             SASSERT(false);
//             //expl.push_justification(ci);
//         }
//         // TBD conflict
//         return false;
//     }
//     if (m_imanager.before(d, a)) {
//         svector<lp::constraint_index> cs;
//         m_dep_manager.linearize(a.m_lower_dep, cs);
//         m_dep_manager.linearize(d.m_upper_dep, cs);
//         for (auto ci : cs) {
//             (void)ci;
//             SASSERT(false); //expl.push_justification(ci);
//         }
//         // TBD conflict
//         return false;
//     }
//     // could also perform bounds propagation:
//     // a has tighter lower/upper bound than m.var(), 
//     // -> transfer bound to m.var()
//     // all but one variable has bound
//     // -> transfer bound to that variable using division
//     return true;
// }

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
    
lp::impq intervals::get_upper_bound_of_monomial(lpvar j) const {
    const monomial& m = m_core->emons()[j];
    interval a = mul(m.vars());
    SASSERT(!m_imanager.upper_is_inf(a));
    auto r = lp::impq(a.m_upper);
    if (a.m_upper_open)
        r.y = -1;
    TRACE("nla_intervals", m_core->print_monomial_with_vars(m, tout) << "upper = " << r << "\n";);
    return r;
}
lp::impq intervals::get_lower_bound_of_monomial(lpvar j) const {
    const monomial& m = m_core->emons()[j];
    interval a = mul(m.vars());
    SASSERT(!a.m_lower_inf);    
    auto r = lp::impq(a.m_lower);
    if (a.m_lower_open)
        r.y = 1;
    TRACE("nla_intervals", m_core->print_monomial_with_vars(m, tout) << "lower = " << r << "\n";);
    return r;
}

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

bool intervals::monomial_has_lower_bound(lpvar j) const {
    const monomial& m = m_core->emons()[j];
    return product_has_upper_bound(-1, m.vars());
}

bool intervals::monomial_has_upper_bound(lpvar j) const {
    const monomial& m = m_core->emons()[j];
    return product_has_upper_bound(1, m.vars());
}
lp::lar_solver& intervals::ls() { return m_core->m_lar_solver; }

const lp::lar_solver& intervals::ls() const { return m_core->m_lar_solver; }

void intervals::get_explanation_of_upper_bound_for_monomial(lpvar j, svector<lp::constraint_index>& expl) const {
    interval a = mul_signs_with_deps(m_core->emons()[j].vars());
    m_dep_manager.linearize(a.m_upper_dep, expl);    
}
void intervals::get_explanation_of_lower_bound_for_monomial(lpvar j, svector<lp::constraint_index>& expl) const{
    interval a = mul_signs_with_deps(m_core->emons()[j].vars());
    m_dep_manager.linearize(a.m_lower_dep, expl);    
    //    return m_intervals.get_explanation_of_lower_bound_for_monomial(j, expl ) 
}
}
// instantiate the template
template class interval_manager<nla::intervals::im_config>;
