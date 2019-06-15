#include "math/lp/nla_core.h"
#include "math/interval/interval_def.h"
#include "math/lp/nla_intervals.h"

namespace nla {

bool intervals::get_lemmas() {
    m_region.reset();
    bool ret = false;
    for (auto const& k : c().m_to_refine) {
        if (get_lemma(c().emons()[k])) {
            ret = true;
        }
        if (c().done())
            break;
    }
    return ret;
}
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

bool intervals::get_lemma(monomial const& m) {
    interval  b, c, d;
    interval a = mul(m.vars());
    lp::impq v(val(m.var()));
    if (!m_imanager.lower_is_inf(a)) {
        lp::impq lb(rational(a.m_lower));
        if (m_config.lower_is_open(a))
            lb.y = 1;
        if (v < lb) {
            interval signs_a = mul_signs_with_deps(m.vars());
            add_empty_lemma();
            svector<lp::constraint_index> expl;
            m_dep_manager.linearize(signs_a.m_lower_dep, expl); 
            _().current_expl().add_expl(expl);
            llc cmp = m_config.lower_is_open(a)? llc::GT: llc::GE;
            mk_ineq(m.var(), cmp,  lb.x);
            TRACE("nla_solver", _().print_lemma(tout); );
            return true;
        }
    }

    if (!m_imanager.upper_is_inf(a)) {
        lp::impq ub(rational(a.m_upper));
        if (m_config.upper_is_open(a))
            ub.y = 1;
        if (v > ub) {
            interval signs_a = mul_signs_with_deps(m.vars());
            add_empty_lemma();
            svector<lp::constraint_index> expl;
            m_dep_manager.linearize(signs_a.m_upper_dep, expl); 
            _().current_expl().add_expl(expl);
            llc cmp = m_config.upper_is_open(a)? llc::LT: llc::LE;
            mk_ineq(m.var(), cmp,  ub.x);
            TRACE("nla_solver", _().print_lemma(tout); );
            return true;
        }
    }
    return false;
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
    TRACE("nla_intervals_detail", m_core->print_monomial_with_vars(m, tout) << "upper = " << r << "\n";);
    return r;
}
lp::impq intervals::get_lower_bound_of_monomial(lpvar j) const {
    const monomial& m = m_core->emons()[j];
    interval a = mul(m.vars());
    SASSERT(!a.m_lower_inf);    
    auto r = lp::impq(a.m_lower);
    if (a.m_lower_open)
        r.y = 1;
    TRACE("nla_intervals_detail", m_core->print_monomial_with_vars(m, tout) << "lower = " << r << "\n";);
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

std::ostream& intervals::print_explanations(const svector<lp::constraint_index> &expl , std::ostream& out) const {
    out << "interv expl:\n ";
    for (auto ci : expl)
        m_core->m_lar_solver.print_constraint_indices_only(ci, out);
    return out;
}

void intervals::get_explanation_of_upper_bound_for_monomial(lpvar j, svector<lp::constraint_index>& expl) const {
    interval a = mul_signs_with_deps(m_core->emons()[j].vars());
    m_dep_manager.linearize(a.m_upper_dep, expl);
    TRACE("nla_intervals", print_explanations(expl, tout););
}
void intervals::get_explanation_of_lower_bound_for_monomial(lpvar j, svector<lp::constraint_index>& expl) const{
    interval a = mul_signs_with_deps(m_core->emons()[j].vars());
    m_dep_manager.linearize(a.m_lower_dep, expl);    
    TRACE("nla_intervals", print_explanations(expl, tout););
    //    return m_intervals.get_explanation_of_lower_bound_for_monomial(j, expl ) 
}
}
// instantiate the template
template class interval_manager<nla::intervals::im_config>;
