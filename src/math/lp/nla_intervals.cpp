#include "math/lp/nla_core.h"
#include "math/interval/interval_def.h"
#include "math/lp/nla_intervals.h"
#include "util/mpq.h"

namespace nla {


void intervals::set_interval_for_scalar(interv& a, const rational& v) {
    set_lower(a, v);
    set_upper(a, v);
    set_lower_is_open(a, false);
    set_lower_is_inf(a, false);
    set_upper_is_open(a, false);
    set_upper_is_inf(a, false);
}

const nex* intervals::get_inf_interval_child(const nex_sum& e) const {
    for (auto * c : e) {
        if (has_inf_interval(*c))
            return c;        
    }
    return nullptr;
}

bool intervals::mul_has_inf_interval(const nex_mul& e) const {
    bool has_inf = false;
    for (const auto & p : e) {
        const nex &c = *p.e();
        if (!c.is_elementary())
            return false; 
        if (has_zero_interval(c))
            return false;
        has_inf |= has_inf_interval(c);
    }
    return has_inf;
}

bool intervals::has_inf_interval(const nex& e) const {
    if (e.is_var())
        return m_core->no_bounds(e.to_var().var());
    if (e.is_mul()) 
        return mul_has_inf_interval(e.to_mul());    
    if (e.is_scalar())
        return false;
    for (auto * c : e.to_sum()) 
        if (has_inf_interval(*c))
            return true;            
    return false;
}

bool intervals::has_zero_interval(const nex& e) const {
    SASSERT(!e.is_scalar() || !e.to_scalar().value().is_zero());
    return e.is_var() && m_core->var_is_fixed_to_zero(e.to_var().var());
}

const nex* intervals::get_zero_interval_child(const nex_mul& e) const {
    for (const auto & p : e) {
        const nex * c = p.e();
        if (has_zero_interval(*c))
            return c;        
    }
    return nullptr;
}

std::ostream & intervals::print_dependencies(ci_dependency* deps , std::ostream& out) const {
    svector<lp::constraint_index> expl;
    m_dep_manager.linearize(deps, expl);
    {
        lp::explanation e(expl);
        if (!expl.empty()) {
            m_core->print_explanation(e, out);
            expl.clear();
        } else {
            out << "\nno constraints\n";
        }
    }
    return out;
}

// return true iff the interval of n is does not contain 0
bool intervals::check_nex(const nex* n, ci_dependency* initial_deps) {
    m_core->lp_settings().stats().m_cross_nested_forms++;
    auto i = interval_of_expr<without_deps>(n, 1);
    if (!separated_from_zero(i)) {
        reset();
        return false;
    }
    auto interv_wd = interval_of_expr<with_deps>(n, 1);
    TRACE("grobner", tout << "conflict: interv_wd = "; display(tout, interv_wd ) <<"expr = " << *n << "\n, initial deps\n"; print_dependencies(initial_deps, tout););
    check_interval_for_conflict_on_zero(interv_wd, initial_deps);
    reset(); // clean the memory allocated by the interval bound dependencies
    return true;
}

void intervals::add_mul_of_degree_one_to_vector(const nex_mul* e, vector<std::pair<rational, lpvar>> &v) {
    TRACE("nla_horner_details", tout << *e << "\n";);
    SASSERT(e->size() == 1);
    SASSERT((*e)[0].pow() == 1);
    const nex *ev = (*e)[0].e();
    lpvar j = to_var(ev)->var();
    v.push_back(std::make_pair(e->coeff(), j));
}

void intervals::add_linear_to_vector(const nex* e, vector<std::pair<rational, lpvar>> &v) {
    TRACE("nla_horner_details", tout << *e << "\n";);
    switch (e->type()) {
    case expr_type::MUL:
        add_mul_of_degree_one_to_vector(to_mul(e), v);
        break; 
    case expr_type::VAR:
        v.push_back(std::make_pair(rational(1), to_var(e)->var()));
        break;
    default:
        SASSERT(!e->is_sum());
        // noop
    }
}

// e = a * can_t + b
lp::lar_term intervals::expression_to_normalized_term(const nex_sum* e, rational& a, rational& b) {
    TRACE("nla_horner_details", tout << *e << "\n";);
    lpvar smallest_j;
    vector<std::pair<rational, lpvar>> v;
    b = rational(0);
    unsigned a_index;
    for (const nex* c : *e) {
        if (c->is_scalar()) {
            b += c->to_scalar().value();
        } else {
            add_linear_to_vector(c, v);
            if (v.empty())
                continue;
            if (v.size() == 1 ||  smallest_j > v.back().second) {
                smallest_j = v.back().second;
                a_index = v.size() - 1;
            }
        }
    }
    TRACE("nla_horner_details", tout << "a_index = " << a_index << ", v="; print_vector(v, tout) << "\n";);
    a = v[a_index].first;
    lp::lar_term t;

    if (a.is_one()) {
        for (auto& p : v) {
            t.add_coeff_var(p.first, p.second);
        }
    } else {
        for (unsigned k = 0; k < v.size(); k++) {
            auto& p = v[k];
            if (k != a_index) 
                t.add_coeff_var(p.first/a, p.second);
            else
                t.add_var(p.second);
        }
    }
    TRACE("nla_horner_details", tout << a << "* (";
          lp::lar_solver::print_term_as_indices(t, tout) << ") + " << b << std::endl;);
    SASSERT(t.is_normalized());
    return t;
}


// we should have in the case of found a * m_terms[k] + b = e,
// where m_terms[k] corresponds to the returned lpvar
lpvar intervals::find_term_column(const lp::lar_term & norm_t, rational& a) const {
    std::pair<rational, lpvar> a_j;
    if (m_core->m_lar_solver.fetch_normalized_term_column(norm_t, a_j)) {
        a /= a_j.first;
        return a_j.second;
    }
    return -1;
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

bool intervals::check_interval_for_conflict_on_zero(const interval & i, ci_dependency* dep) {
    return check_interval_for_conflict_on_zero_lower(i, dep) || check_interval_for_conflict_on_zero_upper(i, dep);
}

bool intervals::check_interval_for_conflict_on_zero_upper(
    const interval & i,
    ci_dependency* dep) {
    if (!separated_from_zero_on_upper(i))
        return false;

    TRACE("grobner", display(tout, i););
    m_core->add_empty_lemma();
    svector<lp::constraint_index> expl;
    dep = m_dep_manager.mk_join(dep, i.m_upper_dep);
    m_dep_manager.linearize(dep, expl); 
    m_core->current_expl().add_expl(expl);
    TRACE("nla_solver", m_core->print_lemma(tout););
    return true;
}

bool intervals::check_interval_for_conflict_on_zero_lower(const interval & i, ci_dependency* dep) {
    if (!separated_from_zero_on_lower(i)) {
        return false;
    }
    TRACE("grobner", display(tout, i););
    m_core->add_empty_lemma();
    svector<lp::constraint_index> expl;
    dep = m_dep_manager.mk_join(dep, i.m_lower_dep);
    m_dep_manager.linearize(dep, expl); 
    m_core->current_expl().add_expl(expl);
    TRACE("nla_solver", m_core->print_lemma(tout););
    return true;
}

common::ci_dependency *intervals::mk_dep(lp::constraint_index ci) const {
    return m_dep_manager.mk_leaf(ci);
}

common::ci_dependency *intervals::mk_dep(const lp::explanation& expl) const {
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
    if (i.m_lower_dep) {
        out << "\nlower deps\n";
        print_dependencies(i.m_lower_dep, out);
    }
    if (i.m_upper_dep) {
        out << "\nupper deps\n";
        print_dependencies(i.m_upper_dep, out);   
    }
    return out;
}

lp::lar_solver& intervals::ls() { return m_core->m_lar_solver; }

const lp::lar_solver& intervals::ls() const { return m_core->m_lar_solver; }


} // end of nla namespace

// instantiate the template
template class interval_manager<nla::intervals::im_config>;
