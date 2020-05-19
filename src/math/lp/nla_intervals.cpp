#include "math/lp/nla_core.h"
#include "math/interval/interval_def.h"
#include "math/lp/nla_intervals.h"
#include "util/mpq.h"

namespace nla {
typedef enum dep_intervals::with_deps_t e_with_deps;

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

std::ostream & intervals::print_dependencies(u_dependency* deps , std::ostream& out) const {
    svector<lp::constraint_index> expl;
    m_dep_intervals.linearize(deps, expl);
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

std::ostream& intervals::display_separating_interval(std::ostream& out, const nex*n, const scoped_dep_interval& interv_wd, u_dependency* initial_deps) {
     out << "conflict: interv_wd = "; display(out, interv_wd ) <<"expr = " << *n << "\n, initial deps\n"; print_dependencies(initial_deps, out);
          out << ", expressions vars = \n";
          for(lpvar j: m_core->get_vars_of_expr_with_opening_terms(n)) {
              m_core->print_var(j, out);
          }
          out << "\n";
          return out;
}

// return true iff the interval of n is does not contain 0
bool intervals::check_nex(const nex* n, u_dependency* initial_deps) {
    m_core->lp_settings().stats().m_cross_nested_forms++;
    scoped_dep_interval i(get_dep_intervals());
    std::function<void (const lp::explanation&)> f = [this](const lp::explanation& e) {
        new_lemma lemma(*m_core, "check_nex");
        lemma &= e;
    };
    if (!interval_of_expr<e_with_deps::without_deps>(n, 1, i, f)) {
        // found a conflict during the interval calculation
        return true;
    }
    if (!m_dep_intervals.separated_from_zero(i)) {
        return false;
    }
    scoped_dep_interval interv_wd(get_dep_intervals());
    interval_of_expr<e_with_deps::with_deps>(n, 1, interv_wd, f);
    TRACE("nla_intervals", display_separating_interval(tout, n, interv_wd, initial_deps););    
    m_dep_intervals.check_interval_for_conflict_on_zero(interv_wd, initial_deps, f);
    return true;
}

void intervals::add_mul_of_degree_one_to_vector(const nex_mul* e, vector<std::pair<rational, lpvar>> &v) {
    TRACE("nla_intervals_details", tout << *e << "\n";);
    SASSERT(e->size() == 1);
    SASSERT((*e)[0].pow() == 1);
    const nex *ev = (*e)[0].e();
    lpvar j = to_var(ev)->var();
    v.push_back(std::make_pair(e->coeff(), j));
}

void intervals::add_linear_to_vector(const nex* e, vector<std::pair<rational, lpvar>> &v) {
    TRACE("nla_intervals_details", tout << *e << "\n";);
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
    TRACE("nla_intervals_details", tout << *e << "\n";);
    lpvar smallest_j = 0;
    vector<std::pair<rational, lpvar>> v;
    b = rational(0);
    unsigned a_index = UINT_MAX;
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
    TRACE("nla_intervals_details", tout << "a_index = " << a_index << ", v="; print_vector(v, tout) << "\n";);
    a = v[a_index].first;
    lp::lar_term t;

    if (a.is_one()) {
        for (auto& p : v) {
            t.add_monomial(p.first, p.second);
        }
    } else {
        for (unsigned k = 0; k < v.size(); k++) {
            auto& p = v[k];
            if (k != a_index) 
                t.add_monomial(p.first/a, p.second);
            else
                t.add_var(p.second);
        }
    }
    TRACE("nla_intervals_details", tout << a << "* (";
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

void intervals::set_zero_interval_with_explanation(interval& i, const lp::explanation& exp) {
    auto val = rational(0);
    m_dep_intervals.set_lower(i, val);
    m_dep_intervals.set_lower_is_open(i, false);
    m_dep_intervals.set_lower_is_inf(i, false);
    m_dep_intervals.set_upper(i, val);
    m_dep_intervals.set_upper_is_open(i, false);
    m_dep_intervals.set_upper_is_inf(i, false);
    i.m_lower_dep = i.m_upper_dep = mk_dep(exp);
}

void intervals::set_zero_interval(interval& i) {
    auto val = rational(0);
    m_dep_intervals.set_lower(i, val);
    m_dep_intervals.set_lower_is_open(i, false);
    m_dep_intervals.set_lower_is_inf(i, false);
    m_dep_intervals.set_upper(i, val);
    m_dep_intervals.set_upper_is_open(i, false);
    m_dep_intervals.set_upper_is_inf(i, false);
}

void intervals::set_zero_interval_deps_for_mult(interval& a) {
    a.m_lower_dep = mk_join(a.m_lower_dep, a.m_upper_dep);
    a.m_upper_dep = a.m_lower_dep;
}

u_dependency *intervals::mk_dep(lp::constraint_index ci) {
    return m_dep_intervals.mk_leaf(ci);
}

u_dependency *intervals::mk_dep(const lp::explanation& expl) {
    u_dependency * r = nullptr;
    for (auto p : expl) {
        if (r == nullptr) {
            r = m_dep_intervals.mk_leaf(p.ci());
        } else {
            r = m_dep_intervals.mk_join(r, m_dep_intervals.mk_leaf(p.ci()));
        }
    }
    return r;
}

std::ostream& intervals::display(std::ostream& out, const interval& i) const {
    if (m_dep_intervals.lower_is_inf(i)) {
        out << "(-oo";
    } else {
        out << (m_dep_intervals.lower_is_open(i)? "(":"[") << rational(m_dep_intervals.lower(i));        
    }
    out << ",";
    if (m_dep_intervals.upper_is_inf(i)) {
        out << "oo)";
    } else {
        out << rational(m_dep_intervals.upper(i)) << (m_dep_intervals.upper_is_open(i)? ")":"]");         
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

template <e_with_deps wd>
void intervals::set_var_interval(lpvar v, interval& b) {
    TRACE("nla_intervals_details", m_core->print_var(v, tout) << "\n";);
    lp::constraint_index ci;
    rational val;
    bool is_strict;
    if (ls().has_lower_bound(v, ci, val, is_strict)) {
        m_dep_intervals.set_lower(b, val);
        m_dep_intervals.set_lower_is_open(b, is_strict);
        m_dep_intervals.set_lower_is_inf(b, false);
        if (wd == e_with_deps::with_deps) b.m_lower_dep = mk_dep(ci);
    }
    else {
        m_dep_intervals.set_lower_is_open(b, true);
        m_dep_intervals.set_lower_is_inf(b, true);
        if (wd == e_with_deps::with_deps) b.m_lower_dep = nullptr;
    }
    if (ls().has_upper_bound(v, ci, val, is_strict)) {
        m_dep_intervals.set_upper(b, val);
        m_dep_intervals.set_upper_is_open(b, is_strict);
        m_dep_intervals.set_upper_is_inf(b, false);
        if (wd == e_with_deps::with_deps) b.m_upper_dep = mk_dep(ci);
    }
    else {
        m_dep_intervals.set_upper_is_open(b, true);
        m_dep_intervals.set_upper_is_inf(b, true);
        if (wd == e_with_deps::with_deps) b.m_upper_dep = nullptr;
    }
}

template <e_with_deps wd>
bool intervals::interval_from_term(const nex& e, scoped_dep_interval& i) {
    rational a, b;
    lp::lar_term norm_t = expression_to_normalized_term(&e.to_sum(), a, b);
    lp::explanation exp;
    if (m_core->explain_by_equiv(norm_t, exp)) {
        m_dep_intervals.set_interval_for_scalar(i, b);
        if (wd == e_with_deps::with_deps) {
            for (auto p : exp) {
                i.get().m_lower_dep = mk_join(i.get().m_lower_dep, mk_leaf(p.ci()));
            }
            i.get().m_upper_dep = i.get().m_lower_dep;
        }
        TRACE("nla_intervals", tout << "explain_by_equiv\n";);
        return true;
    }
    lpvar j = find_term_column(norm_t, a);
    if (j + 1 == 0)
        return false;

    set_var_interval<wd>(j, i);
    interval bi;
    m_dep_intervals.mul<wd>(a, i, bi);
    m_dep_intervals.add(b, bi);
    m_dep_intervals.set<wd>(i, bi);

    TRACE("nla_intervals",
          m_core->m_lar_solver.print_column_info(j, tout) << "\n";
          tout << "a=" << a << ", b=" << b << "\n";
          tout << e << ", interval = "; display(tout, i););
    return true;
}

template <e_with_deps wd, typename T>
bool intervals::interval_of_sum_no_term(const nex_sum& e, scoped_dep_interval & sdi, const std::function<void (const T&)>& f) {
    if (has_inf_interval(e)) {
        SASSERT(m_dep_intervals.lower_is_inf(sdi) && m_dep_intervals.upper_is_inf(sdi));
        return true; // no conflict
    }
    
    if (!interval_of_expr<wd>(e[0], 1, sdi, f))
        return false;
    for (unsigned k = 1; k < e.size(); k++) {
        TRACE("nla_intervals_details", tout << "e[" << k << "]= " << *e[k] << "\n";);
        scoped_dep_interval  b(get_dep_intervals());
        if (!interval_of_expr<wd>(e[k], 1, b, f)) {
            return false;
        }
        scoped_dep_interval  c(get_dep_intervals());

        TRACE("nla_intervals_details", tout << "sdi = "; display(tout, sdi) << "\nb = "; display(tout, b) << "\n";);
        m_dep_intervals.add<wd>(sdi, b, c);        
        m_dep_intervals.set<wd>(sdi, c);
        TRACE("nla_intervals_details", tout << *e[k] << ", ";
              display(tout, sdi); tout << "\n";);
    }
    TRACE("nla_intervals_details", tout << "e=" << e << "\n";
          tout << " interv = "; display(tout, sdi););
    return true; // no conflict
}

// return true iff a.upper < b.lower, or a.upper == b.lower and one of these bounds is open
bool intervals::conflict_u_l(const interval& a, const interval& b) const {
     if (a.m_upper_inf) {
         return false;
     }
     if (b.m_lower_inf) {
         return false;
     }

     if (m_dep_intervals.num_manager().lt(a.m_upper, b.m_lower)) {
         return true;
     }

     if (m_dep_intervals.num_manager().gt(a.m_upper, b.m_lower)) {
            return false;
     }

     return a.m_upper_open || b.m_upper_open;
}

template <e_with_deps wd, typename T>
bool intervals::interval_of_sum(const nex_sum& e, scoped_dep_interval& a, const std::function<void (const T&)>& f) {
    TRACE("nla_intervals_details", tout << "e=" << e << "\n";);
    if(! interval_of_sum_no_term<wd>(e, a, f)) {
        return false;
    }
    TRACE("nla_intervals_details", tout << "a = "; display(tout, a););
    if (e.is_a_linear_term()) {
        SASSERT(e.is_sum() && e.size() > 1);
        scoped_dep_interval i_from_term(get_dep_intervals());
        if (interval_from_term<wd>(e, i_from_term)) {
            scoped_dep_interval r(get_dep_intervals());
            m_dep_intervals.intersect<wd>(a, i_from_term, r);
            TRACE("nla_intervals_details", tout << "intersection="; display(tout, r) << "\n";);
            
            if (m_dep_intervals.is_empty(r)) {
                TRACE("nla_intervals_details", tout << "empty\n";);
                if (wd == e_with_deps::with_deps) {
                    T expl;
                    if (conflict_u_l(a, i_from_term)) {
                        get_dep_intervals().linearize(a.get().m_upper_dep, expl);
                        get_dep_intervals().linearize(r.get().m_lower_dep, expl);                        
                    } else {
                        get_dep_intervals().linearize(r.get().m_upper_dep, expl);
                        get_dep_intervals().linearize(a.get().m_lower_dep, expl);                        
                    }                        
                    f(expl);
                } else {
                    // need to recalculate the interval with dependencies
                    scoped_dep_interval sa(get_dep_intervals());
                    interval_of_sum<e_with_deps::with_deps>(e, sa, f);
                }
                return false;
            }
            m_dep_intervals.set<wd>(a, r);
        }
    }
    return true;
}

template <e_with_deps wd, typename T>
bool intervals::interval_of_mul(const nex_mul& e, scoped_dep_interval& a, const std::function<void (const T&)>& f) {
    TRACE("nla_intervals_details", tout << "e = " << e << "\n";);
    const nex* zero_interval_child = get_zero_interval_child(e);
    if (zero_interval_child) {
        bool r = interval_of_expr<wd>(zero_interval_child, 1, a, f);
        SASSERT(r);
        (void)r;        
        if(wd == e_with_deps::with_deps)
            set_zero_interval_deps_for_mult(a);
        TRACE("nla_intervals_details", tout << "zero_interval_child = " << *zero_interval_child << std::endl << "a = "; display(tout, a); );
         return true; // regural calculation: no conflict
    }

    m_dep_intervals.set_interval_for_scalar(a, e.coeff());
    TRACE("nla_intervals_details", tout << "a = "; display(tout, a); );
    for (const auto& ep : e) {
        scoped_dep_interval b(get_dep_intervals());
        if (!interval_of_expr<wd>(ep.e(), ep.pow(), b, f))
            return false;
        TRACE("nla_intervals_details", tout << "ep = " << ep << ", "; display(tout, b); );
        scoped_dep_interval c(get_dep_intervals());
        m_dep_intervals.mul<wd>(a, b, c);
        TRACE("nla_intervals_details", tout << "a "; display(tout, a););
        TRACE("nla_intervals_details", tout << "c "; display(tout, c););
        m_dep_intervals.set<wd>(a, c);
        TRACE("nla_intervals_details", tout << "part mult "; display(tout, a););
    }
    TRACE("nla_intervals_details", tout << "e=" << e << "\n";
          tout << " return "; display(tout, a););
    return true;
}

template <e_with_deps wd>
void intervals::to_power(scoped_dep_interval& a, unsigned p) {
    if (p == 1) return;
    scoped_dep_interval b(m_dep_intervals);
    m_dep_intervals.power<wd>(a, p, b);
    m_dep_intervals.set<wd>(a, b);

}
template <e_with_deps wd, typename T>
bool intervals::interval_of_expr(const nex* e, unsigned p, scoped_dep_interval& a, const std::function<void (const T&)>& f) {
    switch (e->type()) {
    case expr_type::SCALAR:
        {
            m_dep_intervals.set_interval_for_scalar(a, power(to_scalar(e)->value(), p));
        }
        break;
    case expr_type::SUM: {
        if (!interval_of_sum<wd>(e->to_sum(), a, f))
            return false;
        if (p != 1) {
            to_power<wd>(a, p);
        }
        break;
    }
    case expr_type::MUL: {
        if (!interval_of_mul<wd>(e->to_mul(), a, f))
            return false;
        if (p != 1) {
            to_power<wd>(a, p);
        }
        break;
    }
    case expr_type::VAR:
        set_var_interval<wd>(e->to_var().var(), a);
        if (p != 1) {
            to_power<wd>(a, p);
        }
        break;
    default:
        TRACE("nla_intervals_details", tout << e->type() << "\n";);
        UNREACHABLE();        
    }
    return true; // no conflict
}


lp::lar_solver& intervals::ls() { return m_core->m_lar_solver; }

const lp::lar_solver& intervals::ls() const { return m_core->m_lar_solver; }


} // end of nla namespace

