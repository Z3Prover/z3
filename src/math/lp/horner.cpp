/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/

#include "math/lp/horner.h"
#include "math/lp/nla_core.h"
#include "math/lp/lp_utils.h"
#include "math/lp/cross_nested.h"

namespace nla {
typedef intervals::interval interv;
horner::horner(core * c) : common(c), m_intervals(c, c->reslim()) {}

template <typename T>
bool horner::row_has_monomial_to_refine(const T& row) const {
    for (const auto& p : row) {
        if (c().m_to_refine.contains(p.var()))
            return true;
    }
    return false;
    
}
// Returns true if the row has at least two monomials sharing a variable
template <typename T>
bool horner::row_is_interesting(const T& row) const {
    TRACE("nla_solver_details", m_core->print_term(row, tout););
    if (row.size() > m_core->m_nla_settings.horner_row_length_limit()) {
        TRACE("nla_solver_details", tout << "disregard\n";);
        return false;
    }
    SASSERT(row_has_monomial_to_refine(row));
    c().clear_active_var_set();
    for (const auto& p : row) {
        lpvar j = p.var();
        if (!c().is_monic_var(j))
            continue;
        auto & m = c().emons()[j];
        
        for (lpvar k : m.vars()) {
            if (c().active_var_set_contains(k))
                return true;
        }
        for (lpvar k : m.vars()) {
            c().insert_to_active_var_set(k);
        }
    }
    return false;
}

bool horner::lemmas_on_expr(cross_nested& cn, nex_sum* e) {
    TRACE("nla_horner", tout << "e = " << *e << "\n";);
    cn.run(e);
    return cn.done();
}


bool horner::check_cross_nested_expr(const nex* n) {
    TRACE("nla_horner", tout << "cross-nested n = " << *n << ", n->type() == " << n->type() << "\n";);
    c().lp_settings().stats().m_cross_nested_forms++;

    auto i = interval_of_expr(n, 1);
    TRACE("nla_horner", tout << "callback n = " << *n << "\ni="; m_intervals.display(tout, i) << "\n";);
    if (!m_intervals.separated_from_zero(i)) {
        m_intervals.reset();
        return false;
    }
    auto id = interval_of_expr_with_deps(n, 1);
    TRACE("nla_horner", tout << "conflict: id = "; m_intervals.display(tout, id ) << *n << "\n";);
    m_intervals.check_interval_for_conflict_on_zero(id);
    m_intervals.reset(); // clean the memory allocated by the interval bound dependencies
    return true;
}

template <typename T> 
bool horner::lemmas_on_row(const T& row) {
    cross_nested cn(
        [this](const nex* n) { return check_cross_nested_expr(n); },
        [this](unsigned j)   { return c().var_is_fixed(j); },
        [this]() { return c().random(); }, m_nex_creator);

    SASSERT (row_is_interesting(row));
    create_sum_from_row(row, cn.get_nex_creator(), m_row_sum);
    nex* e =  m_nex_creator.simplify(&m_row_sum);
    if (!e->is_sum())
        return false;
    
    return lemmas_on_expr(cn, to_sum(e));
}

void horner::horner_lemmas() {
    if (!c().m_nla_settings.run_horner()) {
        TRACE("nla_solver", tout << "not generating horner lemmas\n";);
        return;
    }
    c().lp_settings().stats().m_horner_calls++;
    const auto& matrix = c().m_lar_solver.A_r();
    // choose only rows that depend on m_to_refine variables
    std::set<unsigned> rows_to_check; // we need it to be determenistic: cannot work with the unordered_set
    for (lpvar j : c().m_to_refine) {
        for (auto & s : matrix.m_columns[j])
            rows_to_check.insert(s.var());
    }
    c().prepare_active_var_set();
    svector<unsigned> rows;
    for (unsigned i : rows_to_check) {
        if (row_is_interesting(matrix.m_rows[i]))
            rows.push_back(i);
    }

    unsigned r = c().random();
    unsigned sz = rows.size();
    for (unsigned i = 0; i < sz; i++) {
        unsigned row_index = rows[(i + r) % sz];
        if (lemmas_on_row(matrix.m_rows[row_index])) {
            c().lp_settings().stats().m_horner_conflicts++;
            break;
        }
    }
}


void horner::set_interval_for_scalar(interv& a, const rational& v) {
    m_intervals.set_lower(a, v);
    m_intervals.set_upper(a, v);
    m_intervals.set_lower_is_open(a, false);
    m_intervals.set_lower_is_inf(a, false);
    m_intervals.set_upper_is_open(a, false);
    m_intervals.set_upper_is_inf(a, false);
}

interv horner::power_with_deps(const interv& a, unsigned n) {
    interv b;
    interval_deps_combine_rule combine_rule;
    m_intervals.power(a, n, b, combine_rule);
    TRACE("nla_horner_details", tout << "power of "; m_intervals.display(tout, a) << " = ";
          m_intervals.display(tout, b) << "\n";);
    return b; 
}

interv horner::interval_of_expr_with_deps(const nex* e, unsigned power) {
    interv a;
    switch (e->type()) {
    case expr_type::SCALAR:
        set_interval_for_scalar(a, to_scalar(e)->value());
        if (power != 1) {
            return power_with_deps(a, power);
        }
        return a;
    case expr_type::SUM:
        {
        interv b = interval_of_sum_with_deps(to_sum(e));
        if (power != 1)
            return power_with_deps(b, power);
        return b;
        }
    case expr_type::MUL:
        {
        interv b = interval_of_mul_with_deps(to_mul(e));
        if (power != 1)
            return power_with_deps(b, power);;
        return b;        
    }
    case expr_type::VAR: 
        set_var_interval_with_deps(to_var(e)->var(), a);
        if (power != 1)
            return power_with_deps(a, power);;
        return a;
    default:
        TRACE("nla_horner_details", tout << e->type() << "\n";);
        SASSERT(false);
        return interv();
    }
}

interv horner::interval_of_expr(const nex* e, unsigned power) {
    TRACE("nla_horner_details", tout << "e = " << *e << "\n";);
    interv a;
    switch (e->type()) {
    case expr_type::SCALAR:
        set_interval_for_scalar(a, to_scalar(e)->value());
        break;
    case expr_type::SUM:
        {
            interv b = interval_of_sum(to_sum(e));
            if (power != 1) {
                return power_with_deps(b, power);;
            }
            return b;
        }
    case expr_type::MUL:
        {
        interv b  = interval_of_mul(to_mul(e));
        if (power != 1) {
            return power_with_deps(b, power);;
        }
        return b;
    }
    case expr_type::VAR:
        set_var_interval(to_var(e)->var(), a);
        break;
    default:
        TRACE("nla_horner_details", tout << e->type() << "\n";);
        SASSERT(false);
        return interv();
    }
    if (power != 1) {
        return power_with_deps(a, power);;
    }
    return a;
}


interv horner::interval_of_mul_with_deps(const nex_mul* e) {
    const nex * zero_interval_child = get_zero_interval_child(e);
    if (zero_interval_child) {
        interv a = interval_of_expr_with_deps(zero_interval_child, 1);
        m_intervals.set_zero_interval_deps_for_mult(a);
        TRACE("nla_horner_details", tout << "zero_interval_child = "<< *zero_interval_child << std::endl << "a = "; m_intervals.display(tout, a); );
        return a;   
    } 
        
    SASSERT(e->is_mul());
    interv a;
    set_interval_for_scalar(a, e->coeff());
    TRACE("nla_horner_details", tout << "a = "; m_intervals.display(tout, a); );
    for (const auto & ep : *e) {
        interv b = interval_of_expr_with_deps(ep.e(), ep.pow());
        TRACE("nla_horner_details", tout << "ep = " << ep << ", "; m_intervals.display(tout, b); );
        interv c;
        interval_deps_combine_rule comb_rule;
        m_intervals.mul_two_intervals(a, b, c, comb_rule);
        TRACE("nla_horner_details", tout << "c before combine_deps() "; m_intervals.display(tout, c););
        m_intervals.combine_deps(a, b, comb_rule, c);
        TRACE("nla_horner_details", tout << "a "; m_intervals.display(tout, a););
        TRACE("nla_horner_details", tout << "c "; m_intervals.display(tout, c););
        m_intervals.set_with_deps(a, c);
        TRACE("nla_horner_details", tout << "part mult "; m_intervals.display(tout, a););
    }
    TRACE("nla_horner_details",  tout << "e=" << *e << "\n";
          tout << " return "; m_intervals.display(tout, a););
    return a;
}

interv horner::interval_of_mul(const nex_mul* e) {
    TRACE("nla_horner_details", tout << "e = " << *e <<  "\n";);
    const nex * zero_interval_child = get_zero_interval_child(e);
    if (zero_interval_child) {
        interv a = interval_of_expr(zero_interval_child, 1);
        m_intervals.set_zero_interval_deps_for_mult(a);
        TRACE("nla_horner_details", tout << "zero_interval_child = "<< *zero_interval_child << std::endl << "a = "; m_intervals.display(tout, a); );
        return a;   
    } 
        
    interv a;
    
    set_interval_for_scalar(a, e->coeff());
    TRACE("nla_horner_details", tout << "a = "; m_intervals.display(tout, a); );
    for (const auto & ep : *e) {
        interv b = interval_of_expr(ep.e(), ep.pow() );
        TRACE("nla_horner_details", tout << "ep = " << ep << ", "; m_intervals.display(tout, b); );
        interv c;
        interval_deps_combine_rule comb_rule;
        m_intervals.mul_two_intervals(a, b, c, comb_rule);
        TRACE("nla_horner_details", tout << "c before combine_deps() "; m_intervals.display(tout, c););
        m_intervals.combine_deps(a, b, comb_rule, c);
        TRACE("nla_horner_details", tout << "a "; m_intervals.display(tout, a););
        TRACE("nla_horner_details", tout << "c "; m_intervals.display(tout, c););
        m_intervals.set(a, c, 33); 
        TRACE("nla_horner_details", tout << "part mult "; m_intervals.display(tout, a););
    }
    TRACE("nla_horner_details",  tout << "e=" << *e << "\n";
          tout << " return "; m_intervals.display(tout, a););
    return a;
}


void horner::add_mul_of_degree_one_to_vector(const nex_mul* e, vector<std::pair<rational, lpvar>> &v) {
    TRACE("nla_horner_details", tout << *e << "\n";);
    SASSERT(e->size() == 1);
    SASSERT((*e)[0].pow() == 1);
    const nex *ev = (*e)[0].e();
    lpvar j = to_var(ev)->var();
    v.push_back(std::make_pair(e->coeff(), j));
}

void horner::add_linear_to_vector(const nex* e, vector<std::pair<rational, lpvar>> &v) {
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
lp::lar_term horner::expression_to_normalized_term(const nex_sum* e, rational& a, rational& b) {
    TRACE("nla_horner_details", tout << *e << "\n";);
    lpvar smallest_j;
    vector<std::pair<rational, lpvar>> v;
    b = rational(0);
    unsigned a_index;
    for (const nex* c : e->children()) {
        if (c->is_scalar()) {
            b += to_scalar(c)->value();
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
        for (unsigned k = 0; k < v.size(); k++) {
            auto& p = v[k];
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

bool horner::mul_has_inf_interval(const nex_mul* e) const {
    bool has_inf = false;
    for (const auto & p  : e->children()) {
        const nex *c = p.e();
        if (!c->is_elementary())
            return false; 
        if (has_zero_interval(c))
            return false;
        has_inf |= has_inf_interval(c);
    }
    return has_inf;
}

bool horner::has_inf_interval(const nex* e) const {
    if (e->is_var())
        return c().no_bounds(to_var(e)->var());
    if (e->is_mul()) {
        return mul_has_inf_interval(to_mul(e));
    }
    if (e->is_scalar())
        return false;
    for (auto * c : to_sum(e)->children()) {
        if (has_inf_interval(c))
            return true;        
    }
    return false;
}

bool horner::has_zero_interval(const nex* e) const {
    SASSERT(!e->is_scalar() || !to_scalar(e)->value().is_zero());
    if (! e->is_var())
        return false;
    return c().var_is_fixed_to_zero(to_var(e)->var());
}

const nex* horner::get_zero_interval_child(const nex_mul* e) const {
    for (const auto & p : e->children()) {
        const nex * c = p.e();
        if (has_zero_interval(c))
            return c;        
    }
    return nullptr;
}

const nex* horner::get_inf_interval_child(const nex_sum* e) const {
    for (auto * c : e->children()) {
        if (has_inf_interval(c))
            return c;        
    }
    return nullptr;
}

// we should have in the case of found a * m_terms[k] + b = e,
// where m_terms[k] corresponds to the returned lpvar
lpvar horner::find_term_column(const lp::lar_term & norm_t, rational& a) const {
    std::pair<rational, lpvar> a_j;
    if (c().m_lar_solver.fetch_normalized_term_column(norm_t, a_j)) {
        a /= a_j.first;
        return a_j.second;
    }
    return -1;
}

interv horner::interval_of_sum_no_term_with_deps(const nex_sum* e) {
    const nex* inf_e = get_inf_interval_child(e);
    if (inf_e) {
        return interv();
    }
    auto & es = e->children(); 
    interv a = interval_of_expr_with_deps(es[0], 1);
    for (unsigned k = 1; k < es.size(); k++) {
        TRACE("nla_horner_details_sum", tout <<  "es[" << k << "]= " << *es[k] << "\n";);
        interv b = interval_of_expr_with_deps(es[k], 1);
        interv c;
        interval_deps_combine_rule combine_rule;
        TRACE("nla_horner_details_sum", tout << "a = "; m_intervals.display(tout, a) << "\nb = "; m_intervals.display(tout, b) << "\n";);
        m_intervals.add(a, b, c, combine_rule);
        m_intervals.combine_deps(a, b, combine_rule, c);
        m_intervals.set_with_deps(a, c);
        TRACE("nla_horner_details_sum", tout << *es[k] << ", ";
              m_intervals.display(tout, a); tout << "\n";);
    }
    TRACE("nla_horner_details",  tout << "e=" << *e << "\n";
          tout << " interv = "; m_intervals.display(tout, a););
    return a;
}

interv horner::interval_of_sum_no_term(const nex_sum* e) {
    const nex* inf_e = get_inf_interval_child(e);
    if (inf_e) {
        return interv();
    }
    auto & es = e->children(); 
    interv a = interval_of_expr(es[0], 1);
    for (unsigned k = 1; k < es.size(); k++) {
        TRACE("nla_horner_details_sum", tout <<  "es[" << k << "]= " << *es[k] << "\n";);
        interv b = interval_of_expr(es[k], 1);
        interv c;
        interval_deps_combine_rule combine_rule;
        TRACE("nla_horner_details_sum", tout << "a = "; m_intervals.display(tout, a) << "\nb = "; m_intervals.display(tout, b) << "\n";);
        m_intervals.add(a, b, c, combine_rule);
        m_intervals.combine_deps(a, b, combine_rule, c);
        m_intervals.set(a, c, 22);
        TRACE("nla_horner_details_sum", tout << *es[k] << ", ";
              m_intervals.display(tout, a); tout << "\n";);
    }
    TRACE("nla_horner_details",  tout << "e=" << *e << "\n";
          tout << " interv = "; m_intervals.display(tout, a););
    return a;
}

bool horner::interval_from_term_with_deps(const nex* e, interv & i) const {
    rational a, b;
    lp::lar_term norm_t = expression_to_normalized_term(to_sum(e), a, b);
    lp::explanation exp;
    if (c().explain_by_equiv(norm_t, exp)) {
        m_intervals.set_zero_interval_with_explanation(i, exp);
        TRACE("nla_horner", tout << "explain_by_equiv\n";);
        return true;
    }
    lpvar j = find_term_column(norm_t, a);
    if (j + 1 == 0)
        return false;

    set_var_interval_with_deps(j, i);
    interv bi;
    m_intervals.mul_with_deps(a, i, bi);
    m_intervals.add(b, bi);
    m_intervals.set_with_deps(i, bi);
    
    TRACE("nla_horner",
          c().m_lar_solver.print_column_info(j, tout) << "\n";
          tout << "a=" << a << ", b=" << b << "\n"; 
          tout << *e << ", interval = "; m_intervals.display(tout, i););
    return true;
}

bool horner::interval_from_term(const nex* e, interv & i) const {
    rational a, b;
    lp::lar_term norm_t = expression_to_normalized_term(to_sum(e), a, b);
    lp::explanation exp;
    if (c().explain_by_equiv(norm_t, exp)) {
        m_intervals.set_zero_interval(i);
        TRACE("nla_horner", tout << "explain_by_equiv\n";);
        return true;
    }
    lpvar j = find_term_column(norm_t, a);
    if (j + 1 == 0)
        return false;

    set_var_interval(j, i);
    interv bi;
    m_intervals.mul_no_deps(a, i, bi);
    m_intervals.add(b, bi);
    m_intervals.set(i, bi, 44);
    
    TRACE("nla_horner",
          c().m_lar_solver.print_column_info(j, tout) << "\n";
          tout << "a=" << a << ", b=" << b << "\n"; 
          tout << *e << ", interval = "; m_intervals.display(tout, i););
    return true;

}


interv horner::interval_of_sum_with_deps(const nex_sum* e) {
    TRACE("nla_horner_details", tout << "e=" << *e << "\n";);
    interv i_e = interval_of_sum_no_term_with_deps(e);
    if (e->is_a_linear_term()) {
        SASSERT(e->is_sum() && e->size() > 1);
        interv i_from_term ;
        if (interval_from_term_with_deps(e, i_from_term)) {
            interv r = m_intervals.intersect_with_deps(i_e, i_from_term);
            TRACE("nla_horner_details", tout << "intersection="; m_intervals.display(tout, r) << "\n";);
            if (m_intervals.is_empty(r)) {
                SASSERT(false); // not implemented
            }
            return r;
                
        }
    }
    return i_e;
}

interv horner::interval_of_sum(const nex_sum* e) {
    interv i_e = interval_of_sum_no_term(e);
    TRACE("nla_horner_details", tout << "e=" << *e << "\ni_e="; m_intervals.display(tout, i_e) << "\n";);
    if (e->is_a_linear_term()) {
        SASSERT(e->is_sum() && e->size() > 1);
        interv i_from_term ;
        if (interval_from_term(e, i_from_term)) {
            TRACE("nla_horner_details", tout << "i_from_term="; m_intervals.display(tout, i_from_term) << "\n";);
           interv r = m_intervals.intersect(i_e, i_from_term, 44);
            TRACE("nla_horner_details", tout << "intersection="; m_intervals.display(tout, r) << "\n";);
            if (m_intervals.is_empty(r)) {
                SASSERT(false); // not implemented
            }
            return r;
                
        }
    }
    return i_e;
}

// sets the dependencies also
void horner::set_var_interval_with_deps(lpvar v, interv& b) const{
    m_intervals.set_var_interval_with_deps(v, b);    
    TRACE("nla_horner_details_var", tout << "v = "; print_var(v, tout) << "\n"; m_intervals.display(tout, b););    
}

void horner::set_var_interval(lpvar v, interv& b) const{
    m_intervals.set_var_interval(v, b);    
    TRACE("nla_horner_details_var", tout << "v = "; print_var(v, tout) << "\n"; m_intervals.display(tout, b););    
}


}

