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
    SASSERT(row_has_monomial_to_refine(row));
    std::unordered_set<lpvar> seen;
    for (const auto& p : row) {
        lpvar j = p.var();
        if (!c().is_monomial_var(j))
            continue;
        auto & m = c().emons()[j];
        
        std::unordered_set<lpvar> local_vars;
        for (lpvar k : m.vars()) { // have to do it to ignore the powers
            local_vars.insert(k);
        }
        for (lpvar k : local_vars) {
            auto it = seen.find(k);
            if (it == seen.end())
                seen.insert(k);
            else
                return true;
        }
    }
    return false;
}

bool horner::lemmas_on_expr(nex& e) {
    TRACE("nla_horner", tout << "e = " << e << "\n";);
    bool conflict = false;
    cross_nested cn(e, [this, & conflict](const nex& n) {
                           TRACE("nla_horner", tout << "cross-nested n = " << n << "\n";);
                           auto i = interval_of_expr(n);
                           TRACE("nla_horner", tout << "callback n = " << n << "\ni="; m_intervals.display(tout, i) << "\n";);
                           
                           conflict = m_intervals.check_interval_for_conflict_on_zero(i);
                           m_intervals.reset(); // clean the memory allocated by the interval bound dependencies
                           return conflict;
                       },
        [this](unsigned j) {  return c().var_is_fixed(j); }
        );
    cn.run();
    return conflict;
}


template <typename T> 
bool horner::lemmas_on_row(const T& row) {
    SASSERT (row_is_interesting(row));
    nex e = create_sum_from_row(row);
    return lemmas_on_expr(e);
}

void horner::horner_lemmas() {
    if (!c().m_settings.run_horner()) {
        TRACE("nla_solver", tout << "not generating horner lemmas\n";);
        return;
    }

    const auto& matrix = c().m_lar_solver.A_r();
    // choose only rows that depend on m_to_refine variables
    std::set<unsigned> rows_to_check; // we need it to be determenistic: cannot work with the unordered_set
    for (lpvar j : c().m_to_refine) {
        for (auto & s : matrix.m_columns[j])
            rows_to_check.insert(s.var());
    }
    svector<unsigned> rows;
    for (unsigned i : rows_to_check) {
        if (row_is_interesting(matrix.m_rows[i]))
            rows.push_back(i);
    }

    unsigned r = c().random();
    unsigned sz = rows.size();
    for (unsigned i = 0; i < sz; i++) {
        unsigned row_index = rows[(i + r) % sz];
        if (lemmas_on_row(matrix.m_rows[row_index]))
            break;
    }
}

typedef nla_expr<rational> nex;

nex horner::nexvar(lpvar j) const {
    // todo: consider deepen the recursion
    if (!c().is_monomial_var(j))
        return nex::var(j);
    const monomial& m = c().emons()[j];
    nex e(expr_type::MUL);
    for (lpvar k : m.vars()) {
        e.add_child(nex::var(k));
        CTRACE("nla_horner", c().is_monomial_var(k), c().print_var(k, tout) << "\n";);
    }
    return e;
}

template <typename T> nex horner::create_sum_from_row(const T& row) {
    TRACE("nla_horner", tout << "row="; m_core->print_term(row, tout) << "\n";);
    SASSERT(row.size() > 1);
    nex e(expr_type::SUM);
    for (const auto &p : row) {        
        e.add_child(nex::scalar(p.coeff())* nexvar(p.var()));
    }
    return e;
}


void horner::set_interval_for_scalar(interv& a, const rational& v) {
    m_intervals.set_lower(a, v);
    m_intervals.set_upper(a, v);
    m_intervals.set_lower_is_open(a, false);
    m_intervals.set_lower_is_inf(a, false);
    m_intervals.set_upper_is_open(a, false);
    m_intervals.set_upper_is_inf(a, false);
}

interv horner::interval_of_expr(const nex& e) {
    interv a;
    switch (e.type()) {
    case expr_type::SCALAR:
        set_interval_for_scalar(a, e.value());
        return a;
    case expr_type::SUM:
        return interval_of_sum(e);
    case expr_type::MUL:
        return interval_of_mul(e);
    case expr_type::VAR:
        set_var_interval(e.var(), a);
        return a;
    default:
        TRACE("nla_horner_details", tout << e.type() << "\n";);
        SASSERT(false);
        return interv();
    }
}
interv horner::interval_of_mul(const nex& e) {
    SASSERT(e.is_mul());
    auto & es = e.children();
    interv a = interval_of_expr(es[0]);
    if (m_intervals.is_zero(a)) {
        m_intervals.set_zero_interval_deps_for_mult(a);
        TRACE("nla_horner_details", tout << "es[0]= "<< es[0] << std::endl << "a = "; m_intervals.display(tout, a); );
        return a;
    }
    TRACE("nla_horner_details", tout << "es[0]= "<< es[0] << std::endl << "a = "; m_intervals.display(tout, a); );
    for (unsigned k = 1; k < es.size(); k++) {
        interv b = interval_of_expr(es[k]);
        if (m_intervals.is_zero(b)) {
            m_intervals.set_zero_interval_deps_for_mult(b);
            TRACE("nla_horner_details", tout << "es[k]= "<< es[k] << std::endl << ", "; m_intervals.display(tout, b); );
            TRACE("nla_horner_details", tout << "got zero\n"; );
            return b;
        }
        TRACE("nla_horner_details", tout << "es[" << k << "] "<< es[k] << ", "; m_intervals.display(tout, b); );
        interv c;
        interval_deps_combine_rule comb_rule;
        m_intervals.mul(a, b, c, comb_rule);
        TRACE("nla_horner_details", tout << "c before combine_deps() "; m_intervals.display(tout, c););
        m_intervals.combine_deps(a, b, comb_rule, c);
        TRACE("nla_horner_details", tout << "a "; m_intervals.display(tout, a););
        TRACE("nla_horner_details", tout << "c "; m_intervals.display(tout, c););
        m_intervals.set(a, c);
        TRACE("nla_horner_details", tout << "part mult "; m_intervals.display(tout, a););
    }
    TRACE("nla_horner_details",  tout << "e=" << e << "\n";
          tout << " return "; m_intervals.display(tout, a););
    return a;
}

void horner::add_mul_to_vector(const nex& e, vector<std::pair<rational, lpvar>> &v) {
    TRACE("nla_horner_details", tout << e << "\n";);
    SASSERT(e.is_mul() && e.size() > 0);
    if (e.size() == 1) {
        add_linear_to_vector(*(e.children().begin()), v);
        return;
    }
    rational r;
    lpvar j = -1;
    for (const nex & c : e.children()) {
        switch (c.type()) {
        case expr_type::SCALAR:
            r = c.value();
            break;
        case expr_type::VAR:
            j = c.var();
            break;
        default:
            TRACE("nla_horner_details", tout << e.type() << "\n";);
            SASSERT(false);
        }
    }
    SASSERT((j + 1) && !(r.is_zero() || r.is_one()));
    v.push_back(std::make_pair(r, j));
}

void horner::add_linear_to_vector(const nex& e, vector<std::pair<rational, lpvar>> &v) {
    TRACE("nla_horner_details", tout << e << "\n";);
    switch (e.type()) {
    case expr_type::MUL:
        add_mul_to_vector(e, v);
        break; 
    case expr_type::VAR:
        v.push_back(std::make_pair(rational(1), e.var()));
        break;
    default:
        SASSERT(!e.is_sum());
        // noop
    }
}
// e = a * can_t + b
lp::lar_term horner::expression_to_normalized_term(nex& e, rational& a, rational& b) {
    TRACE("nla_horner_details", tout << e << "\n";);
    lpvar smallest_j;
    vector<std::pair<rational, lpvar>> v;
    b = rational(0);
    unsigned a_index;
    for (const nex& c : e.children()) {
        if (c.is_scalar()) {
            b += c.value();
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


// we should have in the case of found a*m_terms[k] + b = e,
// where m_terms[k] corresponds to the returned lpvar
lpvar horner::find_term_column(const nex& e, rational& a, rational& b) const {
    nex n = e;
    lp::lar_term norm_t = expression_to_normalized_term(n, a, b);
    std::pair<rational, lpvar> a_j;
    if (c().m_lar_solver.fetch_normalized_term_column(norm_t, a_j)) {
        a /= a_j.first;
        return a_j.second;
    }
    return -1;
}

interv horner::interval_of_sum_no_terms(const nex& e) {
    auto & es = e.children(); 
    interv a = interval_of_expr(es[0]);
    if (m_intervals.is_inf(a)) {
        TRACE("nla_horner_details",  tout << "e=" << e << "\n";
          tout << " interv = "; m_intervals.display(tout, a););
        return a;
    }
        
    for (unsigned k = 1; k < es.size(); k++) {
        TRACE("nla_horner_details_sum", tout <<  "es[" << k << "]= " << es[k] << "\n";);
        interv b = interval_of_expr(es[k]);
        if (m_intervals.is_inf(b)) {
            TRACE("nla_horner_details", tout << "got inf\n";);
            return b;
        }
        interv c;
        interval_deps_combine_rule combine_rule;
        TRACE("nla_horner_details_sum", tout << "a = "; m_intervals.display(tout, a) << "\nb = "; m_intervals.display(tout, b) << "\n";);
        m_intervals.add(a, b, c, combine_rule);
        m_intervals.combine_deps(a, b, combine_rule, c);
        m_intervals.set(a, c);
        TRACE("nla_horner_details_sum", tout << es[k] << ", ";
              m_intervals.display(tout, a); tout << "\n";);
        if (m_intervals.is_inf(a)) {
            TRACE("nla_horner_details", tout << "got infinity\n";);            
            return a;
        }
    }
    TRACE("nla_horner_details",  tout << "e=" << e << "\n";
          tout << " interv = "; m_intervals.display(tout, a););
    return a;
}

bool horner::interval_from_term(const nex& e, interv & i) const {
    rational a, b;
    nex n = e;
    lpvar j = find_term_column(n, a, b);
    if (j + 1 == 0)
        return false;

    set_var_interval(j, i);
    interv bi;
    m_intervals.mul(a, i, bi);
    m_intervals.add(b, bi);
    m_intervals.set(i, bi);
    
    TRACE("nla_horner",
          c().m_lar_solver.print_column_info(j, tout) << "\n";
          tout << "a=" << a << ", b=" << b << "\n"; 
          tout << e << ", interval = "; m_intervals.display(tout, i););
    return true;
}


interv horner::interval_of_sum(const nex& e) {
    TRACE("nla_horner_details", tout << "e=" << e << "\n";);
    SASSERT(e.is_sum());
    interv i_e = interval_of_sum_no_terms(e);
    if (e.sum_is_a_linear_term()) {
        interv i_from_term ;
        if (interval_from_term(e, i_from_term)) {
            interv r = m_intervals.intersect(i_e, i_from_term);
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
void horner::set_var_interval(lpvar v, interv& b) const{
    m_intervals.set_var_interval_with_deps(v, b);    
    TRACE("nla_horner_details_var", tout << "v = "; print_var(v, tout) << "\n"; m_intervals.display(tout, b););    
}


}

