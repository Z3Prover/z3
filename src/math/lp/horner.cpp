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
bool horner::row_is_interesting(const T& row) const {
    if (row.size() <= 1)
        return false;
    for (const auto& p : row) {
        if (c().m_to_refine.contains(p.var()))
            return true;
    }
    return false;
}

void horner::lemmas_on_expr(nex& e) {
    TRACE("nla_cn", tout << "e = " << e << "\n";);    
    TRACE("nla_cn_cn", tout << "e = " << e << "\n";);
    cross_nested cn(e, [this](const nex& n) {
                        auto i = interval_of_expr(n);
                        m_intervals.check_interval_for_conflict_on_zero(i);} );
    
}


template <typename T> 
void horner::lemmas_on_row(const T& row) {
    if (!row_is_interesting(row))
        return;
    nex e = create_sum_from_row(row);
    lemmas_on_expr(e);
}

void horner::horner_lemmas() {
    if (!c().m_settings.run_horner()) {
        TRACE("nla_solver", tout << "not generating horner lemmas\n";);
        return;
    }

    const auto& matrix = c().m_lar_solver.A_r();
    for (unsigned i = 0; i < matrix.row_count(); i++) {
        lemmas_on_row(matrix.m_rows[i]);
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
    }
    return e;
}

template <typename T> nex horner::create_sum_from_row(const T& row) {
    TRACE("nla_cn", tout << "row="; m_core->print_term(row, tout) << "\n";);
    SASSERT(row.size() > 1);
    nex e(expr_type::SUM);
    for (const auto &p : row) {
        e.add_child(nex::mul(p.coeff(), nexvar(p.var())));
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
    
    TRACE("nla_cn_details", tout << e.type() << " e=" << e << std::endl;);
    interv a;
    switch (e.type()) {
    case expr_type::SCALAR:
        set_interval_for_scalar(a, e.value());
        return a;
    case expr_type::SUM:
        return interval_of_sum(e.children());
    case expr_type::MUL:
        return interval_of_mul(e.children());
    case expr_type::VAR:
        set_var_interval(e.var(), a);
        return a;
    default:
        TRACE("nla_cn_details", tout << e.type() << "\n";);
        SASSERT(false);
        return interv();
    }
}

interv horner::interval_of_mul(const vector<nex>& es) {    
    interv a = interval_of_expr(es[0]);
    //    std::cout << "a" << std::endl;
    TRACE("nla_cn_details", tout << "es[0]= "<< es[0] << std::endl << "a = "; m_intervals.display(tout, a); tout << "\n";);
    for (unsigned k = 1; k < es.size(); k++) {
        interv b = interval_of_expr(es[k]);
        interv c;
        interval_deps deps;
        m_intervals.mul(a, b, c, deps);
        m_intervals.set(a, c);
        m_intervals.add_deps(a, b, deps, a);
        TRACE("nla_cn_details", tout << "es["<< k << "] = " << es[k] << std::endl << "a = "; m_intervals.display(tout, a); tout << "\n";);
        if (m_intervals.is_zero(a)) {
            TRACE("nla_cn_details", tout << "got zero\n"; );
            break;
        }
    }
    TRACE("nla_cn_details",
          for (const auto &e : es) {
              tout << "("<< e << ")";
          }
          tout << " interv a = ";
          m_intervals.display(tout, a) << "\n";);
    return a;
}

interv horner::interval_of_sum(const vector<nex>& es) {
    interv a = interval_of_expr(es[0]);
    TRACE("nla_cn_details", tout << "es[0]= "  << es[0] << "\n"; m_intervals.display(tout, a) << "\n";);
    if (m_intervals.is_inf(a)) {
        return a;
    }
        
    for (unsigned k = 1; k < es.size(); k++) {
        TRACE("nla_cn_details", tout <<  "es[" << k << "]= " << es[k] << "\n";);
        interv b = interval_of_expr(es[k]);
        if (m_intervals.is_inf(b)) {
            TRACE("nla_cn_details", tout << "got inf\n";);
            return b;
        }
        interv c;
        interval_deps deps;
        TRACE("nla_cn_details", tout << "a = "; m_intervals.display(tout, a) << "\nb = "; m_intervals.display(tout, b) << "\n";);
        m_intervals.add(a, b, c, deps);
        TRACE("nla_cn_details", tout << "c = "; m_intervals.display(tout, c); tout << "\n";);
        m_intervals.set(a, c);
        TRACE("nla_cn_details", tout << "a = "; m_intervals.display(tout, a); tout << "\n";);
        
        m_intervals.add_deps(a, b, deps, a);
        TRACE("nla_cn_details", tout << "final a with deps = "; m_intervals.display(tout, a); tout << "\n";);
        if (m_intervals.is_inf(a)) {
            TRACE("nla_cn_details", tout << "got infinity\n";);            
            return a;
        }
    }
    return a;
}
// sets the dependencies also
void horner::set_var_interval(lpvar v, interv& b) {
    m_intervals.set_var_interval_with_deps(v, b);
    
    TRACE("nla_cn_details", tout << "v = "; print_var(v, tout) << "\n"; m_intervals.display(tout, b)<< '\n';);
    
}
}
 auto i = interval_of_expr(e);
                m_intervals.check_interval_for_conflict_on_zero(i);
