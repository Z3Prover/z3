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

namespace nla {
typedef nla_expr<rational> nex;
typedef intervals::interval interv;
horner::horner(core * c) : common(c), m_intervals(c, c->reslim()) {}

template <typename T>
bool horner::row_is_interesting(const T& row) const {
    for (const auto& p : row) {
        if (c().m_to_refine.contains(p.var()))
            return true;
    }
    return false;
}

template <typename T> 
void horner::lemma_on_row(const T& row) {
    if (!row_is_interesting(row))
        return;
    nex e = create_expr_from_row(row);
    TRACE("nla_cn_details", tout << "cross nested e = " << e << std::endl;);
    interv a = interval_of_expr(e);
    TRACE("nla_cn_details", tout << "interval a = ";  m_intervals.display(tout, a) << "\n";);
    check_interval_for_conflict(a, row);
}

void horner::horner_lemmas() {
    if (!c().m_settings.run_horner()) {
        TRACE("nla_solver", tout << "not generating horner lemmas\n";);
        return;
    }

    const auto& m = c().m_lar_solver.A_r();
    unsigned r = random();
    unsigned s = m.row_count();
    for (unsigned i = 0; i < s && !done() ; i++) {
        lemma_on_row(m.m_rows[((i + r) % s)]);
    }
}

nex horner::nexvar(lpvar j) const {
    if (!c().is_monomial_var(j))
        return nex::var(j);
    const monomial& m = c().emons()[j];
    nex e(expr_type::MUL);
    for (lpvar k : m.vars()) {
        e.add_child(nex::var(k));
    }
    return e;
}

void process_var_occurences(lpvar j, std::unordered_set<lpvar>& seen, std::unordered_map<lpvar, unsigned>& occurences) {
    if (seen.find(j) != seen.end()) return;
    seen.insert(j);
    auto it = occurences.find(j);
    if (it == occurences.end())
        occurences[j] = 1;
    else
        it->second ++;
}

void process_mul_occurences(const nex& e, std::unordered_set<lpvar>& seen, std::unordered_map<lpvar, unsigned>& occurences) {
    SASSERT(e.type() == expr_type::MUL);
    for (const auto & ce : e.children()) {
        if (ce.type() == expr_type::SCALAR) {
        } else  if (ce.type() ==  expr_type::VAR) {
            process_var_occurences(ce.var(), seen, occurences);
        } else if (ce.type() ==  expr_type::MUL){
            process_mul_occurences(ce, seen, occurences);
        } else {        
            SASSERT(false); // unexpected type
        }
    }
}

// return a valid j if some variable appears more than once
unsigned horner::random_most_occured_var(std::unordered_map<lpvar, unsigned>& occurences)  {
    unsigned max = 0;
    unsigned ret = -1;
    unsigned n = 0;
    for (const auto & p : occurences) {
        if (p.second > max) {
            n = 0;
            max = p.second;
            ret = p.first;
        } else if (p.second == max) {
            n++;
            if (random() % n == 0) {
                ret = p.first;
            }
        } 
    }
    if (max <= 1)
        return -1;
    SASSERT(ret + 1);
    return ret;
}


// j -> the number of expressions j appears in
void horner::get_occurences_map(const nla_expr<rational>& e, std::unordered_map<lpvar, unsigned>& occurences) const {
    TRACE("nla_cn_details", tout << "e = " << e << std::endl;);    
    SASSERT(e.type() == expr_type::SUM);
    for (const auto & ce : e.children()) {
        std::unordered_set<lpvar> seen;
        if (ce.type() == expr_type::MUL) {
            for (const auto & cce : ce.children()) {
                if (cce.type() == expr_type::SCALAR) {
                }  else  if (cce.type() ==  expr_type::VAR) {
                    process_var_occurences(cce.var(), seen, occurences);
                } else if (cce.type() == expr_type::MUL) {
                    process_mul_occurences(cce, seen, occurences);
                } else {
                    TRACE("nla_cn_details", tout << "e = " << e << "\nce = " << ce << std::endl <<
                          "ce type = " << ce.type() << std::endl;);
                    
                    SASSERT(false); // unexpected type
                }
            }
        } else if (ce.type() ==  expr_type::VAR) {
            process_var_occurences(ce.var(), seen, occurences);
        } else if (ce.type() == expr_type::SCALAR) {
        } else {            
            TRACE("nla_cn_details", tout << "unexpected expression ce = " << ce << std::endl;);            
            SASSERT(false);
        }
    }
}

nex horner::split_with_var(const nex& e, lpvar j) {
    TRACE("nla_cn_details", tout << "e = " << e << ", j = v" << j << "\n";);
    if (!e.is_sum())
        return e;
    nex a, b;
    for (const nex & ce: e.children()) {
        if (ce.is_mul() && ce.contains(j)) {
            a.add_child(ce / j);
        } else {
            b.add_child(ce);
        }        
    }
    if (a.children().size() == 1)
        return e;
    SASSERT(a.children().size());
    a.type() = expr_type::SUM;
    
    if (b.children().size() == 1) {
        nex t = b.children()[0];
        b = t;      
    } else if (b.children().size() > 1) {
        b.type() = expr_type::SUM;
    }

    if (b.is_undef()) {
        SASSERT(b.children().size() == 0);
        nex r(expr_type::MUL);        
        r.add_child(nex::var(j));
        r.add_child(cross_nested_of_sum(a));
        return r;
    }
    TRACE("nla_cn_details", tout << "b = " << b << "\n";);
    return nex::sum(nex::mul(cross_nested_of_sum(a), nex::var(j)), cross_nested_of_sum(b));    
}

nex horner::cross_nested_of_sum(const nex& e) {
    if (!e.is_sum())
        return e;
    std::unordered_map<lpvar, unsigned>  occurences;
    get_occurences_map(e, occurences);
    lpvar j = random_most_occured_var(occurences);
    if (j + 1 == 0) return e;
    TRACE("nla_cn_details",
          tout << "e = "  << e << "\noccurences ";
          for (auto p : occurences){
              tout << "(v"<<p.first << ", "<< p.second<<")";
          }
          tout << std::endl << "most occured = v" << j << std::endl;);
    nex ret = split_with_var(e, j);
    TRACE("nla_cn_details", tout << "ret =" << ret << "\n";);
    return ret;
}

template <typename T> nex horner::create_expr_from_row(const T& row) {
    TRACE("nla_cn", tout << "row="; m_core->print_term(row, tout) << "\n";
          for (const auto & p : row) {
              print_var(p.var(), tout);
          }
          tout << "\n";
          );
    nex e;
    if (row.size() > 1) {
        e.type() = expr_type::SUM;
        for (const auto &p : row) {
            e.add_child(nex::mul(p.coeff(), nexvar(p.var())));
        }
        return cross_nested_of_sum(e);
    }
    if (row.size() == 1) {
        const auto &p  = *row.begin();
        return nex::mul(p.coeff(), nexvar(p.var()));
    }
    std::cout << "ops\n";
    SASSERT(false);
    return e;
}

template <typename T>
void horner::set_interval_for_scalar(interv& a, const T& v) {
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
template <typename T>
interv horner::interval_of_mul(const vector<nla_expr<T>>& es) {    
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

template <typename T>
interv horner::interval_of_sum(const vector<nla_expr<T>>& es) {
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
template <typename T> 
void horner::check_interval_for_conflict(const interv& i, const T& row) {
    if (m_intervals.check_interval_for_conflict_on_zero(i)) {
        TRACE("nla_cn", print_lemma(tout););
    }
}
}
