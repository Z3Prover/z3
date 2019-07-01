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

namespace nla {
typedef nla_expr<rational> nex;
typedef intervals::interval interv;
horner::horner(core * c) : common(c), m_intervals(c->reslim()) {}

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
    TRACE("nla_cn", tout << "cross nested e = " << e << std::endl;);
    intervals::interval inter = interval_of_expr(e);
    check_interval_for_conflict(inter);
}

void horner::horner_lemmas() {
    if (!c().m_settings.run_horner()) {
        TRACE("nla_solver", tout << "not generating horner lemmas\n";);
        return;
    }

    const auto& m = c().m_lar_solver.A_r();
    unsigned r = random();
    unsigned s = m.row_count();
    for (unsigned i = 0; i < s && !done(); i++) {
        lemma_on_row(m.m_rows[((i + r) %s)]);
    }
    
    SASSERT(false);
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
        }  else  if (ce.type() ==  expr_type::VAR) {
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
                    TRACE("nla_cn", tout << "e = " << e << "\nce = " << ce << std::endl <<
                          "ce type = " << ce.type() << std::endl;);
                    
                    SASSERT(false); // unexpected type
                }
            }
        } else if (ce.type() ==  expr_type::VAR) {
            process_var_occurences(ce.var(), seen, occurences);
        } else {
            SASSERT(false);
        }
    }
}

nex horner::split_with_var(const nex& e, lpvar j) {
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
        b = b.children()[0];      
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
    return nex::sum(nex::mul(cross_nested_of_sum(a), nex::var(j)), b);    
}

nex horner::cross_nested_of_sum(const nex& e) {
    if (!e.is_sum())
        return e;
    std::unordered_map<lpvar, unsigned>  occurences;
    get_occurences_map(e, occurences);
    lpvar j = random_most_occured_var(occurences);
    if (j + 1 == 0) return e;
    TRACE("nla_cn",
          tout << "e = "  << e << "\noccurences ";
          for (auto p : occurences){
              tout << "(v"<<p.first << ", "<< p.second<<")";
          }
          tout << std::endl << "most occured = v" << j << std::endl;);
    return split_with_var(e, j);
}

template <typename T> nex horner::create_expr_from_row(const T& row) {
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
    SASSERT(false);
}
intervals::interval horner::interval_of_expr(const nex& e) {
    interv a;
    switch (e.type()) {
    case expr_type::SCALAR:
        m_intervals.set_lower(a, e.value());
        m_intervals.set_upper(a, e.value());
        return a;
    case expr_type::SUM:
        return interval_of_sum(e.children());
    case expr_type::MUL:
        return interval_of_mul(e.children());
    case expr_type::VAR:
        return interval_of_var(e.var());                               
    default:
        TRACE("nla_cn", tout << e.type() << "\n";);
        SASSERT(false);
        return e;
    }
}

void horner::set_var_interval(lpvar v, interv& b) {
    const auto& ls = c().m_lar_solver;
    lp::constraint_index ci;
    rational val;
    bool is_strict;
    if (ls.has_lower_bound(v, ci, val, is_strict)) {            
        m_intervals.set_lower(b, val);
        m_intervals.set_lower_is_open(b, is_strict);
        m_intervals.set_lower_is_inf(b, false);
    }
    else {
        m_intervals.set_lower_is_open(b, true);
        m_intervals.set_lower_is_inf(b, true);
    }
    if (ls.has_upper_bound(v, ci, val, is_strict)) {
        m_intervals.set_upper(b, val);
        m_intervals.set_upper_is_open(b, is_strict);
        m_intervals.set_upper_is_inf(b, false);
    }
    else {
        m_intervals.set_upper_is_open(b, true);
        m_intervals.set_upper_is_inf(b, true);
    }
}

void horner::check_interval_for_conflict(const intervals::interval&) {
    SASSERT(false);
}
}
