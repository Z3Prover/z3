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
horner::horner(core * c) : common(c) {}

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


nex horner::cross_nested_of_sum(const nla_expr<rational>& e) const {
    SASSERT(e.type() == expr_type::SUM);
    std::unordered_map<lpvar, unsigned>  occurences;
    get_occurences_map(e, occurences);
    TRACE("nla_cn",
          tout << "e = "  << e << "\noccurences ";
          for (auto p : occurences){
              tout << "(v"<<p.first << ", "<< p.second<<")";
          }
          tout << std::endl;);
    SASSERT(false);    
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
    
    SASSERT(false);
}
void horner::check_interval_for_conflict(const intervals::interval&) {
    SASSERT(false);
}
}
