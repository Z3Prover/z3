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
    if (row.size() <= 1)
        return false;
    for (const auto& p : row) {
        if (c().m_to_refine.contains(p.var()))
            return true;
    }
    return false;
}

void horner::lemmas_on_expr(nex& e) {
    vector<nex*> front;
    front.push_back(&e);
    cross_nested_of_expr(e, front);

}

void horner::cross_nested_of_expr(nex& e, vector<nex*> & front) {
    TRACE("nla_cn", tout << "e = " << e << ", front has " << front.size() << "\n";);
    if (front.empty()) {
        auto i = interval_of_expr(e);
        m_intervals.check_interval_for_conflict_on_zero(i);
    }
    nex & c = *(front.back());
    front.pop_back();
    TRACE("nla_cn", tout << "pop from front\n";);
    cross_nested_of_expr_on_front_elem(e, c, front);    
}

void horner::cross_nested_of_expr_on_front_elem(nex& e, nex& c, vector<nex*> & front) {
    SASSERT(c.is_sum());
    std::unordered_map<unsigned, lpvar> occurences;
    TRACE("nla_cn", tout << "c = " << c << "\n";);
    get_occurences_map(c, occurences);
    nex copy_of_c(c);
    for(const auto & p : occurences) {
        TRACE("nla_cn", tout << "v" << p.first << ", " << p.second << "\n";);
        if (p.second < 2)
            continue;
        cross_nested_of_expr_on_sum_and_var(e, c, p.first, front);
        c = copy_of_c;
    }
    TRACE("nla_cn", tout << "exit\n";);
}
// e is the global expression, c is the sub expressiond which is going to changed from sum to the cross nested form
void horner::cross_nested_of_expr_on_sum_and_var(nex& e, nex& c, lpvar j, vector<nex*> & front) {
    TRACE("nla_cn", tout << "e=" << e << "\nc = " << c << "\nj = v" << j << "\n";);
    split_with_var(c, j, front);
    cross_nested_of_expr(e, front);
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


// j -> the number of expressions j appears in as a multiplier
void horner::get_occurences_map(const nla_expr<rational>& e, std::unordered_map<lpvar, unsigned>& occurences) const {
    SASSERT(e.type() == expr_type::SUM);
    for (const auto & ce : e.children()) {
        std::unordered_set<lpvar> seen;
        if (ce.type() == expr_type::MUL) {
            for (const auto & cce : ce.children()) {
                if (cce.type() ==  expr_type::VAR) {
                    process_var_occurences(cce.var(), seen, occurences);
                } else if (cce.type() == expr_type::MUL) {
                    process_mul_occurences(cce, seen, occurences);
                } else {
                    continue;
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
    TRACE("nla_cn_details",
          tout << "{";
          for(auto p: occurences) {
              tout << "(v" << p.first << "->" << p.second << ")";
          }
          tout << "}" << std::endl;);    
}

void horner::split_with_var(nex& e, lpvar j, vector<nex*> & front) {
    TRACE("nla_cn", tout << "e = " << e << ", j = v" << j << "\n";);
    if (!e.is_sum())
        return;
    nex a, b;
    for (const nex & ce: e.children()) {
        if ((ce.is_mul() && ce.contains(j)) || (ce.is_var() && ce.var() == j)) {
            a.add_child(ce / j);
        } else {
            b.add_child(ce);
        }        
    }
    a.type() = expr_type::SUM;
    TRACE("nla_cn", tout << "a = " << a << "\n";);
    SASSERT(a.children().size() >= 2);
    
    if (b.children().size() == 1) {
        nex t = b.children()[0];
        b = t;      
    } else if (b.children().size() > 1) {
        b.type() = expr_type::SUM;        
    }

    if (b.is_undef()) {
        SASSERT(b.children().size() == 0);
        e = nex(expr_type::MUL);        
        e.add_child(nex::var(j));
        e.add_child(a);
        if (a.size() > 1) {
            front.push_back(&e.children().back());
            TRACE("nla_cn", tout << "push to front " << e.children().back() << "\n";);
        }
      
    } else {
        TRACE("nla_cn", tout << "b = " << b << "\n";);
        e = nex::sum(nex::mul(nex::var(j), a), b);
        if (a.is_sum()) {
            front.push_back(&(e.children()[0].children()[1]));
            TRACE("nla_cn", tout << "push to front " << e.children()[0].children()[1] << "\n";);
        }
        if (b.is_sum()) {
            front.push_back(&(e.children()[1]));
            TRACE("nla_cn", tout << "push to front " << e.children()[1] << "\n";);
}
    }
}

nex horner::cross_nested_of_sum(const nex& e, lpvar j) {
    if (!e.is_sum())
        return e;
    /*
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
    return ret;*/
    SASSERT(false);
    return nex();
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

std::set<lpvar> horner::get_vars_of_expr(const nex &e ) const {
    std::set<lpvar> r;
    switch (e.type()) {
    case expr_type::SCALAR:
        return r;
    case expr_type::SUM:
    case expr_type::MUL:
        {
            for (const auto & c: e.children())
                for ( lpvar j : get_vars_of_expr(c))
                    r.insert(j);
        }
        return r;
    case expr_type::VAR:
        r.insert(e.var());
        return r;
    default:
        TRACE("nla_cn_details", tout << e.type() << "\n";);
        SASSERT(false);
        return r;
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
