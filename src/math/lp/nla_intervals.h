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
#pragma once
#include "util/dependency.h"
#include "util/region.h"
#include "math/lp/nla_common.h"
#include "math/lp/lar_solver.h"
#include "math/interval/interval.h"
#include "math/interval/dep_intervals.h"
#include "util/dependency.h"

namespace nla {
class core;

class intervals {
    mutable dep_intervals     m_dep_intervals;
    core*                     m_core;
    
public:
    typedef dep_intervals::interval interval;
private:
    u_dependency* mk_dep(lp::constraint_index ci);
    u_dependency* mk_dep(lp::explanation const&);
    lp::lar_solver& ls();
    const lp::lar_solver& ls() const;
public:

    intervals(core* c, reslimit& lim) :
        m_dep_intervals(lim),
        m_core(c)
    {}
    dep_intervals& get_dep_intervals() { return m_dep_intervals; }
    u_dependency* mk_join(u_dependency* a, u_dependency* b) { return m_dep_intervals.mk_join(a, b); }
    u_dependency* mk_leaf(lp::constraint_index ci) { return m_dep_intervals.mk_leaf(ci); }

    std::ostream& print_dependencies(u_dependency*, std::ostream&) const;
    std::ostream& display(std::ostream& out, const intervals::interval& i) const;
    void set_lower(interval& a, rational const& n) const { m_dep_intervals.set_lower(a, n.to_mpq()); }
    void set_upper(interval& a, rational const& n) const { m_dep_intervals.set_upper(a, n.to_mpq()); }
    void set_lower_is_open(interval& a, bool strict) { m_dep_intervals.set_lower_is_open(a, strict); }
    void set_lower_is_inf(interval& a, bool inf) { m_dep_intervals.set_lower_is_inf(a, inf); }
    void set_upper_is_open(interval& a, bool strict) { m_dep_intervals.set_upper_is_open(a, strict); }
    void set_upper_is_inf(interval& a, bool inf) { m_dep_intervals.set_upper_is_inf(a, inf); }
    bool is_zero(const interval& a) const { return m_dep_intervals.is_zero(a); }

    template <dep_intervals::with_deps_t wd>
    void set_var_interval(lpvar v, interval& b);

    template <dep_intervals::with_deps_t wd>
    bool interval_from_term(const nex& e, interval& i); 


    template <dep_intervals::with_deps_t wd>
    interval interval_of_sum_no_term(const nex_sum& e);

    template <dep_intervals::with_deps_t wd>
    interval interval_of_sum(const nex_sum& e);

    template <dep_intervals::with_deps_t wd>
    interval interval_of_mul(const nex_mul& e); 

    template <dep_intervals::with_deps_t wd>
    interval interval_of_expr(const nex* e, unsigned p); 
    bool upper_is_inf(const interval& a) const { return m_dep_intervals.upper_is_inf(a); }
    bool lower_is_inf(const interval& a) const { return m_dep_intervals.lower_is_inf(a); }

    void set_zero_interval_deps_for_mult(interval&);
    void set_zero_interval_with_explanation(interval&, const lp::explanation& exp);
    void set_zero_interval(interval&);
    bool is_inf(const interval& i) const { return m_dep_intervals.is_inf(i); }

    bool check_nex(const nex*, u_dependency*);
    const nex* get_zero_interval_child(const nex_mul&) const;
    const nex* get_inf_interval_child(const nex_sum&) const;
    bool has_zero_interval(const nex&) const;
    bool has_inf_interval(const nex&) const;
    bool mul_has_inf_interval(const nex_mul&) const;
    static lp::lar_term expression_to_normalized_term(const nex_sum*, rational& a, rational& b);
    static void add_linear_to_vector(const nex*, vector<std::pair<rational, lpvar>>&);
    static void add_mul_of_degree_one_to_vector(const nex_mul*, vector<std::pair<rational, lpvar>>&);
    lpvar find_term_column(const lp::lar_term&, rational& a) const;
}; // end of intervals
} // end of namespace nla
