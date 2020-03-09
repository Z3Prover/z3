/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner
  Lev Nachmanson
      
*/
#pragma once
#include "math/lp/lp_settings.h"
#include "util/vector.h"
#include "math/lp/lar_solver.h"
#include "math/lp/nla_defs.h"
namespace nla {
/*
 *  represents definition m_v = v1*v2*...*vn, 
 *  where m_vs = [v1, v2, .., vn]
 */

class mon_eq {
    // fields
    lp::var_index          m_v;
    svector<lp::var_index> m_vs;
public:
    // constructors
    mon_eq(lp::var_index v, unsigned sz, lp::var_index const* vs):
        m_v(v), m_vs(sz, vs) {
        std::sort(m_vs.begin(), m_vs.end());
    }
    mon_eq(lp::var_index v, const svector<lp::var_index> &vs):
        m_v(v), m_vs(vs) {
        std::sort(m_vs.begin(), m_vs.end());
    }
    mon_eq() {}
        
    unsigned var() const { return m_v; }
    unsigned size() const { return m_vs.size(); }
    const svector<lp::var_index>& vars() const { return m_vs; }
    svector<lp::var_index>& vars() { return m_vs; }
    bool empty() const { return m_vs.empty(); }
};

// support the congruence    
class monic: public mon_eq {
    // fields
    svector<lpvar>  m_rvars;
    bool            m_rsign;
    mutable unsigned m_visited;
public:
    // constructors
    monic(lpvar v, unsigned sz, lpvar const* vs, unsigned idx):  monic(v, svector<lpvar>(sz, vs), idx) {
    }
    monic(lpvar v, const svector<lpvar> &vs, unsigned idx) : mon_eq(v, vs), m_rsign(false),  m_visited(0) {
        std::sort(vars().begin(), vars().end());
    }

    unsigned visited() const { return m_visited; }
    unsigned& visited() { return m_visited; }
    svector<lpvar> const& rvars() const { return m_rvars; }
    bool rsign() const { return m_rsign; }
    void reset_rfields() { m_rsign = false; m_rvars.reset(); SASSERT(m_rvars.size() == 0); }
    void push_rvar(signed_var sv) { m_rsign ^= sv.sign(); m_rvars.push_back(sv.var()); }
    void sort_rvars() {
        std::sort(m_rvars.begin(), m_rvars.end());
    }
};

 inline std::ostream& operator<<(std::ostream& out, monic const& m) {
     return out << m.var() << " := " << m.vars() << " r ( " << sign_to_rat(m.rsign()) << " * " << m.rvars() << ")";
 }


typedef std::unordered_map<lpvar, rational> variable_map_type;
template <typename T>
bool check_assignment(T const& m, variable_map_type & vars);
template <typename K>
bool check_assignments(const K & monomimials,
                       const lp::lar_solver& s,
                       variable_map_type & vars);

} // end of namespace nla
