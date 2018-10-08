/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner
*/
#pragma once
#include "util/lp/lp_settings.h"
#include "util/vector.h"
#include "util/lp/lar_solver.h"

namespace nla {
    /*
     *  represents definition m_v = v1*v2*...*vn, 
     *  where m_vs = [v1, v2, .., vn]
     */
    class monomial {
        // fields
        lp::var_index          m_v;
        svector<lp::var_index> m_vs;
    public:
        // constructors
        monomial(lp::var_index v, unsigned sz, lp::var_index const* vs):
           m_v(v), m_vs(sz, vs) {}
        monomial(lp::var_index v, const svector<lp::var_index> &vs):
           m_v(v), m_vs(vs) {}
        monomial() {}
        
        unsigned var() const { return m_v; }
        unsigned size() const { return m_vs.size(); }
        unsigned operator[](unsigned idx) const { return m_vs[idx]; }
        svector<lp::var_index>::const_iterator begin() const { return m_vs.begin(); }
        svector<lp::var_index>::const_iterator end() const { return m_vs.end(); }
        const svector<lp::var_index> vars() const { return m_vs; }
    };

    typedef std::unordered_map<lp::var_index, rational> variable_map_type;
    
    bool check_assignment(monomial const& m, variable_map_type & vars);
    
    bool check_assignments(const vector<monomial> & monomimials,
                           const lp::lar_solver& s,
                           variable_map_type & vars);



    /*
     *  represents definition m_v = coeff* v1*v2*...*vn, 
     *  where m_vs = [v1, v2, .., vn]
     */
    class monomial_coeff : public monomial {
        rational m_coeff;
    public:
        monomial_coeff(monomial const& eq, rational const& coeff):
            monomial(eq), m_coeff(coeff) {}

        monomial_coeff(lp::var_index v, const svector<lp::var_index> &vs, rational const& coeff):
            monomial(v, vs),
            m_coeff(coeff) {}

       rational const& coeff() const { return m_coeff; }
    };

}
