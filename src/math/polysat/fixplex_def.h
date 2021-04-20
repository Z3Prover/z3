/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    fixplex_def.h

Abstract:

    Fixed-precision unsigned integer simplex tableau.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#pragma once

#include "math/polysat/fixplex.h"
#include "math/simplex/sparse_matrix_def.h"

namespace polysat {

    template<typename Ext>
    fixplex<Ext>::~fixplex() {
        reset();
    }    
    
    template<typename Ext>
    void fixplex<Ext>::ensure_var(var_t v) {
        while (v >= m_vars.size()) {
            M.ensure_var(m_vars.size());
            m_vars.push_back(var_info());            
        }
        if (m_to_patch.get_bounds() <= v) 
            m_to_patch.set_bounds(2*v+1);
    }

    template<typename Ext>
    void fixplex<Ext>::reset() {
        M.reset();
        m_to_patch.reset();
        m_vars.reset();
        m_row2base.reset();
        m_left_basis.reset();
        m_base_vars.reset();
    }

    template<typename Ext>
    lbool fixplex<Ext>::make_feasible() {
        ++m_stats.m_num_checks;
        m_left_basis.reset();
        m_infeasible_var = null_var;
        unsigned num_iterations = 0;
        unsigned num_repeated = 0;
        var_t v = null_var;
        m_bland = false;
        SASSERT(well_formed());
        while ((v = select_var_to_fix()) != null_var) {
            TRACE("simplex", display(tout << "v" << v << "\n"););
            if (!m_limit.inc() || num_iterations > m_max_iterations) {
                return l_undef;
            }
            check_blands_rule(v, num_repeated);
            if (!make_var_feasible(v)) {
                m_to_patch.insert(v);
                m_infeasible_var = v;
                ++m_stats.m_num_infeasible;
                return l_false;
            }
            ++num_iterations;
        }
        SASSERT(well_formed());
        return l_true;
    }

    template<typename Ext>
    typename fixplex<Ext>::row 
    fixplex<Ext>::add_row(var_t base_var, unsigned num_vars, var_t const* vars, numeral const* coeffs) {
        m_base_vars.reset();
        row r = M.mk_row();
        for (unsigned i = 0; i < num_vars; ++i) 
            if (coeffs[i] != 0)                 
                M.add_var(r, coeffs[i], vars[i]);

        numeral base_coeff = 0;
        numeral value = 0;
        for (auto const& e : M.row_entries(r)) {
            var_t v = e.m_var;
            if (v == base_var) 
                base_coeff = e.m_coeff;
            else {
                if (is_base(v))
                    m_base_vars.push_back(v);
                value += e.m_coeff * m_vars[v].m_value;
            }
        }
        SASSERT(base_coeff != 0);
        SASSERT(!is_base(base_var));
        while (m_row2base.size() <= r.id()) 
            m_row2base.push_back(null_var);
        m_row2base[r.id()] = base_var;
        m_vars[base_var].m_base2row = r.id();
        m_vars[base_var].m_is_base = true;
        m_vars[base_var].m_base_coeff = base_coeff;
        m_vars[base_var].m_value = value / base_coeff;
        // TBD: record when base_coeff does not divide value
        add_patch(base_var);
        if (!m_base_vars.empty()) {
            gauss_jordan();
        }
        SASSERT(well_formed_row(r));
        SASSERT(well_formed());
        return r;
    }

    template<typename Ext>
    void fixplex<Ext>::gauss_jordan() {
        while (!m_base_vars.empty()) {
            auto v = m_base_vars.back();
            auto rid = m_vars[v].m_base2row;
#if 0
            auto const& row = m_rows[rid];
            make_basic(v, row);
#endif
        }
    }

    /**
     * make v a basic variable.
     * If v is already a basic variable in preferred_row, skip
     * If v
     */

    template<typename Ext>
    void fixplex<Ext>::make_basic(var_t v, row const& preferred_row) {
        numeral c1 = 0;
        for (auto const& e : M.row_entries(preferred_row)) {
            if (e.m_var == v) {
                c1 = e.m_coeff;
                break;
            }                    
        }
        auto c2 = m_vars[v].m_base_coeff;
        auto r2 = m_vars[v].m_base2row;
        unsigned exp1 = trailing_zeros(c1); // exponent of two for v in r
        unsigned exp2 = trailing_zeros(c2); // exponent of two for v in r2
        if (exp1 >= exp2) {
            // eliminate v from r
        }
        else {
            // eliminate v from r2, 
            // make v the new base for r
            // perform gauss-jordan for both r and r2 (add to queue)
        }

        NOT_IMPLEMENTED_YET();
        
    }


#if 0
    /**
       \brief Make x_j the new base variable for row of x_i.
       x_i is assumed base variable of row r_i.
       x_j is assumed to have coefficient a_ij in r_i.                      

       a_ii*x_i + a_ij*x_j + r_i = 0
       
       current value of x_i is v_i
       new value of x_i is     new_value
       a_ii*(x_i + new_value - x_i) + a_ij*((x_i - new_value)*a_ii/a_ij + x_j) + r_i = 0

       Let r_k be a row where x_j has coefficient x_kj != 0.
       r_k <- r_k * a_ij - r_i * a_kj
    */
    template<typename Ext>
    void fixplex<Ext>::update_and_pivot(var_t x_i, var_t x_j, numeral const& a_ij, numeral const& new_value) {
        SASSERT(is_base(x_i));
        SASSERT(!is_base(x_j));
        var_info& x_iI = m_vars[x_i];
        numeral const& a_ii = x_iI.m_base_coeff;
        auto theta = x_iI.m_value - new_value;
        theta *= a_ii;
        theta /= a_ij;
        update_value(x_j, theta);
        SASSERT(new_value == x_iI.m_value);
        pivot(x_i, x_j, a_ij);
    }
    
    template<typename Ext>
    void fixplex<Ext>::pivot(var_t x_i, var_t x_j, numeral const& a_ij) {
        ++m_stats.m_num_pivots;
        var_info& x_iI = m_vars[x_i];
        var_info& x_jI = m_vars[x_j];
        unsigned r_i = x_iI.m_base2row;
        m_row2base[r_i] = x_j;
        x_jI.m_base2row = r_i;
        x_jI.m_base_coeff = a_ij;
        x_jI.m_is_base = true;
        x_iI.m_is_base = false;
        add_patch(x_j);
        SASSERT(well_formed_row(row(r_i)));

        col_iterator it = M.col_begin(x_j), end = M.col_end(x_j);
        scoped_numeral a_kj(m), g(m);
        for (; it != end; ++it) {
            row r_k = it.get_row();
            if (r_k.id() != r_i) {
                a_kj = it.get_row_entry().m_coeff;
                a_kj.neg();
                M.mul(r_k, a_ij);
                M.add(r_k, a_kj, row(r_i));
                var_t s = m_row2base[r_k.id()];
                numeral& coeff = m_vars[s].m_base_coeff;
                m.mul(coeff, a_ij, coeff);
                M.gcd_normalize(r_k, g);
                if (!m.is_one(g)) {
                    m.div(coeff, g, coeff);
                }
                SASSERT(well_formed_row(row(r_k)));
            }
        }
        SASSERT(well_formed());
    }

    template<typename Ext>
    void fixplex<Ext>::update_value(var_t v, eps_numeral const& delta) {
        if (em.is_zero(delta)) {
            return;
        }
        update_value_core(v, delta);
        col_iterator it = M.col_begin(v), end = M.col_end(v);

        // v <- v + delta
        // s*s_coeff + v*v_coeff + R = 0
        // -> 
        // (v + delta)*v_coeff + (s - delta*v_coeff/s_coeff)*v + R = 0
        for (; it != end; ++it) {
            row r = it.get_row();
            var_t s = m_row2base[r.id()];
            var_info& si = m_vars[s];
            scoped_eps_numeral delta2(em);
            numeral const& coeff = it.get_row_entry().m_coeff;
            em.mul(delta,  coeff, delta2);
            em.div(delta2, si.m_base_coeff, delta2);
            delta2.neg();
            update_value_core(s, delta2);
        }            
    }    

    template<typename Ext>
    void fixplex<Ext>::update_value_core(var_t v, eps_numeral const& delta) {
        eps_numeral& val = m_vars[v].m_value;
        em.add(val, delta, val);
        if (is_base(v)) {
            add_patch(v);
        }
    }
#endif

}

