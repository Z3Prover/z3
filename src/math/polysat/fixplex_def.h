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
        m_rows.reset();
        m_left_basis.reset();
        m_base_vars.reset();

        // pivot(0,1, 2);
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
        while (m_rows.size() <= r.id()) 
            m_rows.push_back(row_info());
        m_rows[r.id()].m_base = base_var;
        m_rows[r.id()].m_base_coeff = base_coeff;
        m_rows[r.id()].m_value = value;
        m_vars[base_var].m_base2row = r.id();
        m_vars[base_var].m_is_base = true;
        m_vars[base_var].m_value = 0 - (value / base_coeff);
        // TBD: record when base_coeff does not divide value
        add_patch(base_var);
        if (!m_base_vars.empty()) {
            gauss_jordan();
        }
        SASSERT(well_formed_row(r));
        SASSERT(well_formed());
        return r;
    }


    /**
     * increment v by delta
     */
    template<typename Ext>
    void fixplex<Ext>::update_value(var_t v, numeral const& delta) {
        if (delta == 0)
            return;
        m_vars[v].m_value += delta;
        SASSERT(!is_base(v));

        //
        // v <- v + delta
        // s*s_coeff + R = 0, where R contains v*v_coeff 
        // -> 
        // R.value += delta*v_coeff
        // s.value = - R.value / s_coeff
        // 
        for (auto c : M.col_entries(v)) {
            row r = c.get_row();
            row_info& ri = m_rows[r.id()];
            var_t s = ri.m_base;
            ri.m_value += delta * c.get_row_entry().m_coeff;
            m_vars[s].m_value = 0 - (ri.m_value / ri.m_base_coeff);
            add_patch(s);
        }            
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
     * If v is already a basic variable in preferred_row, skip
     * If v is non-basic but basic in a different row, then 
     *      eliminate v from one of the rows.
     * If v if non-basic
     */

    template<typename Ext>
    void fixplex<Ext>::make_basic(var_t v, row const& preferred_row) {

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
#endif
    
    template<typename Ext>
    void fixplex<Ext>::pivot(var_t x_i, var_t x_j, numeral a_ij) {
        ++m_stats.m_num_pivots;
        var_info& x_iI = m_vars[x_i];
        var_info& x_jI = m_vars[x_j];
        unsigned ri = x_iI.m_base2row;
        m_rows[ri].m_base = x_j;
        m_rows[ri].m_value = 0; // TBD
        m_rows[ri].m_base_coeff = a_ij;
        x_jI.m_base2row = ri;
        x_jI.m_is_base = true;
        x_iI.m_is_base = false;
        row r_i(ri);
        add_patch(x_j);
        SASSERT(well_formed_row(r_i));

        unsigned tz1 = trailing_zeros(a_ij);

        for (auto c : M.col_entries(x_j)) {
            row r_k = c.get_row();
            unsigned rk = r_k.id();
            if (rk == ri)
                continue;

            numeral a_kj = c.get_row_entry().m_coeff;
            unsigned tz2 = trailing_zeros(a_kj);
            if (tz2 >= tz1) {
                // eliminate x_j from row r_k
                numeral a = a_ij >> tz1;
                numeral b = m.inv(a_kj >> (tz2 - tz1));
                M.mul(r_k, a);
                M.add(r_k, b, r_i);
            }
            else {
                // eliminate x_j from row r_i
                // The new base variable for r_i is base of r_k
                // The new base variable for r_k is x_j.
                
                numeral a = a_kj >> tz2;
                numeral b = m.inv(a_ij >> (tz1 - tz2));
                M.mul(r_i, a);
                M.add(r_i, b, r_k);
                unsigned x_k = m_rows[rk].m_base;
                
                // TBD: redo according to slides
                // TBD: std::swap(m_row2base[ri], m_row2base[rk]);
                m_vars[x_j].m_base2row = rk;
                m_vars[x_k].m_base2row = ri;
                tz1  = tz2;
                r_i  = r_k;
                ri   = rk;
                a_ij = a_kj;
            }
            // TBD: should we here recalculate value of basic variables?
            SASSERT(well_formed_row(r_k));
        }
        SASSERT(well_formed());
    }


}

