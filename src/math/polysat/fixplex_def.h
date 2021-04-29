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

    template<typename Ext>
    bool fixplex<Ext>::in_bounds(var_t v) const {
        auto lo = m_vars[v].m_lo;
        auto hi = m_vars[v].m_hi;
        if (lo == hi)
            return true;
        auto val = m_vars[v].m_value;
        if (lo < hi)
            return lo <= val && val < hi;
        return val < hi || lo <= val;
    }

    template<typename Ext>
    typename fixplex<Ext>::numeral fixplex<Ext>::new_value(var_t v) const {
        auto lo = m_vars[v].m_lo;
        auto hi = m_vars[v].m_hi;
        auto val = m_vars[v].m_value;
        if ((lo - val) < (val - hi))
            return lo;
        else
            return hi;
    }

    template<typename Ext>
    bool fixplex<Ext>::make_var_feasible(var_t x_i) {
        if (in_bounds(x_i))
            return true;
        
        NOT_IMPLEMENTED_YET();
        return false; 
    }

#if 0
    /**
       \brief Select a variable x_j in the row r defining the base var x_i, 
       s.t. x_j can be used to patch the error in x_i.  Return null_theory_var
       if there is no x_j. Otherwise, return x_j and store its coefficient
       in out_a_ij.

       The argument is_below is true (false) if x_i is below its lower
       bound (above its upper bound).
    */
    template<typename Ext>
    typename fixplex<Ext>::var_t 
    fixplex<Ext>::select_pivot_core(var_t x_i, numeral & out_a_ij) {
        SASSERT(is_base(x_i));
        var_t max    = get_num_vars();
        var_t result = max;
        row r = row(m_vars[x_i].m_base2row);
        int n = 0;
        unsigned best_col_sz = UINT_MAX;
        int best_so_far    = INT_MAX;
        
        for (auto const& r : M.row_iterator(r)) {
            var_t x_j       = r.m_var;          
            if (x_i == x_j) 
                continue;
            numeral const & a_ij = r.m_coeff;  
                                                               
            bool is_neg = is_below ? m.is_neg(a_ij) : m.is_pos(a_ij);
            bool is_pos = !is_neg;                                   
            bool can_pivot = ((is_pos && above_lower(x_j)) || (is_neg && below_upper(x_j)));
            if (can_pivot) {
                int num  = get_num_non_free_dep_vars(x_j, best_so_far);
                unsigned col_sz    = M.column_size(x_j);
                if (num < best_so_far || (num == best_so_far && col_sz < best_col_sz)) {
                    result        = x_j;
                    out_a_ij      = a_ij;
                    best_so_far   = num;
                    best_col_sz   = col_sz;
                    n             = 1;
                } 
                else if (num == best_so_far && col_sz == best_col_sz) {
                    n++;
                    if (m_random()%n == 0) {
                        result      = x_j;
                        out_a_ij    = a_ij;
                    }
                }                              
            }
        }
        return result < max ? result : null_var;
    }
#endif

    /**
       \brief Given row

         r_x = a*x + b*y + rest = 0

       Assume:

         base(r_x) = x
         value(r_x) = value(b*y + rest)
         old_value(y) := value(y)

       Effect:

         base(r_x)  := y
         value(x)   := new_value            
         value(r_x) := value(r_x) - b*value(y) + a*new_value
         value(y)   := -value(r_x) / b
         base_coeff(r_x) := b
 
       Let r be a row where y has coefficient c != 0.
       Assume: trailing_zeros(c) >= trailing_zeros(b)
       
         z = base(r)
         d = base_coeff(r)
         b1 = (b >> tz(b))
         c1 = (c >> (tz(c) - tz(b)))       
         r <- b1 * r  - c1 * r_x
         value(r) := b1 * value(r) - b1 * old_value(y) - c1 * value(r_x)
         value(z) := - value(r) / d
         base_coeff(r) := b1 * base_coeff(r)
    */    
    template<typename Ext>
    void fixplex<Ext>::pivot(var_t x, var_t y, numeral const& b, numeral const& new_value) {
        ++m_stats.m_num_pivots;
        SASSERT(is_base(x));
        SASSERT(!is_base(y));
        var_info& xI = m_vars[x];
        var_info& yI = m_vars[y];
        unsigned rx = xI.m_base2row;
        auto& row_x = m_rows[rx];
        numeral const& a = row_x.m_base_coeff;
        numeral old_value_y = yI.m_value;
        row_x.m_base = y;
        row_x.m_value = row_i.m_value - b*old_value_y + a*new_value;
        row_x.m_base_coeff = b;
        yI.m_base2row = rx;
        yI.m_is_base = true;
        yI.m_value = 0 - row_x.m_value / b;
        xI.m_is_base = false;
        xI.m_value = new_value;
        row r_x(rx);
        add_patch(y);
        SASSERT(well_formed_row(r_x));

        unsigned tz1 = trailing_zeros(b);

        for (auto col : M.col_entries(y)) {
            row r_z = col.get_row();
            unsigned rz = r_z.id();
            if (rz == rx)
                continue;
            auto& row_z = m_rows[rz];
            var_info& zI = m_vars[row_z];
            numeral c = col.get_row_entry().m_coeff;
            unsigned tz2 = trailing_zeros(c);
            SASSERT(tz1 <= tz2);
            numeral b1 = b >> tz1;
            numeral c1 = m.inv(c >> (tz2 - tz1));
            M.mul(r_z, b1);
            M.add(r_z, c1, r_x);
            row_z.m_value = (b1 * (row_z.m_value - old_value_y)) + c1 * row_x.m_value;
            row_z.m_base_coeff *= b1;
            zI.m_value = 0 - row_z.m_value / row_z.m_base_coeff;
            SASSERT(well_formed_row(r_z));
            add_patch(zI.m_base);
        }
        SASSERT(well_formed());
    }


}

