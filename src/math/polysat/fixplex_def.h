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
            TRACE("polysat", display(tout << "v" << v << "\n"););
            if (!m_limit.inc() || num_iterations > m_max_iterations) 
                return l_undef;
            check_blands_rule(v, num_repeated);
            switch (make_var_feasible(v)) {
            case l_true:
                ++num_iterations;
                break;
            case l_false:
                m_to_patch.insert(v);
                m_infeasible_var = v;
                ++m_stats.m_num_infeasible;
                return l_false;
            case l_undef:
                m_to_patch.insert(v);
                return l_undef;
            }
        }
        SASSERT(well_formed());
        return l_true;
    }

    template<typename Ext>
    typename fixplex<Ext>::row 
    fixplex<Ext>::add_row(var_t base_var, unsigned num_vars, var_t const* vars, numeral const* coeffs) {
        for (unsigned i = 0; i < num_vars; ++i) 
            ensure_var(vars[i]);

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
        set_base_value(base_var);
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
            set_base_value(s);
            add_patch(s);
        }            
    }    

    template<typename Ext>
    void fixplex<Ext>::gauss_jordan() {
#if 0
        while (!m_base_vars.empty()) {
            auto v = m_base_vars.back();
            auto rid = m_vars[v].m_base2row;

            auto const& row = m_rows[rid];
            make_basic(v, row);
        }
#endif
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
    bool fixplex<Ext>::in_bounds(numeral const& val, numeral const& lo, numeral const& hi) const {
        if (lo == hi)
            return true;
        if (lo < hi)
            return lo <= val && val < hi;
        return val < hi || lo <= val;
    }

    /**
     * Attempt to improve assigment to make x feasible.
     * 
     * return l_false if x is base variable of infeasible row
     * return l_true if it is possible to find an assignment that improves
     * return l_undef if the row could not be used for an improvement
     * 
     * delta - improvement over previous gap to feasible bound.
     * new_value - the new value to assign to x within its bounds.
     */

    template<typename Ext>
    lbool fixplex<Ext>::make_var_feasible(var_t x) {
        if (in_bounds(x))
            return l_true;
        auto val = value(x);
        numeral new_value = (lo(x) - val < val - hi(x)) ? lo(x) : hi(x) - 1;
        numeral b;
        var_t y = select_pivot_core(x, new_value, b);

        if (y == null_var) {
            if (is_infeasible_row(x))
                return l_false;
            else
                return l_undef;
        }

        
        pivot(x, y, b, new_value);

        get_offset_eqs(row(base2row(y)));

        return l_true;
    }

    /**
       \brief Select a variable y in the row r defining the base var x, 
       s.t. y can be used to patch the error in x_i.  Return null_var
       if there is no y. Otherwise, return y and store its coefficient
       in out_b.

       The routine gives up if the coefficients of all free variables do not have the minimal
       number of trailing zeros. 
    */
    template<typename Ext>
    var_t fixplex<Ext>::select_pivot_core(var_t x, numeral const& new_value, numeral & out_b) {
        SASSERT(is_base(x));
        var_t max    = get_num_vars();
        var_t result = max;
        row r(base2row(x));
        int n = 0;
        unsigned best_col_sz = UINT_MAX;
        int best_so_far    = INT_MAX;
        numeral row_value = m_rows[r.id()].m_value;
        numeral a = m_rows[r.id()].m_base_coeff;
        numeral delta_y = 0;
        numeral delta_best = 0;
        bool best_in_bounds = false;

        for (auto const& r : M.row_entries(r)) {
            var_t y = r.m_var;          
            numeral const & b = r.m_coeff;  
            if (x == y) 
                continue;
            if (!has_minimal_trailing_zeros(y, b))
                continue;
            numeral new_y_value = (row_value - b*value(y) - a*new_value)/b;
            bool _in_bounds = in_bounds(new_y_value, lo(y), hi(y));
            if (!_in_bounds) {
                if (lo(y) - new_y_value < new_y_value - hi(y))
                    delta_y = new_y_value - lo(y);
                else
                    delta_y = new_y_value - hi(y) - 1;
            }
            int num  = get_num_non_free_dep_vars(y, best_so_far);
            unsigned col_sz = M.column_size(y);
            bool is_improvement = false, is_plateau = false;

            // improvement criteria would need some scrutiny.
            if (best_so_far == INT_MAX)
                is_improvement = true;
            else if (!best_in_bounds && _in_bounds)
                is_improvement = true;
            else if (!best_in_bounds && !_in_bounds && delta_y < delta_best)
                is_improvement = true;
            else if (best_in_bounds && _in_bounds && num < best_so_far)
                is_improvement = true;
            else if (best_in_bounds && _in_bounds && num == best_so_far && col_sz < best_col_sz)
                is_improvement = true;
            else if (!best_in_bounds && !_in_bounds && delta_y == delta_best && best_so_far == num && col_sz == best_col_sz)
                is_plateau = true;
            else if (best_in_bounds && _in_bounds && best_so_far == num && col_sz == best_col_sz)
                is_plateau = true;
            
            if (is_improvement) {
                result       = y;
                out_b        = b;
                best_so_far  = num;
                best_col_sz  = col_sz;
                best_in_bounds = _in_bounds;
                delta_best   = delta_y;
                n            = 1;
            } 
            else if (is_plateau) {
                n++;
                if (m_random() % n == 0) {
                    result   = y;
                    out_b    = b;
                }
            }                              
        }
        if (result == max)
            return null_var;
        if (!best_in_bounds && delta_best >= value2delta(x, new_value))
            return null_var;
        return result;
    }

    /**
     * Compute delta to add to the value, such that value + delta is either lo(v), or hi(v) - 1
     * A pre-condition is that value is not in the range [lo(v),hi(v)[, 
     * and therefore as a consequence lo(v) != hi(v).
     */
    template<typename Ext>
    typename fixplex<Ext>::numeral 
    fixplex<Ext>::value2delta(var_t v, numeral const& value) const {
        SASSERT(!in_bounds(v));
        SASSERT(lo(v) != hi(v));
        if (lo(v) - value < value - hi(v))
            return lo(v) - value;
        else
            return hi(v) - value - 1;    
    }


    /**
     * The the bounds of variable v.
     * If the current value of v, value(v), is in bounds, no further updates are made.
     * If value(v) is outside the the new bounds, then
     * - the tableau is updated if v is non-basic.
     * - the variable v is queued to patch if v is basic.
     */
    template<typename Ext>
    void fixplex<Ext>::set_bounds(var_t v, numeral const& lo, numeral const& hi) {         
        m_vars[v].m_lo = lo; 
        m_vars[v].m_hi = hi; 
        if (in_bounds(v))
            return;
        if (is_base(v)) 
            add_patch(v);
        else
            update_value(v, value2delta(v, value(v)));
    }

    /**
     * Check if the coefficient b of y has the minimal number of trailing zeros.
     * In other words, the coefficient b is a multiple of the smallest power of 2.
     */
    template<typename Ext>
    bool fixplex<Ext>::has_minimal_trailing_zeros(var_t y, numeral const& b) {
        unsigned tz1 = m.trailing_zeros(b);
        if (tz1 == 0)
            return true;
        for (auto col : M.col_entries(y)) {
            numeral c = col.get_row_entry().m_coeff;
            unsigned tz2 = m.trailing_zeros(c);
            if (tz1 > tz2)
                return false;
        }
        return true;
    }

    /**
     * Determine if row is linear infeasiable.
     * A row is linear infeasible if it can be established
     * that none of the available assignments within current
     * bounds let the row add up to 0.
     * 
     * Assume the row is of the form:
     *   ax + by + cz = 0
     * with bounds
     *   x : [lo_x, hi_x[, y : [lo_y, hi_y[, z : [lo_z : hi_z[
     * 
     * Claim. The row is infeasible if the following conditions are met:
     * 
     * - 0 < a*lo_x + b*lo_y + c*lo_z <= a*hi_x + b*hi_y + c*hi_z  mod 2^k
     * - a*(hi_x - lo_x) + b*(hi_y - lo_y) + c*(hi_z - lo_z) < 2^k
     * - lo_x != hi_x, lo_y != hi_y, lo_z != hi_z
     * 
     */
    template<typename Ext>
    bool fixplex<Ext>::is_infeasible_row(var_t x) {
        SASSERT(is_base(x));
        auto r = base2row(x);
        numeral lo_sum = 0, hi_sum = 0, diff = 0;
        for (auto const& e : M.row_entries(row(r))) {
            var_t v = e.m_var;
            numeral const& c = e.m_coeff;
            if (lo(v) == hi(v))
                return false;
            lo_sum += lo(v) * c;
            hi_sum += (hi(v) - 1) * c;
            numeral range = hi(v) - lo(v);
            if (!m.signed_mul(range, c, range))
                return false;
            if (!m.signed_add(diff, diff, range))
                return false;
        }        
        return 0 < lo_sum && lo_sum <= hi_sum;
    }

    /**
     * Check if row is infeasible modulo parity constraints.
     * Let parity be the minimal power of two of coefficients to non-fixed variables.
     * Let fixed be the sum of fixed variables.
     * A row is infeasible if parity > the smallest power of two dividing fixed.
     *
     * Other parity tests are possible.
     * The "range" parity test checks if the minimal parities of all but one variable are outside
     * the range of the value range of a selected variable.
     */
    template<typename Ext>
    bool fixplex<Ext>::is_parity_infeasible_row(var_t x) {
        SASSERT(is_base(x));
        auto r = base2row(x);
        if (row2integral(row(r)))
            return false;
        numeral fixed = 0;
        unsigned parity = UINT_MAX;
        for (auto const& e : M.row_entries(row(r))) {
            var_t v = e.m_var;
            auto c = e.m_coeff;
            if (is_fixed(v))
                fixed += value(v)*c;
            else 
                parity = std::min(m.trailing_zeros(c), parity);
        }

        if (m.trailing_zeros(fixed) < parity)
            return true;
        
        return false;
    }


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
        row_x.m_value = row_x.m_value - b*old_value_y + a*new_value;
        row_x.m_base_coeff = b;
        yI.m_base2row = rx;
        yI.m_is_base = true;
        set_base_value(y);
        xI.m_is_base = false;
        xI.m_value = new_value;
        row r_x(rx);
        add_patch(y);
        SASSERT(well_formed_row(r_x));

        unsigned tz1 = m.trailing_zeros(b);
 
        for (auto col : M.col_entries(y)) {
            row r_z = col.get_row();
            unsigned rz = r_z.id();
            if (rz == rx)
                continue;
            auto z = row2base(r_z);
            auto& row_z = m_rows[rz];
            var_info& zI = m_vars[z];
            numeral c = col.get_row_entry().m_coeff;
            unsigned tz2 = m.trailing_zeros(c);
            SASSERT(tz1 <= tz2);
            numeral b1 = b >> tz1;
            numeral c1 = m.inv(c >> (tz2 - tz1));
            M.mul(r_z, b1);
            M.add(r_z, c1, r_x);
            row_z.m_value = (b1 * (row_z.m_value - old_value_y)) + c1 * row_x.m_value;
            row_z.m_base_coeff *= b1;
            set_base_value(z);
            SASSERT(well_formed_row(r_z));
            add_patch(row_z.m_base);
        }
        SASSERT(well_formed());
    }

    template<typename Ext>    
    bool fixplex<Ext>::is_feasible() const {
        for (unsigned i = m_vars.size(); i-- > 0; )
            if (!in_bounds(i))
                return false;
        return true;
    }

    template<typename Ext>
    typename fixplex<Ext>::row 
    fixplex<Ext>::get_infeasible_row() {
        SASSERT(is_base(m_infeasible_var));
        return row(base2row(m_infeasible_var));
    }

    /**
       \brief Return the number of base variables that are non free and are v dependent.
       The function adds 1 to the result if v is non free.
       The function returns with a partial result r if r > best_so_far.
       This function is used to select the pivot variable.
    */
    template<typename Ext>
    int fixplex<Ext>::get_num_non_free_dep_vars(var_t x_j, int best_so_far) {
        int result = is_non_free(x_j);
        for (auto const& col : M.col_entries(x_j)) {
            var_t s = m_rows[col.get_row().id()].m_base;
            result += is_non_free(s);
            if (result > best_so_far)
                return result;
        }
        return result;
    }

    template<typename Ext>
    void fixplex<Ext>::add_patch(var_t v) {
        SASSERT(is_base(v));
        CTRACE("polysat", !in_bounds(v), tout << "Add patch: v" << v << "\n";);
        if (in_bounds(v)) {
            
        }
        else 
            m_to_patch.insert(v);
    }

    template<typename Ext>
    var_t fixplex<Ext>::select_var_to_fix() {
        switch (pivot_strategy()) {
        case S_BLAND:
            return select_smallest_var();
        case S_GREATEST_ERROR:
            return select_error_var(false);
        case S_LEAST_ERROR:
            return select_error_var(true);
        default:
            return select_smallest_var();
        }
    }

    template<typename Ext>
    var_t fixplex<Ext>::select_error_var(bool least) {
        var_t best = null_var;
        numeral best_error = 0, curr_error = 0;
        for (var_t v : m_to_patch) {
            if (in_bounds(v))
                continue;
            if (lo(v) - value(v) < value(v) - hi(v))
                curr_error = lo(v) - value(v);
            else
                curr_error = value(v) - hi(v) - 1;
            if ((best == null_var) || 
                (least && curr_error < best_error) ||
                (!least && curr_error > best_error)) {
                best = v;
                best_error = curr_error;
            }
        }
        if (best == null_var)
            m_to_patch.clear(); // all variables are satisfied
        else
            m_to_patch.erase(best);
        return best;
    }

    template<typename Ext>
    void fixplex<Ext>::check_blands_rule(var_t v, unsigned& num_repeated) {
        if (m_bland) 
            return;
        if (!m_left_basis.contains(v)) 
            m_left_basis.insert(v);
        else {
            ++num_repeated;
            m_bland = num_repeated > m_blands_rule_threshold;
            CTRACE("polysat", m_bland, tout << "using blands rule, " << num_repeated << "\n";);
        }
    }

    /**
     * Check if row is solved with respect to integrality constraints.
     * The value of the row is allowed to be off by the base coefficient
     * representing the case where there is a rational, but not integer solution.
     */
    template<typename Ext>                                     
    bool fixplex<Ext>::is_solved(row const& r) const {
        return (value(row2base(r)) * row2base_coeff(r)) + row2value(r) == 0;
    }

    template<typename Ext>                                     
    void fixplex<Ext>::set_base_value(var_t x) {
        SASSERT(is_base(x));
        row r(base2row(x));
        m_vars[x].m_value = 0 - (row2value(r) / row2base_coeff(r));
        bool was_integral = row2integral(r);
        m_rows[r.id()].m_integral = is_solved(r);
        if (was_integral && !row2integral(r))
            ++m_num_non_integral;
        else if (!was_integral && row2integral(r))
            --m_num_non_integral;                 
    }

    /**
     * Equality detection.
     *
     * Offset equality detection
     * -------------------------
     * is_offset_row: determine if row is cx*x + cy*y + k == 0 where k is a constant.
     * Then walk every row containing x, y, respectively
     * If there is a row cx*x + cy*z + k' == 0, where y, z are two different variables
     * but value(y) = value(z), cy is odd
     * then it follows that k = k' and y = z is implied.
     * 
     * Offset equality detection is only applied to integral rows where the current  
     * evaluation satisfies the row equality.
     *
     * Fixed variable equalities
     * -------------------------
     * 
     */

    template<typename Ext>
    void fixplex<Ext>::get_offset_eqs(row const& r) {
        var_t x, y;
        numeral cx, cy;
        if (!is_offset_row(r, cx, x, cy, y))
            return;
        lookahead_eq(r, cx, x, cy, y);
        lookahead_eq(r, cy, y, cx, x);
    }

    template<typename Ext>
    bool fixplex<Ext>::is_offset_row(row const& r, numeral& cx, var_t& x, numeral& cy, var_t & y) const {
        x = null_var;
        y = null_var;
        if (!row2integral(r))
            return false;
        for (auto const& e : M.row_entries(r)) {
            var_t v = e.m_var;
            if (is_fixed(v))
                continue;
            numeral const& c = e.m_coeff;
            if (x == null_var) {
                cx = c;
                x = v;
            }
            else if (y == null_var) {
                cy = c;
                y = v;
            }
            else
                return false;
        }        
        return y != null_var;
    }


    template<typename Ext>
    void fixplex<Ext>::lookahead_eq(row const& r1, numeral const& cx, var_t x, numeral const& cy, var_t y) {   
        if (m.is_even(cy))
            return;
        var_t z, u;
        numeral cz, cu;
        for (auto c : M.col_entries(x)) {
            auto r2 = c.get_row();
            if (r1.id() == r2.id())
                continue;
            if (!is_offset_row(r2, cz, z, cu, u))
                continue;
            if (u == x) {
                std::swap(z, u);
                std::swap(cz, cu);
            }
            if (z == x && cx == cz && u != y && cu == cy && value(u) == value(y)) 
                eq_eh(u, y, r1, r2);                
        }
    }

    template<typename Ext>
    void fixplex<Ext>::eq_eh(var_t x, var_t y, row const& r1, row const& r2) {
        m_offset_eqs.push_back(offset_eq(x, y, r1, r2));
    }
    

    template<typename Ext>    
    std::ostream& fixplex<Ext>::display(std::ostream& out) const {
        M.display(out);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            var_info const& vi = m_vars[i];
            out << "v" << i << " " << value(i) << " [" << lo(i) << ", " << hi(i) << "[ ";
            if (vi.m_is_base) out << "b:" << vi.m_base2row << " ";
            out << "\n";
        }
        return out;
    }

    template<typename Ext>    
    std::ostream& fixplex<Ext>::display_row(std::ostream& out, row const& r, bool values) {
        for (auto const& e : M.row_entries(r)) {
            var_t v = e.m_var;
            if (e.m_coeff != 1)
                out << e.m_coeff << " * ";
            out << "v" << v << " ";
            if (values) 
                out << value(v) << " [" << lo(v) << ", " << hi(v) << "[ ";            
        }
        return out << "\n";
    }

    template<typename Ext>    
    bool fixplex<Ext>::well_formed() const { 
        SASSERT(M.well_formed());
        for (unsigned i = 0; i < m_rows.size(); ++i) {
            row r(i);
            var_t s = row2base(r);
            if (s == null_var) 
                continue;
            SASSERT(i == base2row(s));
            VERIFY(well_formed_row(r));
        }
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            SASSERT(is_base(i) || in_bounds(i));
        }
        return true;
    }

    template<typename Ext>                                     
    bool fixplex<Ext>::well_formed_row(row const& r) const { 
        var_t s = m_rows[r.id()].m_base;
        (void)s;
        SASSERT(base2row(s) == r.id());
        SASSERT(m_vars[s].m_is_base);
        numeral sum = 0;
        numeral base_coeff = m_rows[r.id()].m_base_coeff;
        for (auto const& e : M.row_entries(r)) {
            sum += value(e.m_var) * e.m_coeff;
            SASSERT(s != e.m_var || base_coeff == e.m_coeff);
        }
        if (sum >= base_coeff) {
            IF_VERBOSE(0, M.display_row(verbose_stream(), r););
            TRACE("polysat", display(tout << "non-well formed row\n"); M.display_row(tout << "row: ", r););
            throw default_exception("non-well formed row");
        }
        return true;
    }

    template<typename Ext>
    void fixplex<Ext>::collect_statistics(::statistics & st) const {
        M.collect_statistics(st);
        st.update("fixplex num pivots", m_stats.m_num_pivots);
        st.update("fixplex num infeasible", m_stats.m_num_infeasible);
        st.update("fixplex num checks", m_stats.m_num_checks);
        st.update("fixplex num non-integral", m_num_non_integral);
    }
}
