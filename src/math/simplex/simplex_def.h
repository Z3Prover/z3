/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    simplex_def.h

Abstract:

Author:

    Nikolaj Bjorner (nbjorner) 2014-01-15

Notes:

--*/

#ifndef _SIMPLEX_DEF_H_
#define _SIMPLEX_DEF_H_


namespace simplex {

    template<typename Ext>
    typename simplex<Ext>::row 
    simplex<Ext>::add_row(var_t base, unsigned num_vars, var_t const* vars, numeral const* coeffs) {
        DEBUG_CODE(
            bool found = false;
            for (unsigned i = 0; !found && i < num_vars; ++i) found = vars[i] == base;
            SASSERT(found);
            );
        row r = M.mk_row();
        for (unsigned i = 0; i < num_vars; ++i) {
            M.add(r, coeffs[i], vars[i]);
        }
        while (m_row2base.size() <= r.id()) {
            m_row2base.push_back(null_var);
        }
        m_row2base[r.id()] = base;
        m_vars[base].m_base2row = r.id();
        m_vars[base].m_is_base = true;
        return r;
    }

    template<typename Ext>
    void simplex<Ext>::del_row(row const& r) {
        m_is_base[m_row2base[r.id()]] = false;
        M.del(r);
    }

    template<typename Ext>
    void simplex<Ext>::set_lower(var_t var, eps_numeral const& b) {
        var_info& vi = m_vars[var];
        em.set(vi.m_lower, b);
        vi.m_lower_valid = true;
        if (em.lt(vi.m_value, b)) {
            scoped_eps_numeral delta(em);
            em.sub(b, vi.m_value, delta);
            update_value(var, delta);
        }
    }

    template<typename Ext>
    void simplex<Ext>::set_upper(var_t var, eps_numeral const& b) {
        var_info& vi = m_vars[var];
        em.set(vi.m_upper, b);
        vi.m_upper_valid = true;
        if (em.gt(vi.m_value, b)) {
            scoped_eps_numeral delta(em);
            em.sub(b, vi.m_value, delta);
            update_value(var, delta);
        }
    }

    template<typename Ext>
    void simplex<Ext>::unset_lower(var_t var) {
        m_vars[var].m_lower_valid = false;
    }

    template<typename Ext>
    void simplex<Ext>::unset_upper(var_t var) {
        m_vars[var].m_upper_valid = false;
    }

    template<typename Ext>
    void simplex<Ext>::set_value(var_t var, eps_numeral const& b) {
        scoped_eps_numeral delta(em);
        em.sub(b, m_vars[var].m_value, delta);
        update_value(var, delta);
    }

    template<typename Ext>
    typename simplex<Ext>::eps_numeral const& 
    simplex<Ext>::get_value(var_t v) {
        return m_vars[v].m_value;
    }

    template<typename Ext>
    void simplex<Ext>::display(std::ostream& out) const {
        M.display(out);
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            var_info const& vi = m_vars[i];
            out << "v" << i << " ";
            if (vi.m_is_base) out << "b:" << vi.m_base2row << " ";
            em.display(out, vi.m_value);
            out << " [";
            if (vi.m_lower_valid) em.display(out, vi.m_lower) else out << "-oo";
            out << ":";
            if (vi.m_upper_valid) em.display(out, vi.m_upper) else out << "oo";
            out << "]";
            out << "\n";
        }
    }

    template<typename Ext>
    void simplex<Ext>::ensure_var(var_t v) {
        while (v >= m_vars.size()) {
            M.ensure_var(m_vars.size());
            m_vars.push_back(var_info());
        }
    }

    template<typename Ext>
    lbool simplex<Ext>::make_feasible() {
        unsigned num_iterations = 0;
        var_t v = null_var;
        while ((v = select_var_to_fix()) != null_var) {
            if (m_cancel || num_iterations > m_max_iterations) {
                return l_undef;
            }
            check_blands_rule(v);
            if (!make_var_feasible(v)) {
                return l_false;
            }
            ++num_iterations;
            SASSERT(well_formed());
        }
        return l_true;
    }

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
    void simplex<Ext>::update_and_pivot(var_t x_i, var_t x_j, numeral const& a_ij, eps_numeral const& new_value) {
        SASSERT(is_base(x_i));
        SASSERT(!is_base(x_j));
        var_info& x_iI = m_vars[x_i];
        var_info& x_jI = m_vars[x_j];
        scoped_eps_numeral theta(em);
        theta = x_iI.m_value;
        theta -= new_value;
        numeral const& a_ii = x_iI.m_base_coeff;
        em.mul(theta, a_ii, theta);
        em.div(theta, a_ij, theta);
        update_value(x_j, theta);
        SASSERT(em.eq(x_iI.m_value, new_value));
        unsigned r_i = x_iI.m_base2row;
        x_jI.m_base2row = r_i;
        m_row2base[r_i] = x_j;
        x_jI.m_is_base = true;
        x_iI.m_is_base = false;
        if (outside_bounds(x_j)) {
            m_to_patch.insert(x_j);
        }
        col_iterator it = M.col_begin(x_j), end = M.col_end(x_j);
        scoped_numeral a_kj(m), g(m);
        for (; it != end; ++it) {
            row r_k = it.get_row();
            if (r_k != r_i) {
                a_kj = it.get_row_entry().m_coeff;
                a_kj.neg();
                M.mul(r_k, a_ij);
                M.add(r_k, a_kj, r_i);
                var_t s = m_row2base[r_k.id()];
                numeral& coeff = m_vars[s].m_base_coeff;
                m.mul(coeff, a_ij, coeff);
                M.gcd_normalize(r_k, g);
                if (!m.is_one(g)) {
                    m.div(coeff, g, coeff);
                }
            }
        }
    }

    template<typename Ext>
    void simplex<Ext>::update_value(var_t v, eps_numeral const& delta) {
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
            // TBD m.add(si.m_base_coeff, delta2, si.m_base_coeff); 
        }            
    }    

    template<typename Ext>
    void simplex<Ext>::update_value_core(var_t v, eps_numeral const& delta) {
        eps_numeral& val = m_vars[v].m_value;
        em.add(val, delta, val);
        if (is_base(v) && outside_bounds(v)) {
            m_to_patch.insert(v);
        }
    }

    template<typename Ext>
    bool simplex<Ext>::below_lower(var_t v) const {
        var_info const& vi = m_vars[v];
        return vi.m_lower_valid && em.lt(vi.m_value, vi.m_lower);
    }

    template<typename Ext>
    bool simplex<Ext>::above_upper(var_t v) const {
        var_info const& vi = m_vars[v];
        return vi.m_upper_valid && em.gt(vi.m_value, vi.m_upper);
    }

    template<typename Ext>
    bool simplex<Ext>::above_lower(var_t v) const {
        var_info const& vi = m_vars[v];
        return !vi.m_lower_valid || em.gt(vi.m_value, vi.m_lower);
    }

    template<typename Ext>
    bool simplex<Ext>::below_upper(var_t v) const {
        var_info const& vi = m_vars[v];
        return !vi.m_upper_valid || em.lt(vi.m_value, vi.m_upper);
    }

    template<typename Ext>
    bool simplex<Ext>::make_var_feasible(var_t x_i) {
        scoped_numeral a_ij(m);        
        scoped_eps_numeral value(em);
        bool is_below;
        if (below_lower(x_i)) {
            is_below = true;
            value = m_vars[x_i].m_lower;
        }
        else if (above_upper(x_i)) {
            is_below = false;
            value = m_vars[x_i].m_upper;
        }
        else {
            // x_i is already feasible
            return true;
        }
        var_t x_j = select_pivot(x_i, is_below, a_ij);
        if (x_j != null_var) {
            update_and_pivot(x_i, x_j, a_ij, value);
        }
        return x_j != null_var;
    }

    /**
       \brief Wrapper for select_blands_pivot_core and select_pivot_core
    */
    template<typename Ext>
    typename simplex<Ext>::var_t
    simplex<Ext>::select_pivot(var_t x_i, bool is_below, scoped_numeral& out_a_ij) {
        if (m_bland) {
            return select_blands_pivot(x_i, is_below, out_a_ij);
        }
        if (is_below) {
            return select_pivot_core<true>(x_i, out_a_ij);
        }
        else {
            return select_pivot_core<false>(x_i, out_a_ij);
        }
    }

    /**
       \brief Select a variable x_j in the row r defining the base var x_i, 
       s.t. x_j can be used to patch the error in x_i.  Return null_theory_var
       if there is no x_j. Otherwise, return x_j and store its coefficient
       in out_a_ij.

       The argument is_below is true (false) if x_i is below its lower
       bound (above its upper bound).
    */
    template<typename Ext>
    template<bool is_below>
    typename simplex<Ext>::var_t 
    simplex<Ext>::select_pivot_core(var_t x_i, scoped_numeral & out_a_ij) {
        SASSERT(is_base(x_i));
        var_t max    = get_num_vars();
        var_t result = max;
        row r = row(m_vars[x_i].m_base2row);
        int n;
        unsigned best_col_sz = UINT_MAX;
        int best_so_far    = INT_MAX;
        
        row_iterator it = M.row_begin(r), end = M.row_end(r);
    
        for (; it != end; ++it) {
            var_t x_j       = it->m_var;          
            numeral const & a_ij = it->m_coeff;  
                                                               
            bool is_neg = is_below ? m.is_neg(a_ij) : m.is_pos(a_ij);
            bool is_pos = !is_neg;                                   
            if (x_i != x_j && ((is_pos && above_lower(x_j)) || (is_neg && below_upper(x_j)))) {
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

    /**
       \brief Return the number of base variables that are non free and are v dependent.
       The function adds 1 to the result if v is non free.
       The function returns with a partial result r if r > best_so_far.
       This function is used to select the pivot variable.
    */
    template<typename Ext>
    int simplex<Ext>::get_num_non_free_dep_vars(var_t x_j, int best_so_far) {
        int result = is_non_free(x_j);
        col_iterator it = M.col_begin(x_j), end = M.col_end(x_j);
        for (; it != end; ++it) {
            var_t s = m_row2base[it.get_row().id()];
            result += is_non_free(s);
            if (result > best_so_far)
                return result;
        }
        return result;
    }
        

    /**
       \brief Using Bland's rule, select a variable x_j in the row r defining the base var x_i, 
       s.t. x_j can be used to patch the error in x_i.  Return null_theory_var
       if there is no x_j. Otherwise, return x_j and store its coefficient
       in out_a_ij.
    */
    template<typename Ext>
    typename simplex<Ext>::var_t 
    simplex<Ext>::select_blands_pivot(var_t x_i, bool is_below, scoped_numeral & out_a_ij) {
        SASSERT(is_base(x_i));
        unsigned max = get_num_vars();
        var_t result = max;
        row r(m_vars[x_i].m_base2row);
        row_iterator it = M.row_begin(r), end = M.row_end(r);
        for (; it != end; ++it) {
            var_t x_j = it->m_var;    
            numeral const & a_ij = it->m_coeff;                
            bool is_neg = is_below ? m.is_neg(a_ij) : m.is_pos(a_ij);
            bool is_pos = !is_neg; 
            if (x_i != x_j && ((is_pos && above_lower(x_j)) || (is_neg && below_upper(x_j)))) {
                SASSERT(!is_base(x_j));
                if (x_j < result) { 
                    result = x_j; 
                    out_a_ij = a_ij; 
                }
            }
        }
        return result < max ? result : null_var;
    }

    template<typename Ext>
    lbool simplex<Ext>::optimize(var_t v) {
        // TBD SASSERT(is_feasible());
        // pick row for v and check if primal
        // bounds are slack.
        // return l_false for unbounded.
        // return l_undef for canceled.
        // return l_true for optimal.
        return l_true;
    }

    template<typename Ext>
    typename simplex<Ext>::pivot_strategy_t 
    simplex<Ext>::pivot_strategy() {
        if (m_bland) {
            return S_BLAND;
        }
        return S_DEFAULT;
    }

    template<typename Ext>
    typename simplex<Ext>::var_t 
    simplex<Ext>::select_var_to_fix() {
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
    typename simplex<Ext>::var_t 
    simplex<Ext>::select_error_var(bool least) {
        var_t best = null_var;
        scoped_eps_numeral best_error(em);
        scoped_eps_numeral curr_error(em);
        typename var_heap::iterator it  = m_to_patch.begin();
        typename var_heap::iterator end = m_to_patch.end();
        for (; it != end; ++it) {
            var_t v = *it;
            var_info const& vi = m_vars[v];
            if (below_lower(v)) 
                em.sub(vi.m_lower, vi.m_value, curr_error);
            else if (above_upper(v)) 
                em.sub(vi.m_value, vi.m_lower, curr_error);
            else
                continue;
            SASSERT(is_pos(curr_error));
            if ((best == null_var) ||
                (!least && curr_error > best_error) ||
                (least && curr_error < best_error)) {
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
    bool simplex<Ext>::well_formed() const {
        SASSERT(M.well_formed());
        for (unsigned i = 0; i < m_row2base.size(); ++i) {
            var_t s = m_row2base[i];
            SASSERT(i == m_vars[s].m_base2row); // unless row is deleted.
            //
            // TBD: extract coefficient of base variable and compare
            // with m_vars[s].m_base_coeff;
            //
        }
        return true;
    }


};

#endif

