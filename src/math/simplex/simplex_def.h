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
        scoped_numeral base_coeff(m);
        row r = M.mk_row();
        for (unsigned i = 0; i < num_vars; ++i) {
            M.add(r, coeffs[i], vars[i]);
            if (vars[i] == base) {
                m.set(base_coeff, coeffs[i]);
            }
        }
        while (m_row2base.size() <= r.id()) {
            m_row2base.push_back(null_var);
        }
        m_row2base[r.id()] = base;
        m_vars[base].m_base2row = r.id();
        m_vars[base].m_is_base = true;
        m.set(m_vars[base].m_base_coeff, base_coeff); 
        return r;
    }

    template<typename Ext>
    void simplex<Ext>::del_row(row const& r) {
        m_vars[m_row2base[r.id()]].m_is_base = false;
        m_row2base[r.id()] = null_var;
        M.del(r);
    }

    template<typename Ext>
    void simplex<Ext>::set_lower(var_t var, eps_numeral const& b) {
        var_info& vi = m_vars[var];
        em.set(vi.m_lower, b);
        vi.m_lower_valid = true;
        SASSERT(!vi.m_upper_valid || em.le(b, vi.m_upper));
        if (!vi.m_is_base && em.lt(vi.m_value, b)) {
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
        SASSERT(!vi.m_lower_valid || em.le(vi.m_lower, b));
        if (!vi.m_is_base && em.gt(vi.m_value, b)) {
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
            out << em.to_string(vi.m_value);
            out << " [";
            if (vi.m_lower_valid) out << em.to_string(vi.m_lower); else out << "-oo";
            out << ":";
            if (vi.m_upper_valid) out << em.to_string(vi.m_upper); else out << "oo";
            out << "]";
            if (vi.m_is_base) out << " b:" << vi.m_base2row;
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
        m_left_basis.reset();
        unsigned num_iterations = 0;
        unsigned num_repeated = 0;
        var_t v = null_var;
        while ((v = select_var_to_fix()) != null_var) {
            if (m_cancel || num_iterations > m_max_iterations) {
                return l_undef;
            }
            check_blands_rule(v, num_repeated);
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
        scoped_eps_numeral theta(em);
        theta = x_iI.m_value;
        theta -= new_value;
        numeral const& a_ii = x_iI.m_base_coeff;
        em.mul(theta, a_ii, theta);
        em.div(theta, a_ij, theta);
        update_value(x_j, theta);
        SASSERT(em.eq(x_iI.m_value, new_value));
        pivot(x_i, x_j, a_ij);
    }
    
    template<typename Ext>
    void simplex<Ext>::pivot(var_t x_i, var_t x_j, numeral const& a_ij) {
        var_info& x_iI = m_vars[x_i];
        var_info& x_jI = m_vars[x_j];
        unsigned r_i = x_iI.m_base2row;
        m_row2base[r_i] = x_j;
        x_jI.m_base2row = r_i;
        m.set(x_jI.m_base_coeff, a_ij);
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
    bool simplex<Ext>::at_lower(var_t v) const {
        var_info const& vi = m_vars[v];
        return vi.m_lower_valid && em.eq(vi.m_value, vi.m_lower);
    }

    template<typename Ext>
    bool simplex<Ext>::at_upper(var_t v) const {
        var_info const& vi = m_vars[v];
        return vi.m_upper_valid && em.eq(vi.m_value, vi.m_upper);
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
       \brief Wrapper for select_pivot_blands and select_pivot_core
    */
    template<typename Ext>
    typename simplex<Ext>::var_t
    simplex<Ext>::select_pivot(var_t x_i, bool is_below, scoped_numeral& out_a_ij) {
        if (m_bland) {
            return select_pivot_blands(x_i, is_below, out_a_ij);
        }
        return select_pivot_core(x_i, is_below, out_a_ij);
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
    typename simplex<Ext>::var_t 
    simplex<Ext>::select_pivot_core(var_t x_i, bool is_below, scoped_numeral & out_a_ij) {
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
            if (x_i == x_j) continue;
            numeral const & a_ij = it->m_coeff;  
                                                               
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
       s.t. x_j can be used to patch the error in x_i.  Return null_var
       if there is no x_j. Otherwise, return x_j and store its coefficient
       in out_a_ij.
    */
    template<typename Ext>
    typename simplex<Ext>::var_t 
    simplex<Ext>::select_pivot_blands(var_t x_i, bool is_below, scoped_numeral & out_a_ij) {
        SASSERT(is_base(x_i));
        unsigned max = get_num_vars();
        var_t result = max;
        row r(m_vars[x_i].m_base2row);
        row_iterator it = M.row_begin(r), end = M.row_end(r);
        for (; it != end; ++it) {
            var_t x_j = it->m_var;    
            numeral const & a_ij = it->m_coeff;                
            bool is_neg = is_below ? m.is_neg(a_ij) : m.is_pos(a_ij);
            if (x_i != x_j && ((!is_neg && above_lower(x_j)) || (is_neg && below_upper(x_j)))) {
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
    lbool simplex<Ext>::minimize(var_t v) {
        
        // minimize v, such that tableau is feasible.
        // Assume there are no bounds on v.
        // Let  k*v + c*x = 0 e.g, maximize c*x over 
        // tableau constraints:
        //
        //   max { c*x | A*x = 0 and l <= x <= u }
        //
        // start with feasible assigment 
        // A*x0 = 0 and l <= x0 <= u
        //
        // Identify pivot: i, j: such that x_i is base,
        // there is a row k1*x_i + k2*x_j + R = 0
        // and a delta such that:
        //
        // x_i' <- x_i + delta
        // x_j' <- x_j - delta*k1/k2
        // l_i <= x_i' <= u_i
        // l_j <= x_j' <= u_j
        // and c*x' > c*x
        // e.g., c*x := c_i*x_i + c_j*x_j + ...
        // and c_i*delta > c_j*delta*k1/k2 
        // and x_i < u_i (if delta > 0), l_i < x_i (if delta < 0)
        // and l_j < x_j (if delta > 0), x_j < u_j (if delta < 0)
        // 
        // update all rows, including c*x, using the pivot.
        // 
        // If there is c_i*x_i in c*x such that c_i > 0 
        // and upper_i = oo and complementary lower_j = -oo
        // then the objective is unbounded.
        // 
        // There is a singularity if there is a pivot such that
        // c_i*delta == c_j*delta*k1/k2, e.g., nothing is improved,
        // pivot, but use bland's rule to ensure
        // convergence in the limit.
        // 

        SASSERT(is_feasible());
        scoped_eps_numeral delta(em);
        scoped_numeral a_ij(m);
        var_t x_i, x_j;
        bool inc;

        while (true) {
            if (m_cancel) {
                return l_undef;
            }
            select_pivot_primal(v, x_i, x_j, a_ij, inc);
            if (x_j == null_var) {
                // optimal
                return l_true;
            }
            var_info& vj = m_vars[x_j];
            if (x_i == null_var) {
                if (inc && vj.m_upper_valid) {
                    delta = vj.m_upper;
                    delta -= vj.m_value;
                    update_value(x_j, delta);
                }
                else if (!inc && vj.m_lower_valid) {
                    delta = vj.m_lower;
                    delta -= vj.m_value;
                    update_value(x_j, delta);
                }
                else {
                    // unbounded
                    return l_false;
                }
                continue;
            }

            // TBD: Change the value of x_j directly without pivoting:
            // 
            // if (!vj.is_fixed() && vj.bounded() && gain >= upper - lower) {
            // 
            // }
            // 

            pivot(x_i, x_j, a_ij);
            move_to_bound(x_i, inc == m.is_pos(a_ij));            
        }
        return l_true;
    }

    template<typename Ext>
    void simplex<Ext>::move_to_bound(var_t x, bool to_lower) {
        scoped_eps_numeral delta(em), delta2(em);
        var_info& vi = m_vars[x];
        if (to_lower) {
            em.sub(vi.m_value, vi.m_lower, delta);
        }
        else {
            em.sub(vi.m_upper, vi.m_value, delta);
        }
        col_iterator it = M.col_begin(x), end = M.col_end(x);
        for (; it != end && is_pos(delta); ++it) {
            var_t s = m_row2base[it.get_row().id()];
            var_info& vs = m_vars[s];
            numeral const& coeff = it.get_row_entry().m_coeff;
            SASSERT(!m.is_zero(coeff));
            bool inc_s = (m.is_pos(coeff) == to_lower);
            eps_numeral const* bound = 0;
            if (inc_s && vs.m_upper_valid) {
                bound = &vs.m_upper;
            }
            else if (!inc_s && vs.m_lower_valid) {
                bound = &vs.m_lower;
            }
            if (bound) {
                em.sub(*bound, vs.m_value, delta2);
                em.div(delta2, coeff, delta2);
                abs(delta2);
                if (delta2 < delta) {
                    delta = delta2;
                }
            }
        }
        if (to_lower) {
            delta.neg();
        }
        update_value(x, delta);        
    }

    template<typename Ext>
    void simplex<Ext>::select_pivot_primal(var_t v, var_t& x_i, var_t& x_j, scoped_numeral& a_ij, bool& inc) {
        row r(m_vars[v].m_base2row);
        row_iterator it = M.row_begin(r), end = M.row_end(r);
    
        scoped_eps_numeral gain(em), new_gain(em);
        scoped_numeral new_a_ij(m);
        x_i = null_var;
        x_j = null_var;
        inc = false;

        for (; it != end; ++it) {
            var_t x = it->m_var;          
            if (x == v) continue; 
            bool is_pos = m.is_pos(it->m_coeff);
            if ((is_pos && at_upper(x)) || (!is_pos && at_lower(x))) {
                continue; // variable cannot be used for improving bounds.
                // TBD check?
            }
            var_t y = pick_var_to_leave(x, is_pos, new_gain, new_a_ij);
            if (y == null_var) {
                // unbounded.
                x_i = y;
                x_j = x;
                inc = is_pos;
                a_ij = new_a_ij;
                break;
            }
            bool better = 
                (new_gain > gain) ||
                ((is_zero(new_gain) && is_zero(gain) && (x_i == null_var || y < x_i)));

            if (better) {
                x_i = y;
                x_j = x;
                inc = is_pos;
                gain = new_gain;
                a_ij = new_a_ij;
            }            
        }
    }

    template<typename Ext>
    typename simplex<Ext>::var_t 
    simplex<Ext>::pick_var_to_leave(
        var_t x_j, bool inc, 
        scoped_eps_numeral& gain, scoped_numeral& new_a_ij) {
        var_t x_i = null_var;
        gain.reset();
        scoped_eps_numeral curr_gain(em);
        col_iterator it = M.col_begin(x_j), end = M.col_end(x_j);
        for (; it != end; ++it) {
            row r = it.get_row();
            var_t s = m_row2base[r.id()];
            var_info& vi = m_vars[s];
            numeral const& a_ij = it.get_row_entry().m_coeff;
            numeral const& a_ii = vi.m_base_coeff;
            bool inc_s = m.is_neg(a_ij) ? inc : !inc;
            if ((inc_s && !vi.m_upper_valid) || (!inc_s && !vi.m_lower_valid)) {
                continue;
            }            
            // 
            // current gain: (value(x_i)-bound)*a_ii/a_ij
            // 
            curr_gain = vi.m_value;
            curr_gain -= inc_s?vi.m_upper:vi.m_lower;
            em.mul(curr_gain, a_ii, curr_gain);
            em.div(curr_gain, a_ij, curr_gain);
            if (is_neg(curr_gain)) {
                curr_gain.neg();
            }
            if (x_i == null_var || (curr_gain < gain) || 
                (is_zero(gain) && is_zero(curr_gain) && s < x_i)) {
                x_i = s;
                gain = curr_gain;
                new_a_ij = a_ij;
            }
        }
        TRACE("simplex", tout << "x_i v" << x_i << "\n";);
        return x_i;
    }

    template<typename Ext>
    void simplex<Ext>::check_blands_rule(var_t v, unsigned& num_repeated) {
        if (m_bland) 
            return;
        if (m_left_basis.contains(v)) {
            num_repeated++;        
            if (num_repeated > m_blands_rule_threshold) {
                TRACE("simplex", tout << "using blands rule, " << num_repeated << "\n";);
                // std::cerr << "BLANDS RULE...\n";
                m_bland = true;
            }
        }
        else {
            m_left_basis.insert(v);
        }
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
            if (s == null_var) continue;
            SASSERT(i == m_vars[s].m_base2row); 
            //
            // TBD: extract coefficient of base variable and compare
            // with m_vars[s].m_base_coeff;
            //
            // check that sum of assignments add up to 0 for every row.
            row_iterator it = M.row_begin(row(i)), end = M.row_end(row(i));
            scoped_eps_numeral sum(em), tmp(em);
            for (; it != end; ++it) {
                em.mul(m_vars[it->m_var].m_value, it->m_coeff, tmp);
                sum += tmp;
            }
            SASSERT(em.is_zero(sum));
        }
        return true;
    }

    template<typename Ext>
    bool simplex<Ext>::is_feasible() const {
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            if (below_lower(i) || above_upper(i)) return false;            
        }
        return true;
    }

};

#endif

