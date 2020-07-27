/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    simplex_def.h

Author:

    Nikolaj Bjorner (nbjorner) 2014-01-15

Notes:

    Sign of base variables can vary.
    Sign could possibly be normalized to positive.
    Otherwise, sign could be accounted in pivoting.

--*/

#pragma once


namespace simplex {

    template<typename Ext>
    const typename simplex<Ext>::var_t simplex<Ext>::null_var = UINT_MAX; 

    template<typename Ext>
    simplex<Ext>::~simplex() {
        reset();
    }

    template<typename Ext>
    typename simplex<Ext>::row 
    simplex<Ext>::add_row(var_t base_var, unsigned num_vars, var_t const* vars, numeral const* coeffs) {
        m_base_vars.reset();
        row r = M.mk_row();
        for (unsigned i = 0; i < num_vars; ++i) {
            if (!m.is_zero(coeffs[i])) {
                var_t v = vars[i];
                if (is_base(v)) {
                    m_base_vars.push_back(i);
                }
                M.add_var(r, coeffs[i], v);
            }
        }
        scoped_numeral mul(m), a(m), b(m), c(m);
        m.set(mul, 1);
        for (unsigned i = 0; i < m_base_vars.size(); ++i) {
            var_t v = vars[m_base_vars[i]];
            m.mul(coeffs[m_base_vars[i]], mul, a);            
            m.set(b, m_vars[v].m_base_coeff);
            m.lcm(a, b, c);
            TRACE("simplex",
                  m.display(tout << " a: ", a);
                  m.display(tout << " b v" << v << " : ", b);
                  m.display(tout << " c: ", c);
                  tout << "\n";
                  M.display_row(tout, r);
                  M.display_row(tout, row(m_vars[v].m_base2row));
                  if (m.is_zero(b)) {
                      display(tout);
                  });
            SASSERT(is_base(v));
            m.abs(c);
            m.div(c, a, b);
            m.div(c, m_vars[v].m_base_coeff, a);
            m.mul(mul, b, mul);
            M.mul(r, b);
            m.neg(a);
            M.add(r, a, row(m_vars[v].m_base2row));
            TRACE("simplex", M.display_row(tout, r););
        }

        scoped_numeral base_coeff(m);
        scoped_eps_numeral value(em), tmp(em);
        row_iterator it = M.row_begin(r), end = M.row_end(r);
        for (; it != end; ++it) {
            var_t v = it->m_var;
            if (v == base_var) {
                m.set(base_coeff, it->m_coeff);
            }
            else {
                SASSERT(!is_base(v));
                em.mul(m_vars[v].m_value, it->m_coeff, tmp);
                em.add(value, tmp, value);
            }
        }
        SASSERT(!m.is_zero(base_coeff));
        TRACE("simplex", 
              for (unsigned i = 0; i < num_vars; ++i) {
                  m.display(tout << "v" << vars[i] << " * ", coeffs[i]); tout << " ";
                  if (i + 1 < num_vars) tout << " + ";
              }
              tout << "\n";
              row_iterator it2 = M.row_begin(r);
              bool first = true;
              for (; it2 != end; ++it2) {
                  if (!first) tout << " + ";
                  tout << "v" << it2->m_var << " * ";
                  m.display(tout, it2->m_coeff); tout << " ";                  
                  first = false;
              }
              tout << "\n";
              );
        SASSERT(!is_base(base_var));
        em.neg(value);
        em.div(value, base_coeff, value);
        while (m_row2base.size() <= r.id()) {
            m_row2base.push_back(null_var);
        }
        m_row2base[r.id()] = base_var;
        m_vars[base_var].m_base2row = r.id();
        m_vars[base_var].m_is_base = true;
        m.set(m_vars[base_var].m_base_coeff, base_coeff); 
        em.set(m_vars[base_var].m_value, value);
        add_patch(base_var);
        SASSERT(well_formed_row(r));
        SASSERT(well_formed());
        return r;
    }

    template<typename Ext>
    typename simplex<Ext>::row 
    simplex<Ext>::get_infeasible_row() {
        SASSERT(is_base(m_infeasible_var));
        unsigned row_id = m_vars[m_infeasible_var].m_base2row;
        return row(row_id);
    }

    template<typename Ext>
    void simplex<Ext>::add_patch(var_t v) {
        SASSERT(is_base(v));
        if (outside_bounds(v)) {
            TRACE("simplex", tout << "Add patch: v" << v << "\n";);
            m_to_patch.insert(v);
        }
    }

    template<typename Ext>
    void simplex<Ext>::del_row(row const& r) {
        var_t var = m_row2base[r.id()];
        m_vars[var].m_is_base = false;
        m_vars[var].m_lower_valid = false;
        m_vars[var].m_upper_valid = false;
        m_row2base[r.id()] = null_var;
        M.del(r);
        SASSERT(M.col_begin(var) == M.col_end(var));
        SASSERT(well_formed());
    }

    template<typename Ext>
    void simplex<Ext>::del_row(var_t var) {
        TRACE("simplex", tout << var << "\n";);
        row r;
        if (is_base(var)) {
            r = row(m_vars[var].m_base2row);                                    
        }
        else {
            col_iterator it = M.col_begin(var), end = M.col_end(var);
            if (it == end) {
                return;
            }
            typename matrix::row_entry const& re = it.get_row_entry();
            r = it.get_row();
            var_t old_base = m_row2base[r.id()];
            scoped_eps_numeral new_value(em);
            var_info& vi = m_vars[old_base];
            if (below_lower(old_base)) {
                new_value = vi.m_lower;
            }
            else if (above_upper(old_base)) {
                new_value = vi.m_upper;
            }
            else {
                new_value = vi.m_value;
            }
            // need to move var such that old_base comes in bound.
            update_and_pivot(old_base, var, re.m_coeff, new_value);   
            SASSERT(is_base(var));
            SASSERT(m_vars[var].m_base2row == r.id());            
            SASSERT(!below_lower(old_base) && !above_upper(old_base));
        }
        del_row(r);
        TRACE("simplex", display(tout););
        SASSERT(well_formed());
    }

    template<typename Ext>
    bool simplex<Ext>::above_lower(var_t var, eps_numeral const& b) const {
        var_info const& vi = m_vars[var];        
        return !vi.m_lower_valid || em.gt(b, vi.m_lower);
    }

    template<typename Ext>
    bool simplex<Ext>::below_upper(var_t var, eps_numeral const& b) const {
        var_info const& vi = m_vars[var];        
        return !vi.m_upper_valid || em.lt(b, vi.m_upper);
    }

    template<typename Ext>
    void simplex<Ext>::set_lower(var_t var, eps_numeral const& b) {
        var_info& vi = m_vars[var];
        em.set(vi.m_lower, b);
        vi.m_lower_valid = true;
        TRACE("simplex", em.display(tout << "v" << var << " lower: ", b);
              em.display(tout << " value: ", vi.m_value););
        SASSERT(!vi.m_upper_valid || em.le(b, vi.m_upper));
        if (!vi.m_is_base && em.lt(vi.m_value, b)) {
            scoped_eps_numeral delta(em);
            em.sub(b, vi.m_value, delta);
            update_value(var, delta);
        }
        else if (vi.m_is_base && em.lt(vi.m_value, b)) {
            SASSERT(outside_bounds(var));
            add_patch(var);
        }
        SASSERT(well_formed());
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
        else if (vi.m_is_base && em.lt(b, vi.m_value)) {
            SASSERT(outside_bounds(var));
            add_patch(var);
        }
        SASSERT(well_formed());
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
        SASSERT(well_formed());
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
            out << "] ";
            if (vi.m_is_base) out << "b:" << vi.m_base2row << " ";
            //col_iterator it = M.col_begin(i), end = M.col_end(i);
            //for (; it != end; ++it) {
            //    out << "r" << it.get_row().id() << " ";
            //}
            out << "\n";
        }
    }

    template<typename Ext>
    void simplex<Ext>::display_row(std::ostream& out, row const& r, bool values) {
        row_iterator it = M.row_begin(r), end = M.row_end(r);        
        for (; it != end; ++it) {
            m.display(out, it->m_coeff);
            out << "*v" << it->m_var << " ";
            if (values) {
                var_info const& vi = m_vars[it->m_var];
                out << em.to_string(vi.m_value);
                out << " [";
                if (vi.m_lower_valid) out << em.to_string(vi.m_lower); else out << "-oo";
                out << ":";
                if (vi.m_upper_valid) out << em.to_string(vi.m_upper); else out << "oo";
                out << "] ";
            }
        }
        out << "\n";
    }


    template<typename Ext>
    void simplex<Ext>::ensure_var(var_t v) {
        while (v >= m_vars.size()) {
            M.ensure_var(m_vars.size());
            m_vars.push_back(var_info());            
        }
        if (m_to_patch.get_bounds() <= v) {
            m_to_patch.set_bounds(2*v+1);
        }
    }

    template<typename Ext>
    void simplex<Ext>::reset() {
        M.reset();
        m_to_patch.reset();
        for (var_info& v : m_vars) {
            em.del(v.m_value);
            em.del(v.m_lower);
            em.del(v.m_upper);
            m.del(v.m_base_coeff);
        }
        m_vars.reset();
        m_row2base.reset();
        m_left_basis.reset();
        m_base_vars.reset();
    }

    template<typename Ext>
    lbool simplex<Ext>::make_feasible() {
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
        ++m_stats.m_num_pivots;
        var_info& x_iI = m_vars[x_i];
        var_info& x_jI = m_vars[x_j];
        unsigned r_i = x_iI.m_base2row;
        m_row2base[r_i] = x_j;
        x_jI.m_base2row = r_i;
        m.set(x_jI.m_base_coeff, a_ij);
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
        if (is_base(v)) {
            add_patch(v);
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
            SASSERT(is_base(x_i));
            is_below = m.is_pos(m_vars[x_i].m_base_coeff);
            value = m_vars[x_i].m_lower;
        }
        else if (above_upper(x_i)) {
            SASSERT(is_base(x_i));
            is_below = m.is_neg(m_vars[x_i].m_base_coeff);
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
        int n = 0;
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
        // start with feasible assignment
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
        bool inc_x_i, inc_x_j;

        while (true) {
            if (!m_limit.inc()) {
                return l_undef;
            }
            select_pivot_primal(v, x_i, x_j, a_ij, inc_x_i, inc_x_j);
            if (x_j == null_var) {
                // optimal
                return l_true;
            }
            TRACE("simplex", tout << "x_i: v" << x_i << " x_j: v" << x_j << "\n";);
            var_info& vj = m_vars[x_j];
            if (x_i == null_var) {
                if (inc_x_j && vj.m_upper_valid) {
                    delta = vj.m_upper;
                    delta -= vj.m_value;
                    update_value(x_j, delta);
                }
                else if (!inc_x_j && vj.m_lower_valid) {
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
            TRACE("simplex", display(tout << "after pivot\n"););
            move_to_bound(x_i, !inc_x_i);
            SASSERT(well_formed_row(row(m_vars[x_j].m_base2row)));
            TRACE("simplex", display(tout););
            SASSERT(is_feasible());
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
        TRACE("simplex", tout << "move " << (to_lower?"to_lower":"to_upper") 
              << " v" << x << " delta: " << em.to_string(delta) << "\n";);
        col_iterator it = M.col_begin(x), end = M.col_end(x);
        for (; it != end && is_pos(delta); ++it) {
            //
            // base_coeff*s + coeff*x + R = 0
            // 
            // to_lower    coeff > 0    base_coeff > 0     bound(s)
            // ------------------------------------------------------
            // T           T            T                  !to_lower
            // T           T            F                   to_lower
            // T           F            T                   to_lower
            // T           F            F                  !to_lower
            //
            var_t s = m_row2base[it.get_row().id()];
            var_info& vs = m_vars[s];
            numeral const& coeff = it.get_row_entry().m_coeff;
            numeral const& base_coeff = vs.m_base_coeff;
            SASSERT(!m.is_zero(coeff));
            bool base_to_lower = (m.is_pos(coeff) != m.is_pos(base_coeff)) == to_lower;
            eps_numeral const* bound = nullptr;
            if (!base_to_lower && vs.m_upper_valid) {
                bound = &vs.m_upper;
            }
            else if (base_to_lower && vs.m_lower_valid) {
                bound = &vs.m_lower;
            }
            if (bound) {
                // |delta2*coeff| = |(bound-value)*base_coeff|
                em.sub(*bound, vs.m_value, delta2);
                em.mul(delta2, base_coeff, delta2);
                em.div(delta2, coeff, delta2);
                em.abs(delta2);
                TRACE("simplex", tout << "Delta for v" << s << " " << delta2 << "\n";);
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

    /**
       \brief 
       Arguments:
       v   - base variable of row(v) to optimize
       x_i - base variable of row(x_i) to become non-base
       x_j - variable in row(v) to make a base variable
       a_ij - coefficient to x_j in row(x_i)
       inc  - whether to increment x_i 
     */
    template<typename Ext>
    void simplex<Ext>::select_pivot_primal(var_t v, var_t& x_i, var_t& x_j, scoped_numeral& a_ij, 
                                           bool& inc_x_i, bool& inc_x_j) {
        row r(m_vars[v].m_base2row);
        row_iterator it = M.row_begin(r), end = M.row_end(r);
    
        scoped_eps_numeral gain(em), new_gain(em);
        scoped_numeral new_a_ij(m);
        x_i = null_var;
        x_j = null_var;
        inc_x_i = false;
        bool inc_y = false;

        for (; it != end; ++it) {
            var_t x = it->m_var;          
            if (x == v) continue; 
            bool inc_x = m.is_pos(it->m_coeff) == m.is_pos(m_vars[v].m_base_coeff);
            if ((inc_x && at_upper(x)) || (!inc_x && at_lower(x))) {
                TRACE("simplex", tout << "v" << x << " pos: " << inc_x 
                      << " at upper: " << at_upper(x) 
                      << " at lower: " << at_lower(x) << "\n";);
                continue; // variable cannot be used for improving bounds.
                // TBD check?
            }            
            var_t y = pick_var_to_leave(x, inc_x, new_gain, new_a_ij, inc_y);
            if (y == null_var) {
                // unbounded.
                x_i = y;
                x_j = x;
                inc_x_i = inc_y;
                inc_x_j = inc_x;
                a_ij = new_a_ij;
                break;
            }
            bool better = 
                (new_gain > gain) ||
                ((is_zero(new_gain) && is_zero(gain) && (x_i == null_var || y < x_i)));

            if (better) {
                TRACE("simplex", 
                      em.display(tout << "gain:", gain); 
                      em.display(tout << " new gain:", new_gain);
                      tout << " base x_i: " << y << ", new base x_j: " << x << ", inc x_j: " << inc_x << "\n";);

                x_i = y;
                x_j = x;
                inc_x_i = inc_y;
                inc_x_j = inc_x;
                gain = new_gain;
                a_ij = new_a_ij;
            }            
        }
    }

    //
    // y is a base variable.
    // v is a base variable.
    // v*a_v + x*a_x + E = 0
    // y*b_y + x*b_x + F = 0
    // inc(x)  := sign(a_v) == sign(a_x)
    // sign_eq := sign(b_y) == sign(b_x)
    // sign_eq => (inc(x) != inc(y))
    // !sign_eq => (inc(x) = inc(y))
    // -> 
    // inc(y) := sign_eq != inc(x)
    //

    template<typename Ext>
    typename simplex<Ext>::var_t 
    simplex<Ext>::pick_var_to_leave(
        var_t x_j, bool inc_x_j, 
        scoped_eps_numeral& gain, scoped_numeral& new_a_ij, bool& inc_x_i) {
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
            bool sign_eq = (m.is_pos(a_ii) == m.is_pos(a_ij));
            bool inc_s =  sign_eq != inc_x_j;
            TRACE("simplex", tout << "x_j: v" << x_j << ", base x_i: v" << s 
                  << ", inc_x_i: " << inc_s 
                  << ", inc_x_j: " << inc_x_j 
                  << ", upper valid:" << vi.m_upper_valid 
                  << ", lower valid:" << vi.m_lower_valid << "\n";
                  display_row(tout, r););
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
                inc_x_i = inc_s;
                TRACE("simplex", tout << "x_j v" << x_j << " x_i v" << x_i << " gain: ";
                      tout << curr_gain << "\n";);
            }
        }
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
            VERIFY(well_formed_row(row(i)));            
        }
        for (unsigned i = 0; i < m_vars.size(); ++i) {
            if (!is_base(i)) {
                SASSERT(!above_upper(i));
                SASSERT(!below_lower(i));
            }
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

    template<typename Ext>
    bool simplex<Ext>::well_formed_row(row const& r) const {
        var_t s = m_row2base[r.id()];
        (void)s;
        SASSERT(m_vars[s].m_base2row == r.id());
        SASSERT(m_vars[s].m_is_base);
        // SASSERT(m.is_neg(m_vars[s].m_base_coeff));
        row_iterator it = M.row_begin(r), end = M.row_end(r);
        scoped_eps_numeral sum(em), tmp(em);
        for (; it != end; ++it) {
            em.mul(m_vars[it->m_var].m_value, it->m_coeff, tmp);
            sum += tmp;
            SASSERT(s != it->m_var || m.eq(m_vars[s].m_base_coeff, it->m_coeff));
        }
        if (!em.is_zero(sum)) {
            IF_VERBOSE(0, M.display_row(verbose_stream(), r););
            TRACE("pb", display(tout << "non-well formed row\n"); M.display_row(tout << "row: ", r););
            throw default_exception("non-well formed row");
        }

        return true;
    }

    template<typename Ext>
    void simplex<Ext>::collect_statistics(::statistics & st) const {
        M.collect_statistics(st);
        st.update("simplex num pivots", m_stats.m_num_pivots);
        st.update("simplex num infeasible", m_stats.m_num_infeasible);
        st.update("simplex num checks", m_stats.m_num_checks);
    }
        

};


