/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_arith_aux.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-04-29.

Revision History:

--*/
#ifndef _THEORY_ARITH_AUX_H_
#define _THEORY_ARITH_AUX_H_

#include"theory_arith.h"

namespace smt {

    // -----------------------------------
    //
    // Rows
    //
    // -----------------------------------

    template<typename Ext>
    theory_arith<Ext>::row::row():
        m_size(0),
        m_base_var(null_theory_var),
        m_first_free_idx(-1) {
    }
    
    template<typename Ext>
    void theory_arith<Ext>::row::reset() {
        m_entries.reset();
        m_size           = 0;
        m_base_var       = -1;
        m_first_free_idx = -1;
    }
    
    /**
       \brief Add a new row_entry. The result is a reference to the new row_entry. The position of the new row_entry in the
       row is stored in pos_idx.
    */
    template<typename Ext>
    typename theory_arith<Ext>::row_entry & theory_arith<Ext>::row::add_row_entry(int & pos_idx) {
        m_size++;
        if (m_first_free_idx == -1) {
            pos_idx = m_entries.size();
            m_entries.push_back(row_entry());
            return m_entries.back();
        }
        else {
            pos_idx = m_first_free_idx;
            row_entry & result = m_entries[pos_idx];
            SASSERT(result.is_dead());
            m_first_free_idx = result.m_next_free_row_entry_idx;
            return result;
        }
    }

    /**
       \brief Delete row_entry at position idx.
    */
    template<typename Ext>
    void theory_arith<Ext>::row::del_row_entry(unsigned idx) {
        row_entry & t = m_entries[idx];
        SASSERT(!t.is_dead());
        t.m_next_free_row_entry_idx = m_first_free_idx;
        t.m_var = null_theory_var;
        m_size--;
        SASSERT(t.is_dead());
    }

    /**
       \brief Remove holes (i.e., dead entries) from the row. 
    */
    template<typename Ext>
    void theory_arith<Ext>::row::compress(vector<column> & cols) {
        unsigned i  = 0;
        unsigned j  = 0;
        unsigned sz = m_entries.size();
        for (; i < sz; i++) {
            row_entry & t1 = m_entries[i];
            if (!t1.is_dead()) {
                if (i != j) {
                    row_entry & t2 = m_entries[j];
                    t2.m_coeff.swap(t1.m_coeff);
                    t2.m_var = t1.m_var;
                    t2.m_col_idx = t1.m_col_idx;
                    SASSERT(!t2.is_dead());
                    column & col = cols[t2.m_var];
                    col[t2.m_col_idx].m_row_idx = j;
                }
                j++;
            }
        }
        SASSERT(j == m_size);
        m_entries.shrink(m_size);
        m_first_free_idx = -1;
    }
    
    /**
       \brief Invoke compress if the row contains too many holes (i.e., dead entries).
    */
    template<typename Ext>
    inline void theory_arith<Ext>::row::compress_if_needed(vector<column> & cols) {
        if (size() * 2 < num_entries()) {
            compress(cols);
        }
    }
    
    /**
       \brief Fill the map var -> pos/idx
    */
    template<typename Ext>
    inline void theory_arith<Ext>::row::save_var_pos(svector<int> & result_map) const {
        typename vector<row_entry>::const_iterator it  = m_entries.begin();
        typename vector<row_entry>::const_iterator end = m_entries.end();
        unsigned idx = 0;
        for (; it != end; ++it, ++idx) {
            if (!it->is_dead()) {
                result_map[it->m_var] = idx;
            }
        }
    }
    
    /**
       \brief Reset the map var -> pos/idx. That is for all variables v in the row, set result[v] = -1
       This method can be viewed as the "inverse" of save_var_pos.
    */
    template<typename Ext>
    inline void theory_arith<Ext>::row::reset_var_pos(svector<int> & result_map) const {
        typename vector<row_entry>::const_iterator it  = m_entries.begin();
        typename vector<row_entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                result_map[it->m_var] = -1;
            }
        }
    };
    
#ifdef Z3DEBUG
    /**
       \brief Return true if the coefficient of v in the row is equals to 'expected'.
    */
    template<typename Ext>
    bool theory_arith<Ext>::row::is_coeff_of(theory_var v, numeral const & expected) const {
        typename vector<row_entry>::const_iterator it  = m_entries.begin();
        typename vector<row_entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            if (!it->is_dead() && it->m_var == v) {
                return it->m_coeff == expected;
            }
        }
        return false;
    }
#endif

    template<typename Ext>
    void theory_arith<Ext>::row::display(std::ostream & out) const {
        out << "v" << m_base_var << ", ";
        typename vector<row_entry>::const_iterator it  = m_entries.begin();
        typename vector<row_entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                out << it->m_coeff << "*v" << it->m_var << " ";
            }
        }
        out << "\n";
    }

    template<typename Ext>
    typename theory_arith<Ext>::numeral theory_arith<Ext>::row::get_denominators_lcm() const {
        numeral r(1);
        TRACE("lcm_bug", tout << "starting get_denominators_lcm...\n";);
        typename vector<row_entry>::const_iterator it  = m_entries.begin();
        typename vector<row_entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                r = lcm(r, denominator(it->m_coeff));
                TRACE("lcm_bug", tout << "it->m_coeff: " << it->m_coeff << ", denominator(it->m_coeff): " << denominator(it->m_coeff) << ", r: " << r << "\n";);
            }
        }
        return r;
    }
    
    template<typename Ext>
    int theory_arith<Ext>::row::get_idx_of(theory_var v) const {
        typename vector<row_entry>::const_iterator it  = m_entries.begin();
        typename vector<row_entry>::const_iterator end = m_entries.end();
        for (unsigned idx = 0; it != end; ++it, ++idx) {
            if (!it->is_dead() && it->m_var == v)
                return idx;
        }
        return -1;
    }

    // -----------------------------------
    //
    // Columns
    //
    // -----------------------------------
    
    template<typename Ext>
    void theory_arith<Ext>::column::reset() {
        m_entries.reset();
        m_size           = 0;
        m_first_free_idx = -1;
    }
    
    /**
       \brief Remove holes (i.e., dead entries) from the column.
    */
    template<typename Ext>
    void theory_arith<Ext>::column::compress(vector<row> & rows) {
        unsigned i  = 0;
        unsigned j  = 0;
        unsigned sz = m_entries.size();
        for (; i < sz; i++) {
            col_entry & e1 = m_entries[i];
            if (!e1.is_dead()) {
                if (i != j) {
                    m_entries[j] = e1;
                    row & r = rows[e1.m_row_id];
                    r[e1.m_row_idx].m_col_idx = j;
                }
                j++;
            }
        }
        SASSERT(j == m_size);
        m_entries.shrink(m_size);
        m_first_free_idx = -1;
    }
    
    /**
       \brief Invoke compress if the column contains too many holes (i.e., dead entries).
    */
    template<typename Ext>
    inline void theory_arith<Ext>::column::compress_if_needed(vector<row> & rows) {
        if (size() * 2 < num_entries()) {
            compress(rows);
        }
    }

    /**
       \brief Special version of compress, that is used when the column contain
       only one entry located at position singleton_pos.
    */
    template<typename Ext>
    void theory_arith<Ext>::column::compress_singleton(vector<row> & rows, unsigned singleton_pos) {
        SASSERT(m_size == 1);
        if (singleton_pos != 0) {
            col_entry & s  = m_entries[singleton_pos];
            m_entries[0]   = s;
            row & r        = rows[s.m_row_id];
            r[s.m_row_idx].m_col_idx = 0;
        }
        m_first_free_idx = -1;
        m_entries.shrink(1);
    }
    
    template<typename Ext>
    const typename theory_arith<Ext>::col_entry * theory_arith<Ext>::column::get_first_col_entry() const {
        typename svector<col_entry>::const_iterator it  = m_entries.begin();
        typename svector<col_entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                return it;
            }
        }
        return 0;
    }

    template<typename Ext>
    typename theory_arith<Ext>::col_entry & theory_arith<Ext>::column::add_col_entry(int & pos_idx) {
        m_size++;
        if (m_first_free_idx == -1) {
            pos_idx = m_entries.size();
            m_entries.push_back(col_entry());
            return m_entries.back();
        }
        else {
            pos_idx            = m_first_free_idx;
            col_entry & result = m_entries[pos_idx];
            SASSERT(result.is_dead());
            m_first_free_idx = result.m_next_free_row_entry_idx;
            return result;
        }
    }
    
    template<typename Ext>
    void theory_arith<Ext>::column::del_col_entry(unsigned idx) {
        col_entry & c = m_entries[idx];
        SASSERT(!c.is_dead());
        c.m_row_id                  = dead_row_id;
        c.m_next_free_row_entry_idx = m_first_free_idx;
        m_first_free_idx            = idx;
        m_size--;
    }

    // -----------------------------------
    //
    // Antecedents
    //
    // -----------------------------------

    template<typename Ext>
    void theory_arith<Ext>::antecedents::init() {
        if (!m_init && !empty()) {
            m_params.push_back(parameter(symbol("unknown-arith")));
            for (unsigned i = 0; i < m_lits.size(); i++) {
                m_params.push_back(parameter(m_lit_coeffs[i].to_rational()));
            }
            for (unsigned i = 0; i < m_eqs.size(); i++) {
                m_params.push_back(parameter(m_eq_coeffs[i].to_rational()));
            }
            m_init = true;
        }                
    }

    template<typename Ext>
    void theory_arith<Ext>::antecedents::reset() { 
        m_init = false; 
        m_eq_coeffs.reset();
        m_lit_coeffs.reset();
        m_eqs.reset(); 
        m_lits.reset(); 
        m_params.reset(); 
    }

    template<typename Ext>
    void theory_arith<Ext>::antecedents::push_lit(literal l, numeral const& r) { 
        m_lits.push_back(l);
        if (proofs_enabled) {
            m_lit_coeffs.push_back(r); 
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::antecedents::push_eq(enode_pair const& p, numeral const& r) { 
        m_eqs.push_back(p);
        if (proofs_enabled) {
            m_eq_coeffs.push_back(r); 
        }
    }

    template<typename Ext>
    parameter * theory_arith<Ext>::antecedents::params(char const* name) {
        if (empty()) return 0;
        init();
        m_params[0] = parameter(symbol(name));
        return m_params.c_ptr();
    }

    // -----------------------------------
    //
    // Atoms
    //
    // -----------------------------------

    template<typename Ext>
    theory_arith<Ext>::atom::atom(bool_var bv, theory_var v, numeral const & k, atom_kind kind):
        bound(v, inf_numeral::zero(), B_LOWER, true),
        m_bvar(bv),
        m_k(k),
        m_atom_kind(kind),
        m_is_true(false) {
    }

    template<typename Ext>
    void theory_arith<Ext>::atom::assign_eh(bool is_true, inf_numeral const & epsilon) {
        m_is_true     = is_true;
        if (is_true) {
            this->m_value = m_k;
            this->m_bound_kind = static_cast<bound_kind>(m_atom_kind);
            SASSERT((this->m_bound_kind == B_LOWER) == (m_atom_kind == A_LOWER));
        }
        else {
            if (get_atom_kind() == A_LOWER) {
                this->m_value       = m_k;
                this->m_value      -= epsilon;
                this->m_bound_kind  = B_UPPER;
            }
            else {
                SASSERT(get_atom_kind() == A_UPPER);
                this->m_value       = m_k;
                this->m_value      += epsilon;
                this->m_bound_kind  = B_LOWER;
            }
        }
    }

    // -----------------------------------
    //
    // Auxiliary methods
    //
    // -----------------------------------

    template<typename Ext>
    bool theory_arith<Ext>::at_bound(theory_var v) const {
        bound * l = lower(v);
        if (l != 0 && get_value(v) == l->get_value())
            return true;
        bound * u = upper(v);
        return u != 0 && get_value(v) == u->get_value();
    }

    template<typename Ext>
    bool theory_arith<Ext>::is_fixed(theory_var v) const {
        bound * l = lower(v);
        if (l == 0)
            return false;
        bound * u = upper(v);
        if (u == 0) 
            return false;
        return l->get_value() == u->get_value();
    }

    template<typename Ext>
    void theory_arith<Ext>::set_bound(bound * new_bound, bool upper) {
        SASSERT(new_bound);
        SASSERT(!upper || new_bound->get_bound_kind() == B_UPPER);
        SASSERT(upper  || new_bound->get_bound_kind() == B_LOWER);
        theory_var v = new_bound->get_var();
        set_bound_core(v, new_bound, upper);
        if ((propagate_eqs() || propagate_diseqs()) && is_fixed(v))
            fixed_var_eh(v);
    }
    


    /**
       \brief Return the col_entry that points to a base row that contains the given variable.
       Return 0 if no row contains v.
    */
    template<typename Ext>
    typename theory_arith<Ext>::col_entry const * theory_arith<Ext>::get_a_base_row_that_contains(theory_var v) {
        while (true) {
            column const & c = m_columns[v];
            if (c.size() == 0)
                return 0;
            int quasi_base_rid = -1;
            typename svector<col_entry>::const_iterator it  = c.begin_entries();
            typename svector<col_entry>::const_iterator end = c.end_entries();
            for (; it != end; ++it) {
                if (!it->is_dead()) {
                    unsigned rid = it->m_row_id;
                    row & r = m_rows[rid];
                    if (is_base(r.get_base_var()))
                        return it;
                    else if (quasi_base_rid == -1)
                        quasi_base_rid = rid;
                }
            }
            SASSERT(quasi_base_rid != -1); // since c.size() != 0
            quasi_base_row2base_row(quasi_base_rid);
            // There is no guarantee that v is still a variable of row quasi_base_rid.

            // However, this loop will always terminate since I'm creating
            // a base row that contains v, or decreasing c.size().
        }
    }

    /**
       \brief Return true if all coefficients of the given row are int.
    */
    template<typename Ext>
    bool theory_arith<Ext>::all_coeff_int(row const & r) const {
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {                                                                                   
            if (!it->is_dead() && !it->m_coeff.is_int())
                TRACE("gomory_cut", display_row(tout, r, true););
                return false;
        }
        return true;
    }

    /**
       \brief Return the col_entry that points to row that contains the given variable.
       This row should not be owned by an unconstrained quasi-base variable.
       Return 0 if failed.
       
       This method is used by move_unconstrained_to_base
    */
    template<typename Ext>
    typename theory_arith<Ext>::col_entry const * theory_arith<Ext>::get_row_for_eliminating(theory_var v) const {
        column const & c = m_columns[v];
        if (c.size() == 0)
            return 0;
        typename svector<col_entry>::const_iterator it  = c.begin_entries();
        typename svector<col_entry>::const_iterator end = c.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                row const & r = m_rows[it->m_row_id];
                theory_var s  = r.get_base_var();
                if (is_quasi_base(s) && m_var_occs[s].size() == 0)
                    continue;
                if (is_int(v)) {
                    numeral const & c = r[it->m_row_idx].m_coeff;
                    // If c == 1 or c == -1, and all other coefficients of r are integer,
                    // then if we pivot v with the base var of r, we will produce a row
                    // that will guarantee an integer assignment for v, when the 
                    // non-base vars have integer assignment.
                    if (!c.is_one() && !c.is_minus_one())
                        continue; 
                    if (!all_coeff_int(r))
                        continue;
                }
                return it;
            }
        }
        return 0;
    }

    template<typename Ext>
    void theory_arith<Ext>::move_unconstrained_to_base() {
        if (lazy_pivoting_lvl() == 0)
            return;
        TRACE("move_unconstrained_to_base", tout << "before...\n"; display(tout););
        int num = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            if (m_var_occs[v].size() == 0 && is_free(v)) {
                switch (get_var_kind(v)) {
                case QUASI_BASE:
                    break;
                case BASE:
                    if (is_int(v) && !all_coeff_int(m_rows[get_var_row(v)]))
                        // If the row contains non integer coefficients, then v may be assigned
                        // to a non-integer value even if all non-base variables are integer.
                        // So, v should not be "eliminated"
                        break; 
                    eliminate<false>(v, m_eager_gcd);
                    break;
                case NON_BASE: {
                    col_entry const * entry = get_row_for_eliminating(v);
                    if (entry) {
                        TRACE("move_unconstrained_to_base", tout << "moving v" << v << " to the base\n";);
                        row & r = m_rows[entry->m_row_id];
                        SASSERT(r[entry->m_row_idx].m_var == v);
                        pivot<false>(r.get_base_var(), v, r[entry->m_row_idx].m_coeff, m_eager_gcd);
                        SASSERT(is_base(v));                    
                        set_var_kind(v, QUASI_BASE);
                        SASSERT(is_quasi_base(v));                    
                    }
                    break;
                } }
            }
        }
        TRACE("move_unconstrained_to_base", tout << "after...\n"; display(tout););
        CASSERT("arith", wf_rows());
        CASSERT("arith", wf_columns());
        CASSERT("arith", valid_row_assignment());
    }
    
    /**
       \brief Force all quasi_base rows to become base rows.
    */
    template<typename Ext>
    void theory_arith<Ext>::elim_quasi_base_rows() {
        int num = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            if (is_quasi_base(v)) {
                quasi_base_row2base_row(get_var_row(v));
            }
        }
    }

    /**
       \brief Remove fixed vars from the base.
    */
    template<typename Ext>
    void theory_arith<Ext>::remove_fixed_vars_from_base() {
        int num = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            if (is_base(v) && is_fixed(v)) {
                row const & r = m_rows[get_var_row(v)];
                typename vector<row_entry>::const_iterator it  = r.begin_entries();
                typename vector<row_entry>::const_iterator end = r.end_entries();
                for (; it != end; ++it) {
                    if (!it->is_dead() && it->m_var != v && !is_fixed(it->m_var)) {
                        break;
                    }
                }
                if (it != end) {
                    pivot<true>(v, it->m_var, it->m_coeff, false);
                }
            }
        }
    }

    /**
       \brief Try to minimize the number of rational coefficients.
       The idea is to pivot x_i and x_j whenever there is a row
       
       x_i + 1/n * x_j + ... = 0

       where
       - x_i is a base variable
       - x_j is a non-base variables
       - x_j is not a fixed variable
       - The denominator of any other coefficient a_ik divides n (I only consider the coefficient of non-fixed variables)
       
       remark if there are more than one variable with such properties, we give preference to free variables,
       then to variables where upper - lower is maximal.
    */
    template<typename Ext>
    void theory_arith<Ext>::try_to_minimize_rational_coeffs() {
        int num = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            if (!is_base(v) || !is_int(v))
                continue;
            numeral max_den;
            row const & r = m_rows[get_var_row(v)];
            typename vector<row_entry>::const_iterator it  = r.begin_entries();
            typename vector<row_entry>::const_iterator end = r.end_entries();
            for (; it != end; ++it) {
                if (it->is_dead())
                    continue;
                if (it->m_var == v)
                    continue;
                if (is_fixed(it->m_var))
                    continue;
                numeral num = numerator(it->m_coeff);
                if (!num.is_one() && !num.is_minus_one())
                    continue;
                numeral den = denominator(it->m_coeff);
                if (den > max_den)
                    max_den = den;
            }
            if (max_den <= numeral(1))
                continue;
            // check whether all a_ik denominators divide max_den
            it  = r.begin_entries();
            for (; it != end; ++it) {
                if (it->is_dead())
                    continue;
                if (is_fixed(it->m_var))
                    continue;
                numeral den = denominator(it->m_coeff);
                if (!(max_den / den).is_int())
                    break;
            }
            if (it != end)
                continue;
            // pick best candidate
            theory_var x_j   = null_theory_var;
            numeral    a_ij;
            it  = r.begin_entries();
            for (; it != end; ++it) {
                if (it->is_dead())
                    continue;
                if (it->m_var == v)
                    continue;
                if (is_fixed(it->m_var))
                    continue;
                numeral num = numerator(it->m_coeff);
                if (!num.is_one() && !num.is_minus_one())
                    continue;
                numeral den = denominator(it->m_coeff);
                if (den != max_den)
                    continue;
                if (x_j == null_theory_var ||
                    // TODO: add extra cases...
                    is_free(it->m_var)           ||
                    (is_bounded(x_j) && !is_bounded(it->m_var)) ||
                    (is_bounded(x_j) && is_bounded(it->m_var) && (upper_bound(x_j) - lower_bound(x_j) > upper_bound(it->m_var) - lower_bound(it->m_var)))) {
                    x_j  = it->m_var;
                    a_ij = it->m_coeff;
                    if (is_free(x_j))
                        break;
                }
            }
            if (x_j != null_theory_var) 
                pivot<true>(v, x_j, a_ij, false);
        }
    }

    // -----------------------------------
    //
    // Derived bounds
    //
    // -----------------------------------

    template<typename Ext>
    void theory_arith<Ext>::derived_bound::push_justification(antecedents& a, numeral const& coeff) {

        if (proofs_enabled) {
            for (unsigned i = 0; i < m_lits.size(); ++i) {
                a.push_lit(m_lits[i], coeff);
            }
            for (unsigned i = 0; i < m_eqs.size(); ++i) {
                a.push_eq(m_eqs[i], coeff);
            }
        }
        else {
            a.lits().append(m_lits.size(), m_lits.c_ptr());
            a.eqs().append(m_eqs.size(), m_eqs.c_ptr());
        }
    }


    template<typename Ext>
    void theory_arith<Ext>::justified_derived_bound::push_justification(antecedents& a, numeral const& coeff) {
        for (unsigned i = 0; i < this->m_lits.size(); ++i) {
            a.push_lit(this->m_lits[i], coeff*m_lit_coeffs[i]);
        }
        for (unsigned i = 0; i < this->m_eqs.size(); ++i) {
            a.push_eq(this->m_eqs[i], coeff*m_eq_coeffs[i]);
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::justified_derived_bound::push_lit(literal l, numeral const& coeff) {
        for (unsigned i = 0; i < this->m_lits.size(); ++i) {
            if (this->m_lits[i] == l) {
                m_lit_coeffs[i] += coeff;
                return;
            }
        }
        this->m_lits.push_back(l);
        m_lit_coeffs.push_back(coeff);
    }

    template<typename Ext>
    void theory_arith<Ext>::justified_derived_bound::push_eq(enode_pair const& p, numeral const& coeff) {
        for (unsigned i = 0; i < this->m_eqs.size(); ++i) {
            if (this->m_eqs[i] == p) {
                m_eq_coeffs[i] += coeff;
                return;
            }
        }
        this->m_eqs.push_back(p);
        m_eq_coeffs.push_back(coeff);
    }

    /**
       \brief Copy the justification of b to new_bound. Only literals and equalities not in lits and eqs are copied.
       The justification of b is also copied to lits and eqs.
    */
    template<typename Ext>
    void theory_arith<Ext>::accumulate_justification(bound & b, derived_bound& new_bound, numeral const& coeff, literal_idx_set & lits, eq_set & eqs) {
        antecedents& ante = m_tmp_antecedents;
        ante.reset();
        b.push_justification(ante, coeff);
        unsigned num_lits = ante.lits().size();
        for (unsigned i = 0; i < num_lits; ++i) {
            literal l = ante.lits()[i];
            if (lits.contains(l.index()))
                continue;
            if (proofs_enabled) {
                new_bound.push_lit(l, ante.lit_coeffs()[i]);
            }			
            else {
                new_bound.push_lit(l, numeral::zero());
                lits.insert(l.index());
            }
        }
        unsigned num_eqs = ante.eqs().size();
        for (unsigned i = 0; i < num_eqs; ++i) {
            enode_pair const & p = ante.eqs()[i];
            if (eqs.contains(p))
                continue;
            if (proofs_enabled) {
                new_bound.push_eq(p, ante.eq_coeffs()[i]);
            }
            else {
                new_bound.push_eq(p, numeral::zero());
                eqs.insert(p);
            }
        }
    }

    
    
    template<typename Ext>
    typename theory_arith<Ext>::inf_numeral theory_arith<Ext>::normalize_bound(theory_var v, inf_numeral const & k, bound_kind kind) {
        if (is_real(v))
            return k;
        if (kind == B_LOWER)
            return inf_numeral(ceil(k));
        SASSERT(kind == B_UPPER);
        return inf_numeral(floor(k));
    }

    /**
       \brief Create a derived bound for v using the given row as an explanation.
    */
    template<typename Ext>
    void theory_arith<Ext>::mk_bound_from_row(theory_var v, inf_numeral const & k, bound_kind kind, row const & r) {
        inf_numeral k_norm = normalize_bound(v, k, kind);
        derived_bound * new_bound = proofs_enabled?alloc(justified_derived_bound, v, k_norm, kind):alloc(derived_bound, v, k_norm, kind);
        m_bounds_to_delete.push_back(new_bound);
        m_asserted_bounds.push_back(new_bound);
        m_tmp_lit_set.reset();
        m_tmp_eq_set.reset();
#ifdef Z3DEBUG
        inf_numeral val;
#endif 
        typename vector<row_entry>::const_iterator it  = r.begin_entries();  
        typename vector<row_entry>::const_iterator end = r.end_entries();                
        for (; it != end; ++it) {
            if (!it->is_dead()) { 
                theory_var v = it->m_var;
                bool use_upper = (kind == B_UPPER);
                if (!it->m_coeff.is_pos())
                    use_upper = !use_upper;
                TRACE("derived_bound", tout << "using " << (use_upper ? "upper" : "lower") << " bound of v" << v << "\n";);
                bound * b  = get_bound(v, use_upper);
                SASSERT(b);
                DEBUG_CODE({
                    inf_numeral tmp = b->get_value();
                    tmp *= it->m_coeff;
                    val += tmp;
                });
                accumulate_justification(*b, *new_bound, it->m_coeff, m_tmp_lit_set, m_tmp_eq_set);
            }
        }
        TRACE("derived_bound", 
              tout << "explanation:\n";
              literal_vector::const_iterator it1  = new_bound->m_lits.begin();
              literal_vector::const_iterator end1 = new_bound->m_lits.end();
              for (; it1 != end1; ++it1) tout << *it1 << " ";
              tout << " ";
              eq_vector::const_iterator it2  = new_bound->m_eqs.begin();
              eq_vector::const_iterator end2 = new_bound->m_eqs.end();
              for (; it2 != end2; ++it2) tout << "#" << it2->first->get_owner_id() << "=#" << it2->second->get_owner_id() << " ";
              tout << "\n";);
        DEBUG_CODE(CTRACE("derived_bound", k != val, tout << "k: " << k << ", k_norm: " << k_norm << ", val: " << val << "\n";););
        SASSERT(k == val);
    }

    // -----------------------------------
    //
    // Maximization/Minimization 
    //
    // -----------------------------------

    /**
       \brief Set: row1 <- row1 + coeff * row2,
       where row1 is a temporary row.
       
       \remark Columns do not need to be updated when updating a temporary row.
    */
    template<typename Ext>
    void theory_arith<Ext>::add_tmp_row(row & r1, numeral const & coeff, row const & r2) {
        r1.save_var_pos(m_var_pos);

        // 
        // loop over variables in row2,
        // add terms in row2 to row1.
        //
#define ADD_TMP_ROW(_SET_COEFF_, _ADD_COEFF_)                                   \
    typename vector<row_entry>::const_iterator it  = r2.begin_entries();        \
    typename vector<row_entry>::const_iterator end = r2.end_entries();          \
    for (; it != end; ++it) {                                                   \
        if (!it->is_dead()) {                                                   \
            theory_var v = it->m_var;                                           \
            int pos  = m_var_pos[v];                                            \
            if (pos == -1) {                                                    \
                /* variable v is not in row1 */                                 \
                int row_idx;                                                    \
                row_entry & r_entry = r1.add_row_entry(row_idx);                \
                r_entry.m_var         = v;                                      \
                _SET_COEFF_;                                                    \
            }                                                                   \
            else {                                                              \
                /* variable v is in row1 */                                     \
                row_entry & r_entry   = r1[pos];                                \
                SASSERT(r_entry.m_var == v);                                    \
                _ADD_COEFF_;                                                    \
                if (r_entry.m_coeff.is_zero()) {                                \
                    r1.del_row_entry(pos);                                      \
                }                                                               \
                m_var_pos[v] = -1;                                              \
            }                                                                   \
        }                                                                       \
    } ((void) 0)

        if (coeff.is_one()) {
            ADD_TMP_ROW(r_entry.m_coeff  = it->m_coeff,
                        r_entry.m_coeff += it->m_coeff);
        }
        else if (coeff.is_minus_one()) {
            ADD_TMP_ROW(r_entry.m_coeff  = it->m_coeff; r_entry.m_coeff.neg(),
                        r_entry.m_coeff -= it->m_coeff);
        }
        else {
            ADD_TMP_ROW(r_entry.m_coeff = it->m_coeff; r_entry.m_coeff *= coeff, 
                        r_entry.m_coeff += it->m_coeff * coeff);
        }
     
        r1.reset_var_pos(m_var_pos);
    }

    /**
       \brief Select tightest variable x_i to pivot with x_j. The goal
       is to select a x_i such that the value of x_j is increased
       (decreased) if inc = true (inc = false), and the tableau
       remains feasible. Store the gain in x_j of the pivoting
       operation in 'gain'. Note the gain can be too much. That is,
       it may make x_i infeasible. In this case, instead of pivoting
       we move x_j to its upper bound (lower bound) when inc = true (inc = false).
       
       If no x_i imposes a restriction on x_j, then return null_theory_var.
       That is, x_j is free to move to its upper bound (lower bound).
    */
    template<typename Ext>
    theory_var theory_arith<Ext>::pick_var_to_leave(theory_var x_j, bool inc, numeral & a_ij, inf_numeral & gain) {
        TRACE("maximize", tout << "selecting variable to replace v" << x_j << ", inc: " << inc << "\n";);
        theory_var x_i  = null_theory_var;
        inf_numeral curr_gain; 
        column & c      = m_columns[x_j];
        typename svector<col_entry>::iterator it  = c.begin_entries();
        typename svector<col_entry>::iterator end = c.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                row & r        = m_rows[it->m_row_id];
                theory_var s = r.get_base_var();
                if (s != null_theory_var && !is_quasi_base(s)) {
                    numeral const & coeff = r[it->m_row_idx].m_coeff;
                    bool inc_s = coeff.is_neg() ? inc : !inc;
                    bound * b  = get_bound(s, inc_s);
                    if (b) {
                        curr_gain  = get_value(s);
                        curr_gain -= b->get_value();
                        curr_gain /= coeff;
                        if (curr_gain.is_neg())
                            curr_gain.neg();
                        if (x_i == null_theory_var || (curr_gain < gain) || (gain.is_zero() && curr_gain.is_zero() && s < x_i)) {
                            x_i  = s;
                            a_ij = coeff;
                            gain = curr_gain;
                        }
                    }
                }
                TRACE("maximize", tout << "x_j: v" << x_i << ", gain: " << gain << "\n";);
            }
        }
        TRACE("maximize", tout << "x_i v" << x_i << "\n";);
        return x_i;
    }

    /**
       \brief Maximize (Minimize) the given temporary row.
       Return true if succeeded.
    */
    template<typename Ext>
    bool theory_arith<Ext>::max_min(row & r, bool max) {
        TRACE("max_min", tout << "max_min...\n";);
        m_stats.m_max_min++;

        SASSERT(valid_row_assignment());
        SASSERT(satisfy_bounds());

        theory_var x_i = null_theory_var;
        theory_var x_j = null_theory_var;
        bool inc       = false;
        numeral a_ij, curr_a_ij, coeff, curr_coeff;
        inf_numeral curr_gain, gain;
#ifdef _TRACE
        unsigned i = 0;
#endif
        while (true) {
            x_j = null_theory_var;
            x_i = null_theory_var;
            gain.reset();
            TRACE("maximize", tout << "i: " << i << ", max: " << max << "\n"; display_row(tout, r, true); tout << "state:\n"; display(tout); i++;);
            typename vector<row_entry>::const_iterator it  = r.begin_entries();
            typename vector<row_entry>::const_iterator end = r.end_entries();
            for (; it != end; ++it) {  
                if (!it->is_dead()) {                                                  
                    theory_var curr_x_j = it->m_var;
                    SASSERT(is_non_base(curr_x_j));
                    curr_coeff    = it->m_coeff;
                    bool curr_inc = curr_coeff.is_pos() ? max : !max; 
                    if ((curr_inc && at_upper(curr_x_j)) || (!curr_inc && at_lower(curr_x_j)))
                        continue; // variable cannot be used for max/min.
                    theory_var curr_x_i = pick_var_to_leave(curr_x_j, curr_inc, curr_a_ij, curr_gain);
                    if (curr_x_i == null_theory_var) {
                        // we can increase/decrease curr_x_j as much as we want.
                        x_i   = null_theory_var; // unbounded
                        x_j   = curr_x_j;
                        inc   = curr_inc;
                        break;
                    }
                    else if (curr_gain > gain) {
                        x_i   = curr_x_i;
                        x_j   = curr_x_j;
                        a_ij  = curr_a_ij;
                        coeff = curr_coeff;
                        gain  = curr_gain;
                        inc   = curr_inc;
                    }
                    else if (curr_gain.is_zero() && (x_i == null_theory_var || curr_x_i < x_i)) {
                        x_i   = curr_x_i;
                        x_j   = curr_x_j;
                        a_ij  = curr_a_ij;
                        coeff = curr_coeff;
                        gain  = curr_gain;
                        inc   = curr_inc;
                        // continue
                    }
                }
            }
            TRACE("maximize", tout << "after traversing row:\nx_i: v" << x_i << ", x_j: v" << x_j << ", gain: " << gain << "\n";);

            if (x_j == null_theory_var) {
                TRACE("maximize", tout << "row is " << (max ? "maximized" : "minimized") << "\n";);
                SASSERT(valid_row_assignment());
                SASSERT(satisfy_bounds());
                return true;
            }

            if (x_i == null_theory_var) {
                // can increase/decrease x_j as much as we want.
                if (inc && upper(x_j)) {
                    update_value(x_j, upper_bound(x_j) - get_value(x_j));
                    TRACE("maximize", tout << "moved v" << x_j << " to upper bound\n";);
                    SASSERT(valid_row_assignment());
                    SASSERT(satisfy_bounds());
                    continue;
                }
                if (!inc && lower(x_j)) {
                    update_value(x_j, lower_bound(x_j) - get_value(x_j));
                    TRACE("maximize", tout << "moved v" << x_j << " to lower bound\n";);
                    SASSERT(valid_row_assignment());
                    SASSERT(satisfy_bounds());
                    continue;
                }
                return false; // unbounded.
            }

            if (!is_fixed(x_j) && is_bounded(x_j) && (upper_bound(x_j) - lower_bound(x_j) <= gain)) {
                // can increase/decrease x_j up to upper/lower bound.
                if (inc) {
                    update_value(x_j, upper_bound(x_j) - get_value(x_j));
                    TRACE("maximize", tout << "moved v" << x_j << " to upper bound\n";);
                }
                else {
                    update_value(x_j, lower_bound(x_j) - get_value(x_j));
                    TRACE("maximize", tout << "moved v" << x_j << " to lower bound\n";);
                }
                SASSERT(valid_row_assignment());
                SASSERT(satisfy_bounds());
                continue;
            }

            TRACE("maximize", tout << "max: " << max << ", x_i: v" << x_i << ", x_j: v" << x_j << ", a_ij: " << a_ij << ", coeff: " << coeff << "\n";);
            bool move_xi_to_lower;
            if (inc) 
                move_xi_to_lower = a_ij.is_pos();
            else
                move_xi_to_lower = a_ij.is_neg();
            pivot<true>(x_i, x_j, a_ij, false);
            SASSERT(is_non_base(x_i));
            SASSERT(is_base(x_j));
            if (move_xi_to_lower)
                update_value(x_i, lower_bound(x_i) - get_value(x_i));
            else
                update_value(x_i, upper_bound(x_i) - get_value(x_i));
            row & r2 = m_rows[get_var_row(x_j)];
            coeff.neg();
            add_tmp_row(r, coeff, r2);
            SASSERT(r.get_idx_of(x_j) == -1);
            SASSERT(valid_row_assignment());
            SASSERT(satisfy_bounds());
        }
    }

    /**
       \brief Add an entry to a temporary row.
       
       \remark Columns do not need to be updated when updating a temporary row.
    */
    template<typename Ext>
    template<bool invert>
    void theory_arith<Ext>::add_tmp_row_entry(row & r, numeral const & coeff, theory_var v) {
        int r_idx;
        row_entry & r_entry = r.add_row_entry(r_idx);
        r_entry.m_var       = v;
        r_entry.m_coeff     = coeff;
        if (invert)
            r_entry.m_coeff .neg();
    }

    /**
       \brief Maximize/Minimize the given variable. The bounds of v are update if procedure succeeds.
    */
    template<typename Ext>
    bool theory_arith<Ext>::max_min(theory_var v, bool max) { 
        TRACE("maximize", tout << (max ? "maximizing" : "minimizing") << " v" << v << "...\n";);
        SASSERT(valid_row_assignment());
        SASSERT(satisfy_bounds());
        SASSERT(!is_quasi_base(v));
        if ((max && at_upper(v)) || (!max && at_lower(v)))
            return false; // nothing to be done...
        m_tmp_row.reset();
        if (is_non_base(v)) {
            add_tmp_row_entry<false>(m_tmp_row, numeral(1), v);
        }
        else {
            row & r = m_rows[get_var_row(v)];
            typename vector<row_entry>::const_iterator it  = r.begin_entries();
            typename vector<row_entry>::const_iterator end = r.end_entries();
            for (; it != end; ++it) {  
                if (!it->is_dead() && it->m_var != v)                          
                    add_tmp_row_entry<true>(m_tmp_row, it->m_coeff, it->m_var);
            }            
        }
        if (max_min(m_tmp_row, max)) {
            TRACE("maximize", tout << "v" << v << " " << (max ? "max" : "min") << " value is: " << get_value(v) << "\n";
                  display_row(tout, m_tmp_row, true); display_row_info(tout, m_tmp_row););
            
            mk_bound_from_row(v, get_value(v), max ? B_UPPER : B_LOWER, m_tmp_row);
            return true;
        }
        return false;
    }

    /**
       \brief Maximize & Minimize variables in vars.
       Return false if an inconsistency was detected.
    */
    template<typename Ext>
    bool theory_arith<Ext>::max_min(svector<theory_var> const & vars) { 
        bool succ = false;
        svector<theory_var>::const_iterator it  = vars.begin();
        svector<theory_var>::const_iterator end = vars.end();
        for (; it != end; ++it) {
            if (max_min(*it, true))
                succ = true;
            if (max_min(*it, false))
                succ = true;
        }
        if (succ) {
            // process new bounds
            bool r = propagate_core();
            TRACE("maximize", tout << "after max/min round:\n"; display(tout););
            return r;
        }
        return true;
    }

    // -----------------------------------
    //
    // Freedom intervals
    //
    // -----------------------------------
    
    /**
       \brief See Model-based theory combination paper.
       Return false if failed to build the freedom interval.
       
       \remark If x_j is an integer variable, then m will contain the lcm of the denominators of a_ij.
       We only consider the a_ij coefficients for x_i 
    */
    template<typename Ext>
    bool theory_arith<Ext>::get_freedom_interval(theory_var x_j, bool & inf_l, inf_numeral & l, bool & inf_u, inf_numeral & u, numeral & m) {
        if (is_base(x_j))
            return false;

        inf_numeral const & x_j_val = get_value(x_j);
        column & c = m_columns[x_j];
        typename svector<col_entry>::iterator it  = c.begin_entries();
        typename svector<col_entry>::iterator end = c.end_entries();

        inf_l = true;
        inf_u = true;
        l.reset(); 
        u.reset();
        m = numeral(1);
#define IS_FIXED() { if (!inf_l && !inf_u && l == u) goto fi_succeeded; }
#define SET_LOWER(VAL) { inf_numeral const & _VAL = VAL; if (inf_l || _VAL > l) { l = _VAL; inf_l = false; } IS_FIXED(); }
#define SET_UPPER(VAL) { inf_numeral const & _VAL = VAL; if (inf_u || _VAL < u) { u = _VAL; inf_u = false; } IS_FIXED(); }
        
        if (lower(x_j)) {
            SET_LOWER(lower_bound(x_j));
        }
        if (upper(x_j)) {
            SET_UPPER(upper_bound(x_j));
        }
       
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                row & r        = m_rows[it->m_row_id];
                theory_var x_i = r.get_base_var();
                if (x_i != null_theory_var && !is_quasi_base(x_i)) {
                    numeral const &        a_ij = r[it->m_row_idx].m_coeff;
                    inf_numeral const & x_i_val = get_value(x_i);
                    if (is_int(x_i) && is_int(x_j) && !a_ij.is_int())
                        m = lcm(m, denominator(a_ij));
                    bound * x_i_lower = lower(x_i);
                    bound * x_i_upper = upper(x_i);
                    if (a_ij.is_neg()) {
                        if (x_i_lower) {
                            inf_numeral new_l = x_j_val + ((x_i_val - x_i_lower->get_value()) / a_ij);
                            SET_LOWER(new_l);
                        }
                        if (x_i_upper) {
                            inf_numeral new_u = x_j_val + ((x_i_val - x_i_upper->get_value()) / a_ij);
                            SET_UPPER(new_u);
                        }
                    }
                    else {
                        if (x_i_upper) {
                            inf_numeral new_l = x_j_val + ((x_i_val - x_i_upper->get_value()) / a_ij);
                            SET_LOWER(new_l);
                        }
                        if (x_i_lower) {
                            inf_numeral new_u = x_j_val + ((x_i_val - x_i_lower->get_value()) / a_ij);
                            SET_UPPER(new_u);
                        }
                    }
                }
            }
        }
    fi_succeeded:
        TRACE("freedom_interval",
              tout << "freedom variable for:\n";
              display_var(tout, x_j);
              tout << "[";
              if (inf_l) tout << "-oo"; else tout << l;
              tout << "; ";
              if (inf_u) tout << "oo";  else tout << u;
              tout << "]\n";);
        return true;
    }

    // -----------------------------------
    //
    // Implied eqs
    //
    // -----------------------------------
    

    /**
       \brief Try to check whether v1 == v2 is implied by the current state.
       If it is return true.
    */
    template<typename Ext>
    bool theory_arith<Ext>::try_to_imply_eq(theory_var v1, theory_var v2) {
        SASSERT(v1 != v2);
        SASSERT(get_value(v1) == get_value(v2));
        SASSERT(valid_row_assignment());
        SASSERT(satisfy_bounds());
        if (is_quasi_base(v1) || is_quasi_base(v2))
            return false;
        m_tmp_row.reset();

        if (is_non_base(v1)) {
            add_tmp_row_entry<false>(m_tmp_row, numeral(1), v1);
        }
        else {
            row & r = m_rows[get_var_row(v1)];
            typename vector<row_entry>::const_iterator it  = r.begin_entries();
            typename vector<row_entry>::const_iterator end = r.end_entries();
            for (; it != end; ++it) {  
                if (!it->is_dead() && it->m_var != v1)                          
                    add_tmp_row_entry<true>(m_tmp_row, it->m_coeff, it->m_var);
            }            
        }

        m_tmp_row.save_var_pos(m_var_pos);

#define ADD_ENTRY(COEFF, VAR) {                                                         \
            int pos  = m_var_pos[VAR];                                                  \
            if (pos == -1) {                                                            \
                add_tmp_row_entry<false>(m_tmp_row, COEFF, VAR);                        \
            }                                                                           \
            else {                                                                      \
                row_entry & r_entry   = m_tmp_row[pos];                                 \
                SASSERT(r_entry.m_var == VAR);                                          \
                r_entry.m_coeff      += COEFF;                                          \
                if (r_entry.m_coeff.is_zero())                                          \
                    m_tmp_row.del_row_entry(pos);                                       \
                m_var_pos[VAR] = -1;                                                    \
            }                                                                           \
        }        

        if (is_non_base(v2)) {
            ADD_ENTRY(numeral(-1), v2);
        }
        else {
            row & r = m_rows[get_var_row(v2)];
            typename vector<row_entry>::const_iterator it  = r.begin_entries();
            typename vector<row_entry>::const_iterator end = r.end_entries();
            for (; it != end; ++it) {  
                if (!it->is_dead() && it->m_var != v2) {
                    numeral c = it->m_coeff;
                    c.neg();
                    ADD_ENTRY(c, it->m_var);
                }
            }
        }
        m_tmp_row.reset_var_pos(m_var_pos);
        
        SASSERT(m_tmp_row.size() > 0);

#if 0
        TRACE("imply_eq", display_row_info(tout, m_tmp_row););
        m_tmp_acc_lits.reset();
        m_tmp_acc_eqs.reset();
        m_tmp_lit_set.reset();
        m_tmp_eq_set.reset();
        
        if (max_min(m_tmp_row, true) && 
            is_zero_row(m_tmp_row, true, m_tmp_acc_lits, m_tmp_acc_eqs, m_tmp_lit_set, m_tmp_eq_set) &&
            max_min(m_tmp_row, false) &&
            is_zero_row(m_tmp_row, false, m_tmp_acc_lits, m_tmp_acc_eqs, m_tmp_lit_set, m_tmp_eq_set)) {
            // v1 == v2
            TRACE("imply_eq", tout << "found new implied equality:\n";
                  display_var(tout, v1); display_var(tout, v2););
            // TODO: assert implied equality
            // return true;
        }
#endif

        return false;
    }

    // -----------------------------------
    //
    // Assume eqs
    //
    // The revamped assume eqs try to perturbate the 
    // current assignment using pivoting operations.
    //
    // -----------------------------------

#define RANGE 10000

    /**
       \brief Performs a random update on v using its freedom interval.
       Return true if it was possible to change.
    */
    template<typename Ext>
    bool theory_arith<Ext>::random_update(theory_var v) {
        if (is_fixed(v) || !is_non_base(v))
            return false;
        bool inf_l, inf_u;
        inf_numeral l, u;
        numeral m;
        get_freedom_interval(v, inf_l, l, inf_u, u, m);
        if (inf_l && inf_u) {
            inf_numeral new_val = inf_numeral(m_random() % (RANGE + 1));
            set_value(v, new_val);
            return true;
        }
        if (is_int(v)) {
            if (!inf_l) {
                l = ceil(l);
                if (!m.is_one())
                    l = m*ceil(l/m);
            }
            if (!inf_u) {
                u = floor(u);
                if (!m.is_one())
                    u = m*floor(u/m);
            }
        }
        if (!inf_l && !inf_u && l >= u)
            return false;
        if (inf_u) {
            SASSERT(!inf_l);
            inf_numeral delta   = inf_numeral(m_random() % (RANGE + 1));
            inf_numeral new_val = l + m*delta;
            set_value(v, new_val);
            return true;
        }
        if (inf_l) {
            SASSERT(!inf_u);
            inf_numeral delta   = inf_numeral(m_random() % (RANGE + 1));
            inf_numeral new_val = u - m*delta;
            set_value(v, new_val);
            return true;
        }
        if (!is_int(v)) {
            SASSERT(!inf_l && !inf_u);
            numeral delta       = numeral(m_random() % (RANGE + 1));
            inf_numeral new_val = l + ((delta * (u - l)) / numeral(RANGE)); 
            set_value(v, new_val);
            return true;
        }
        else {
            unsigned range = RANGE;
            numeral r = (u.get_rational() - l.get_rational()) / m;
            if (r < numeral(RANGE))
                range = static_cast<unsigned>(r.get_uint64());
            inf_numeral new_val = l + m * (inf_numeral(m_random() % (range + 1)));
            set_value(v, new_val);
            return true;
        }
    }
    
    template<typename Ext>
    void theory_arith<Ext>::mutate_assignment() {
        remove_fixed_vars_from_base();
        int num_vars = get_num_vars();
        m_var_value_table.reset();
        m_tmp_var_set.reset();
        sbuffer<theory_var> candidates;
        for (theory_var v = 0; v < num_vars; v++) {
            enode * n1        = get_enode(v);
            if (!is_relevant_and_shared(n1))
                continue;
            theory_var other = m_var_value_table.insert_if_not_there(v);
            if (other == v)
                continue; // first node with the given value...
            enode * n2 = get_enode(other);
            if (n1->get_root() == n2->get_root())
                continue;
            if (!is_fixed(v)) {
                candidates.push_back(v);
            }
            else if (!is_fixed(other) && !m_tmp_var_set.contains(other)) {
                m_tmp_var_set.insert(other);
                candidates.push_back(other);
            }
        }
        if (candidates.empty())
            return;
        typename sbuffer<theory_var>::iterator it  = candidates.begin();
        typename sbuffer<theory_var>::iterator end = candidates.end();
        m_tmp_var_set.reset();
        m_tmp_var_set2.reset();
        for (; it != end; ++it) {
            theory_var v = *it;
            SASSERT(!is_fixed(v));
            if (is_base(v)) {
                row & r = m_rows[get_var_row(v)];
                typename vector<row_entry>::const_iterator it2  = r.begin_entries();
                typename vector<row_entry>::const_iterator end2 = r.end_entries();
                for (; it2 != end2; ++it2) {  
                    if (!it2->is_dead() && it2->m_var != v && !is_fixed(it2->m_var) && random_update(it2->m_var))
                        break;
                }
            }
            else {
                random_update(v);
            }
        }
        SASSERT(m_to_patch.empty());
    }

    /**
       \brief We must redefine this method, because theory of arithmetic contains
       underspecified operators such as division by 0.
       (/ a b) is essentially an uninterpreted function when b = 0.
       Thus, 'a' must be considered a shared var if it is the child of an underspecified operator.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_shared(theory_var v) const {
        enode * n      = get_enode(v);
        enode * r      = n->get_root();
        enode_vector::const_iterator it  = r->begin_parents();
        enode_vector::const_iterator end = r->end_parents();
        for (; it != end; ++it) {
            enode * parent = *it;
            app *   o = parent->get_owner();
            if (o->get_family_id() == get_id()) {
                switch (o->get_decl_kind()) {
                case OP_DIV:
                case OP_IDIV:
                case OP_REM:
                case OP_MOD:
                    return true;
                default:
                    break;
                }
            }
        }
        return false;
    }

    template<typename Ext>
    bool theory_arith<Ext>::assume_eqs_core() {
        // See comment in m_liberal_final_check declaration
        if (m_liberal_final_check)
            mutate_assignment();
        TRACE("assume_eq_int", display(tout););

        unsigned old_sz = m_assume_eq_candidates.size();
        TRACE("func_interp_bug", display(tout););
        m_var_value_table.reset();
        bool result   = false;
        int num       = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            enode * n        = get_enode(v);
            TRACE("func_interp_bug", tout << "#" << n->get_owner_id() << " -> " << m_value[v] << "\n";);
            if (!is_relevant_and_shared(n))
                continue;
            theory_var other = null_theory_var;
            other = m_var_value_table.insert_if_not_there(v);
            if (other == v)
                continue;
            enode * n2 = get_enode(other);
            if (n->get_root() == n2->get_root())
                continue;
            TRACE("func_interp_bug", tout << "adding to assume_eq queue #" << n->get_owner_id() << " #" << n2->get_owner_id() << "\n";);
            m_assume_eq_candidates.push_back(std::make_pair(other, v));
            result = true;
        }

        if (result)
            get_context().push_trail(restore_size_trail<context, std::pair<theory_var, theory_var>, false>(m_assume_eq_candidates, old_sz));
        return delayed_assume_eqs();
        // return this->assume_eqs(m_var_value_table);
    }

    template<typename Ext>
    bool theory_arith<Ext>::delayed_assume_eqs() {
        if (m_assume_eq_head == m_assume_eq_candidates.size())
            return false;

        get_context().push_trail(value_trail<context, unsigned>(m_assume_eq_head));
        while (m_assume_eq_head < m_assume_eq_candidates.size()) {
            std::pair<theory_var, theory_var> const & p = m_assume_eq_candidates[m_assume_eq_head];
            theory_var v1 = p.first;
            theory_var v2 = p.second;
            m_assume_eq_head++;
            CTRACE("func_interp_bug", 
                   get_value(v1) == get_value(v2) && 
                   get_enode(v1)->get_root() != get_enode(v2)->get_root(),
                   tout << "assuming eq: #" << get_enode(v1)->get_owner_id() << " = #" << get_enode(v2)->get_owner_id() << "\n";);
            if (get_value(v1) == get_value(v2) && 
                get_enode(v1)->get_root() != get_enode(v2)->get_root() &&
                assume_eq(get_enode(v1), get_enode(v2))) {
                return true;
            }
        }
        return false;
    }


#if 0
    /**
       \brief Check if the given row is implying a zero upper/lower bound.
       Accumulate the justification in the given vectors.
       Return true if it is.
    */
    template<typename Ext>
    bool theory_arith<Ext>::is_zero_row(row const & r, bool upper, literal_vector & lit_vect, eq_vector & eq_vect, literal_idx_set & lits, eq_set & eqs) {
        inf_numeral val;
        typename vector<row_entry>::const_iterator it  = r.begin_entries();  
        typename vector<row_entry>::const_iterator end = r.end_entries();                
        for (; it != end; ++it) {
            if (!it->is_dead()) { 
                theory_var v = it->m_var;
                bool use_upper = upper;
                if (!it->m_coeff.is_pos())
                    use_upper = !use_upper;
                bound * b  = get_bound(v, use_upper);
                inf_numeral tmp = b->get_value();
                tmp *= it->m_coeff;
                val += tmp;
                SASSERT(b);
                acc_umulate_justification(*b, lit_vect, eq_vect, lits, eqs);
            }
        }
        return val.is_zero();
    }
#endif

};

#endif /* _THEORY_ARITH_AUX_H_ */

