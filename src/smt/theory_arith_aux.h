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
#ifndef THEORY_ARITH_AUX_H_
#define THEORY_ARITH_AUX_H_

#include"inf_eps_rational.h"
#include"theory_arith.h"
#include"smt_farkas_util.h"
#include"th_rewriter.h"
#include"filter_model_converter.h"

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
    void theory_arith<Ext>::antecedents::push_lit(literal l, numeral const& r, bool proofs_enabled) { 
        m_lits.push_back(l);
        if (proofs_enabled) {
            m_lit_coeffs.push_back(r); 
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::antecedents::push_eq(enode_pair const& p, numeral const& r, bool proofs_enabled) { 
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
    // Bounds
    //
    // -----------------------------------

    
    template<typename Ext>
    void theory_arith<Ext>::bound::display(theory_arith<Ext> const& th, std::ostream& out) const {
        out << "v" << get_var() << " " << get_bound_kind() << " " << get_value();
    }


    // -----------------------------------
    //
    // Atoms
    //
    // -----------------------------------

    template<typename Ext>
    theory_arith<Ext>::atom::atom(bool_var bv, theory_var v, inf_numeral const & k, atom_kind kind):
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

    template<typename Ext>
    void theory_arith<Ext>::atom::display(theory_arith<Ext> const& th, std::ostream& out) const {
        literal l(get_bool_var(), !m_is_true);
        out << "v" << bound::get_var() << " " << bound::get_bound_kind() << " " << get_k() << " ";
        out << l << ":";
        th.get_context().display_detailed_literal(out, l);
    }

    // -----------------------------------
    //
    // eq_bound
    //
    // -----------------------------------

    template<typename Ext>
    void theory_arith<Ext>::eq_bound::display(theory_arith<Ext> const& th, std::ostream& out) const {        
        ast_manager& m = th.get_manager();
        out << "#" << m_lhs->get_owner_id() << " " << mk_pp(m_lhs->get_owner(), m) << " = "
            << "#" << m_rhs->get_owner_id() << " " << mk_pp(m_rhs->get_owner(), m);
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
            if (!it->is_dead() && !it->m_coeff.is_int()) {
                TRACE("gomory_cut", display_row(tout, r, true););
                return false;
            }
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
    void theory_arith<Ext>::derived_bound::push_justification(antecedents& a, numeral const& coeff, bool proofs_enabled) {

        if (proofs_enabled) {
            for (unsigned i = 0; i < m_lits.size(); ++i) {
                a.push_lit(m_lits[i], coeff, proofs_enabled);
            }
            for (unsigned i = 0; i < m_eqs.size(); ++i) {
                a.push_eq(m_eqs[i], coeff, proofs_enabled);
            }
        }
        else {
            a.lits().append(m_lits.size(), m_lits.c_ptr());
            a.eqs().append(m_eqs.size(), m_eqs.c_ptr());
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::derived_bound::display(theory_arith<Ext> const& th, std::ostream& out) const {
      out << "v" << bound::get_var() << " " << bound::get_bound_kind() << " " << bound::get_value();
        
        ast_manager& m = th.get_manager();
        for (unsigned i = 0; i < m_eqs.size(); ++i) {
            enode* a = m_eqs[i].first;
            enode* b = m_eqs[i].second;
            out << " ";
            out << "#" << a->get_owner_id() << " " << mk_pp(a->get_owner(), m) << " = "
                << "#" << b->get_owner_id() << " " << mk_pp(b->get_owner(), m);
        }
        for (unsigned i = 0; i < m_lits.size(); ++i) {
            literal l = m_lits[i];
            out << " " << l << ":"; th.get_context().display_detailed_literal(out, l);            
        }
    }


    template<typename Ext>
    void theory_arith<Ext>::justified_derived_bound::push_justification(antecedents& a, numeral const& coeff, bool proofs_enabled) {
        for (unsigned i = 0; i < this->m_lits.size(); ++i) {
            a.push_lit(this->m_lits[i], coeff*m_lit_coeffs[i], proofs_enabled);
        }
        for (unsigned i = 0; i < this->m_eqs.size(); ++i) {
            a.push_eq(this->m_eqs[i], coeff*m_eq_coeffs[i], proofs_enabled);
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
        b.push_justification(ante, coeff, proofs_enabled());
        unsigned num_lits = ante.lits().size();
        for (unsigned i = 0; i < num_lits; ++i) {
            literal l = ante.lits()[i];
            if (lits.contains(l.index()))
                continue;
            if (proofs_enabled()) {
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
            if (proofs_enabled()) {
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
        derived_bound * new_bound = proofs_enabled()?alloc(justified_derived_bound, v, k_norm, kind):alloc(derived_bound, v, k_norm, kind);
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

    template<typename Ext>
    bool theory_arith<Ext>::is_safe_to_leave(theory_var x, bool inc, bool& has_int, bool& shared) {
        
        context& ctx = get_context();
        shared |= ctx.is_shared(get_enode(x));
        column & c      = m_columns[x];
        typename svector<col_entry>::iterator it  = c.begin_entries();
        typename svector<col_entry>::iterator end = c.end_entries();
        has_int = false;
        bool unbounded = (inc && !upper(x)) || (!inc && !lower(x));
        bool was_unsafe = false;
        for (; it != end; ++it) {
            if (it->is_dead()) continue;
            row const & r = m_rows[it->m_row_id];
            theory_var s  = r.get_base_var();
            numeral const & coeff = r[it->m_row_idx].m_coeff;    
            if (s != null_theory_var && is_int(s)) has_int = true;
            bool is_unsafe = (s != null_theory_var && is_int(s) && !coeff.is_int());                
            shared |= (s != null_theory_var && ctx.is_shared(get_enode(s)));
            was_unsafe |= is_unsafe;
            bool inc_s = coeff.is_neg() ? inc : !inc;
            unbounded &= !get_bound(s, inc_s);
            TRACE("opt", tout << "is v" << x << " safe to leave for v" << s 
                  << "? " << (is_unsafe?"no":"yes") << " " << (has_int?"int":"real") << " " << (unbounded?"unbounded":"bounded") << "\n";
                  display_row(tout, r, true););
            if (was_unsafe && !unbounded) return false;
        }

        return !was_unsafe || unbounded;
    }


    template<typename Ext>
    bool theory_arith<Ext>::get_theory_vars(expr * n, uint_set & vars) {
        rational r;
        expr* x, *y;
        if (m_util.is_numeral(n, r)) {
            return true;
        }
        else if (m_util.is_add(n)) {
            for (unsigned i = 0; i < to_app(n)->get_num_args(); ++i) {
                if (!get_theory_vars(to_app(n)->get_arg(i), vars)) {
                    return false;
                }
            }
        }
        else if (m_util.is_to_real(n, x) || m_util.is_to_int(n, x)) {
            return get_theory_vars(x, vars);
        }
        else if (m_util.is_mul(n, x, y) && m_util.is_numeral(x, r)) {
            return get_theory_vars(y, vars);
        }
        else if (m_util.is_mul(n, y, x) && m_util.is_numeral(x, r)) {
            return get_theory_vars(y, vars);
        }
        else if (!is_app(n)) {
            return false;
        }
        else if (to_app(n)->get_family_id() == m_util.get_family_id()) {
            return false;
        }
        else {
            context & ctx = get_context();
            SASSERT(ctx.e_internalized(n));
            enode * e    = ctx.get_enode(n);
            if (is_attached_to_var(e)) {
                vars.insert(e->get_th_var(get_id()));
            }
            return true;
        }
        return true;
    }

    //
    // add_objective(expr* term) internalizes the arithmetic term and creates
    // a row for it if it is not already internalized. 
    // Then return the variable corresponding to the term.
    //

    template<typename Ext>
    theory_var theory_arith<Ext>::add_objective(app* term) {
        theory_var v = internalize_term_core(term);
        TRACE("opt", tout << mk_pp(term, get_manager()) << " |-> v" << v << "\n";);
        SASSERT(!is_quasi_base(v));
        if (!is_linear(get_manager(), term)) {
            v = null_theory_var;
        }
        return v;
    }

    template<typename Ext>
    inf_eps_rational<inf_rational> theory_arith<Ext>::value(theory_var v) {
        return inf_eps_rational<inf_rational>(get_value(v));
    }

    template<typename Ext>
    inf_eps_rational<inf_rational> theory_arith<Ext>::maximize(theory_var v, expr_ref& blocker, bool& has_shared) {
        TRACE("bound_bug", display_var(tout, v); display(tout););
        has_shared = false;
        max_min_t r = max_min(v, true, true, has_shared); 
        if (r == UNBOUNDED) {
            has_shared = false;
            blocker = get_manager().mk_false();
            return inf_eps_rational<inf_rational>::infinity();
        }
        else {
            blocker = mk_gt(v);
            return inf_eps_rational<inf_rational>(get_value(v));
        }
        
    }

    /**
       \brief: Create an atom that enforces the inequality v > val
       The arithmetical expression encoding the inequality suffices 
       for the theory of aritmetic.
    */
    template<typename Ext>
    expr_ref theory_arith<Ext>::mk_gt(theory_var v) {
        ast_manager& m = get_manager();
        inf_numeral const& val = get_value(v);
        expr* obj = get_enode(v)->get_owner();
        expr_ref e(m);
        rational r = val.get_rational();
        if (m_util.is_int(m.get_sort(obj))) {
            if (r.is_int()) {
                r += rational::one();
            }
            else {
                r = ceil(r);
            }
            e = m_util.mk_numeral(r, m.get_sort(obj));
            e = m_util.mk_ge(obj, e);
        }
        else {
            // obj is over the reals.
            e = m_util.mk_numeral(r, m.get_sort(obj));
            
            if (val.get_infinitesimal().is_neg()) {
                e = m_util.mk_ge(obj, e);
            }
            else {
                e = m_util.mk_gt(obj, e);
            }
        }
        return e;
    }

    /**
      \brief create atom that enforces: val <= v
      The atom that enforces the inequality is created directly 
      as opposed to using arithmetical terms. 
      This allows to handle inequalities with non-standard numbers.
    */
    template<typename Ext>
    expr_ref theory_arith<Ext>::mk_ge(filter_model_converter& fm, theory_var v, inf_numeral const& val) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        std::ostringstream strm;
        strm << val << " <= " << mk_pp(get_enode(v)->get_owner(), get_manager());
        app* b = m.mk_const(symbol(strm.str().c_str()), m.mk_bool_sort());
        if (!ctx.b_internalized(b)) {
            fm.insert(b->get_decl());
            bool_var bv = ctx.mk_bool_var(b);
            ctx.set_var_theory(bv, get_id());
            // ctx.set_enode_flag(bv, true);
            atom* a = alloc(atom, bv, v, val, A_LOWER);
            mk_bound_axioms(a);
            m_unassigned_atoms[v]++;
            m_var_occs[v].push_back(a);
            m_atoms.push_back(a);
            insert_bv2a(bv, a);
            TRACE("arith", tout << mk_pp(b, m) << "\n";
                  display_atom(tout, a, false););            
        }
        return expr_ref(b, m);
    }


    /**
       \brief enable watching bound atom.       
     */
    template<typename Ext>
    void theory_arith<Ext>::enable_record_conflict(expr* bound) {
        m_params.m_arith_bound_prop = BP_NONE;
        SASSERT(propagation_mode() == BP_NONE); // bound propagtion rules are not (yet) handled.
        if (bound) {
            context& ctx = get_context();
            m_bound_watch = ctx.get_bool_var(bound);
        }
        else {
            m_bound_watch = null_bool_var;
        }        
        m_upper_bound = -inf_eps_rational<inf_rational>::infinity();
    }

    /**
       \brief 
          pos < 0
       == 
          r(Ax <= b) + q(v <= val) 
       == 
          val' <= q*v & q*v <= q*val
      
          q*v - val' >= 0

       => 
          (q*v - val' - q*v)/q >= -v
       ==
          val/q <= v
     */

    template<typename Ext>
    void theory_arith<Ext>::record_conflict(
        unsigned num_lits, literal const * lits, 
        unsigned num_eqs, enode_pair const * eqs,
        unsigned num_params, parameter* params) {
        ast_manager& m = get_manager();
        context& ctx = get_context();
        expr_ref tmp(m), vq(m);
        expr* x, *y, *e;
        if (null_bool_var == m_bound_watch) {
            return;
        }
        unsigned idx = num_lits;
        for (unsigned i = 0; i < num_lits; ++i) {
            if (m_bound_watch == lits[i].var()) {
                //SASSERT(!lits[i].sign());
                idx = i;
                break;
            }
        }
        if (idx == num_lits) {
            return;
        }
        for (unsigned i = 0; i < num_lits; ++i) {
            ctx.literal2expr(lits[i], tmp);
        }
        for (unsigned i = 0; i < num_eqs; ++i) {
            enode_pair const& p = eqs[i];
            x = p.first->get_owner();
            y = p.second->get_owner();
            tmp = m.mk_eq(x,y);
        }

        SASSERT(num_params == 1 + num_lits + num_eqs);
        SASSERT(params[0].is_symbol());
        SASSERT(params[0].get_symbol() == symbol("farkas")); // for now, just handle this rule.
        farkas_util farkas(m);
        rational q;
        for (unsigned i = 0; i < num_lits; ++i) {
            parameter const& pa = params[i+1];
            SASSERT(pa.is_rational());
            if (idx == i) {
                q = abs(pa.get_rational());
                continue;
            }
            ctx.literal2expr(lits[i], tmp);
            farkas.add(abs(pa.get_rational()), to_app(tmp));
        }
        for (unsigned i = 0; i < num_eqs; ++i) {
            enode_pair const& p = eqs[i];
            x = p.first->get_owner();
            y = p.second->get_owner();
            tmp = m.mk_eq(x,y);
            parameter const& pa = params[1 + num_lits + i];
            SASSERT(pa.is_rational());
            farkas.add(abs(pa.get_rational()), to_app(tmp));
        }
        tmp = farkas.get();
        // IF_VERBOSE(1, verbose_stream() << "Farkas result: " << tmp << "\n";);
        atom* a = get_bv2a(m_bound_watch);
        SASSERT(a);
        expr_ref_vector  terms(m);
        vector<rational> mults;
        bool strict = false;
        if (m_util.is_le(tmp, x, y) || m_util.is_ge(tmp, y, x)) {
        }
        else if (m.is_not(tmp, e) && (m_util.is_le(e, y, x) || m_util.is_ge(e, x, y))) {
            strict = true;
        }
        else if (m.is_eq(tmp, x, y)) {            
        }
        else {
            UNREACHABLE();
        }
        e = var2expr(a->get_var());
        q *= farkas.get_normalize_factor();
        SASSERT(!m_util.is_int(e) || q.is_int());  // TBD: not fully handled.
        if (q.is_one()) {
            vq = e;
        }
        else {
            vq = m_util.mk_mul(m_util.mk_numeral(q, q.is_int()), e);
        }
        vq = m_util.mk_add(m_util.mk_sub(x, y), vq);
        if (!q.is_one()) {
            vq = m_util.mk_div(vq, m_util.mk_numeral(q, q.is_int()));
        }
        th_rewriter rw(m);
        rw(vq, tmp);
        VERIFY(m_util.is_numeral(tmp, q));
        if (m_upper_bound < q) {
            m_upper_bound = q;
            if (strict) {
                m_upper_bound -= get_epsilon(a->get_var());
            }
            IF_VERBOSE(1, verbose_stream() << "new upper bound: " << m_upper_bound << "\n";);
        }
    }

    /**
       \brief find the minimal upper bound on the variable that was last enabled
              for conflict recording.
     */
    template<typename Ext>
    inf_eps_rational<inf_rational> theory_arith<Ext>::conflict_minimize() {
        return m_upper_bound;
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

       Get the equations for x_j:

       x_i1 = coeff_1 * x_j + rest_1
       ...
       x_in = coeff_n * x_j + rest_n

       gain_k := (upper_bound(x_ik) - value(x_ik))/coeff_k

    */

    
    template<typename Ext>
    bool theory_arith<Ext>::pick_var_to_leave(
        theory_var x_j,        // non-base variable to increment/decrement 
        bool       inc, 
        numeral &  a_ij,       // coefficient of x_i
        inf_numeral& min_gain, // minimal required gain on x_j (integral value on integers)
        inf_numeral& max_gain, // maximal possible gain on x_j
        bool& has_shared,      // determine if pivot involves shared variable
        theory_var& x_i) {     // base variable to pivot with x_j

        context& ctx = get_context();
        x_i = null_theory_var;
        init_gains(x_j, inc, min_gain, max_gain);
        has_shared |= ctx.is_shared(get_enode(x_j));
        if (is_int(x_j) && !get_value(x_j).is_int()) {
            return false;
        }        
        column & c   = m_columns[x_j];
        typename svector<col_entry>::iterator it  = c.begin_entries();
        typename svector<col_entry>::iterator end = c.end_entries();
        bool empty_column = true;
        for (; it != end; ++it) {
            if (it->is_dead()) continue;
            empty_column = false;
            row const & r = m_rows[it->m_row_id];
            theory_var s  = r.get_base_var();
            numeral const & coeff_ij = r[it->m_row_idx].m_coeff;
            if (update_gains(inc, s, coeff_ij, min_gain, max_gain) ||
                (x_i == null_theory_var && !unbounded_gain(max_gain))) {
                x_i = s;
                a_ij = coeff_ij;
            }
            has_shared |= ctx.is_shared(get_enode(s));
        }
        TRACE("opt", 
              tout << (safe_gain(min_gain, max_gain)?"safe":"unsafe") << "\n";
              tout << "min gain: " << min_gain;
              tout << " max gain: " << max_gain << "\n";
              tout << "v" << x_i << " ";
              tout << (has_shared?"shared":"not shared") << "\n";);

        SASSERT(!safe_gain(min_gain, max_gain) ||
                empty_column ||
                (unbounded_gain(max_gain) == (x_i == null_theory_var)));
        
        return !empty_column && safe_gain(min_gain, max_gain);
    }

    template<typename Ext>
    bool theory_arith<Ext>::unbounded_gain(inf_numeral const & max_gain) const {
        return max_gain.is_minus_one();
    }

    /*
      A gain is 'safe' with respect to the tableau if:
      - the selected variable is unbounded and every base variable where it occurs is unbounded
        in the direction of the gain. max_gain == -1 is used to indicate unbounded variables.
      - the selected variable is a rational (min_gain == -1, max_gain >= 0).
      - 
     */
    template<typename Ext>
    bool theory_arith<Ext>::safe_gain(inf_numeral const& min_gain, inf_numeral const & max_gain) const {
        return 
            unbounded_gain(max_gain) || 
            min_gain <= max_gain;        
    }

    /**
       \brief ensure that maximal gain is divisible by divisor.
    */
    template<typename Ext>
    void theory_arith<Ext>::normalize_gain(numeral const& divisor, inf_numeral & max_gain) const {
        SASSERT(divisor.is_int());
        if (!divisor.is_minus_one() && !max_gain.is_minus_one()) {
            max_gain = floor(max_gain/divisor)*divisor;
        }
    }

    /**
       \brief initialize gains for x_j based on the bounds for x_j.       
     */
    template<typename Ext>
    void theory_arith<Ext>::init_gains(
        theory_var     x,            // non-base variable to increment/decrement 
        bool           inc, 
        inf_numeral&   min_gain,     // min value to increment, -1 if rational
        inf_numeral&   max_gain) {   // max value to decrement, -1 if unbounded
        min_gain = -inf_numeral::one();
        max_gain = -inf_numeral::one();
        if (inc && upper(x)) {
            max_gain = upper_bound(x) - get_value(x);
        }
        else if (!inc && lower(x)) {
            max_gain = get_value(x) - lower_bound(x);
        }        
        if (is_int(x)) {
            min_gain = inf_numeral::one();
        }
        TRACE("opt",
              tout << "v" << x << " := " << get_value(x) << " "
              << "min gain: " << min_gain << " " 
              << "max gain: " << max_gain << "\n";);           
                

        SASSERT(max_gain.is_minus_one() || !max_gain.is_neg());
        SASSERT(min_gain.is_minus_one() || min_gain.is_one());
        SASSERT(is_int(x) == min_gain.is_one());

    }

    template<typename Ext>
    bool theory_arith<Ext>::update_gains(
        bool       inc,              // increment/decrement x_j
        theory_var x_i,              // potential base variable to pivot
        numeral const& a_ij,         // coefficient of x_j in row where x_i is base.
        inf_numeral&   min_gain,     // min value to increment, -1 if rational
        inf_numeral&   max_gain) {   // max value to decrement, -1 if unbounded

        // x_i = row + a_ij*x_j
        // a_ij > 0, inc -> decrement x_i
        // a_ij < 0, !inc -> decrement x_i
        // a_ij denominator

        SASSERT(!a_ij.is_zero());

        if (!safe_gain(min_gain, max_gain)) return false;

        inf_numeral max_inc = inf_numeral::minus_one();
        bool decrement_x_i = (inc && a_ij.is_pos()) || (!inc && a_ij.is_neg());
        if (decrement_x_i && lower(x_i)) {
            max_inc = abs((get_value(x_i) - lower_bound(x_i))/a_ij);
        }
        else if (!decrement_x_i && upper(x_i)) {
            max_inc = abs((upper_bound(x_i) - get_value(x_i))/a_ij);
        }
        numeral den_aij(1);
        bool is_tighter = false;
        if (is_int(x_i)) den_aij = denominator(a_ij);
        SASSERT(den_aij.is_pos() && den_aij.is_int());

        if (is_int(x_i) && !den_aij.is_one()) {
            if (min_gain.is_neg()) {
                min_gain = inf_numeral(den_aij);
            }
            else {
                min_gain = inf_numeral(lcm(min_gain.get_rational(), den_aij));
            }
            normalize_gain(min_gain.get_rational(), max_gain);
        }

        if (!max_inc.is_minus_one()) {
            if (is_int(x_i)) {
                TRACE("opt",
                      tout << "v" << x_i << " a_ij " << a_ij << " "
                      << "min gain: " << min_gain << " " 
                      << "max gain: " << max_gain << "\n";);

                max_inc = floor(max_inc);
                normalize_gain(min_gain.get_rational(), max_inc);
            }
            if (unbounded_gain(max_gain)) {
                max_gain = max_inc;
                is_tighter = true;
            }
            else if (max_gain > max_inc) {
                max_gain = max_inc;
                is_tighter = true;
            }
        }
        TRACE("opt",
              tout << "v" << x_i << " a_ij " << a_ij << " "
              << "min gain: " << min_gain << " " 
              << "max gain: " << max_gain << " tighter: "
              << (is_tighter?"true":"false") << "\n";);

        SASSERT(max_gain.is_minus_one() || !max_gain.is_neg());
        SASSERT(min_gain.is_minus_one() || !min_gain.is_neg());
        //SASSERT(!is_int(x_i) || min_gain.is_pos());
        //SASSERT(!is_int(x_i) || min_gain.is_int());
        //SASSERT(!is_int(x_i) || max_gain.is_int());
        return is_tighter;
    }

    /**
       \brief Check if bound change affects interface equality.
    */
    template<typename Ext>
    bool theory_arith<Ext>::has_interface_equality(theory_var x) {
        theory_var num = get_num_vars();
        context& ctx = get_context();
        enode* r = get_enode(x)->get_root();
        for (theory_var v = 0; v < num; v++) {
            if (v == x) continue;
            enode* n = get_enode(v);
            if (ctx.is_shared(n) && n->get_root() == r) {
                return true;
            }
        }
        return false;
    }
    

    /**
       \brief Maximize (Minimize) the given temporary row.
       Return true if succeeded.
    */
    template<typename Ext>
    typename theory_arith<Ext>::max_min_t theory_arith<Ext>::max_min(
        row & r, 
        bool max, 
        bool maintain_integrality, 
        bool& has_shared) {
        m_stats.m_max_min++;
        unsigned best_efforts = 0;
        bool inc = false;
        context& ctx = get_context();

        SASSERT(!maintain_integrality || valid_assignment());
        SASSERT(satisfy_bounds());

        numeral a_ij, curr_a_ij, coeff, curr_coeff;
        inf_numeral min_gain, max_gain, curr_min_gain, curr_max_gain;
        unsigned round = 0;
        max_min_t result = OPTIMIZED;
        has_shared = false;
        unsigned max_efforts = 10 + (ctx.get_random_value() % 20);
        while (best_efforts < max_efforts && !ctx.get_cancel_flag()) {
            theory_var x_j = null_theory_var;
            theory_var x_i = null_theory_var;
            max_gain.reset();
            min_gain.reset();
            ++round;

            TRACE("opt", tout << "round: " << round << ", max: " << max << "\n"; display_row(tout, r, true); tout << "state:\n"; display(tout););
            typename vector<row_entry>::const_iterator it  = r.begin_entries();
            typename vector<row_entry>::const_iterator end = r.end_entries();
            for (; it != end; ++it) {  
                if (it->is_dead()) continue;                                                  
                theory_var curr_x_j = it->m_var;
                theory_var curr_x_i = null_theory_var;
                SASSERT(is_non_base(curr_x_j));
                curr_coeff    = it->m_coeff;
                bool curr_inc = curr_coeff.is_pos() ? max : !max;                 
                if ((curr_inc && at_upper(curr_x_j)) || (!curr_inc && at_lower(curr_x_j))) {
                    // variable cannot be used for max/min.
                    continue; 
                }
                bool picked_var = pick_var_to_leave(curr_x_j, curr_inc, curr_a_ij, 
                                                    curr_min_gain, curr_max_gain, 
                                                    has_shared, curr_x_i);


                SASSERT(!picked_var || safe_gain(curr_min_gain, curr_max_gain));
                
                if (!picked_var) { //  && (r.size() > 1 || !safe_gain(curr_min_gain, curr_max_gain))
                    TRACE("opt", tout << "no variable picked\n";);
                    best_efforts++;
                }
                else if (curr_x_i == null_theory_var) {
                    TRACE("opt", tout << "v" << curr_x_j << " is unrestricted by other variables\n";);
                    // we can increase/decrease curr_x_j as much as we want.
                    x_i   = null_theory_var; // unbounded
                    x_j   = curr_x_j;
                    inc   = curr_inc;
                    min_gain = curr_min_gain;
                    max_gain = curr_max_gain;
                    break;
                }
                else if (curr_max_gain > max_gain) {
                    x_i   = curr_x_i;
                    x_j   = curr_x_j;
                    a_ij  = curr_a_ij;
                    coeff = curr_coeff;
                    max_gain = curr_max_gain;
                    min_gain = curr_min_gain;
                    inc   = curr_inc;
                }
                else if (curr_max_gain.is_zero() && (x_i == null_theory_var || curr_x_i < x_i)) {
                    x_i   = curr_x_i;
                    x_j   = curr_x_j;
                    a_ij  = curr_a_ij;
                    coeff = curr_coeff;
                    max_gain = curr_max_gain;
                    min_gain = curr_min_gain;
                    inc   = curr_inc;
                    // continue
                }
            }

            TRACE("opt", tout << "after traversing row:\nx_i: v" << x_i << ", x_j: v" << x_j << ", gain: " << max_gain << "\n";
                  tout << "best efforts: " << best_efforts << " has shared: " << has_shared << "\n";);
            
            if (x_j == null_theory_var && x_i == null_theory_var) {
                has_shared = false;
                best_efforts = 0;
                result = UNBOUNDED;
                break;
            }

            if (x_j == null_theory_var) {
                TRACE("opt", tout << "row is " << (max ? "maximized" : "minimized") << "\n";
                      display_row(tout, r, true););
                SASSERT(!maintain_integrality || valid_assignment());
                SASSERT(satisfy_bounds());
                result = OPTIMIZED;
                break; 
            }
            
            if (min_gain.is_pos() && !min_gain.is_one()) {
                ++best_efforts;
            }
            if (x_i == null_theory_var) {
                // can increase/decrease x_j as much as we want.
                
                if (inc && upper(x_j)) {
                    if (max_gain.is_zero()) return BEST_EFFORT;
                    SASSERT(!unbounded_gain(max_gain));
                    update_value(x_j, max_gain);
                    TRACE("opt", tout << "moved v" << x_j << " to upper bound\n";);
                    SASSERT(!maintain_integrality || valid_assignment());
                    SASSERT(satisfy_bounds());
                    continue;
                }
                if (!inc && lower(x_j)) {
                    if (max_gain.is_zero()) return BEST_EFFORT;
                    SASSERT(!unbounded_gain(max_gain));
                    SASSERT(max_gain.is_pos());
                    max_gain.neg();
                    update_value(x_j, max_gain);
                    TRACE("opt", tout << "moved v" << x_j << " to lower bound\n";);
                    SASSERT(!maintain_integrality || valid_assignment());
                    SASSERT(satisfy_bounds());
                    continue;
                }
#if 0
                if (ctx.is_shared(get_enode(x_j)) && has_interface_equality(x_j)) {
                    ++best_efforts;
                }
                else {
                    SASSERT(unbounded_gain(max_gain));
                    has_shared = false;
                    best_efforts = 0;
                }
#endif
                //
                // NB. As it stands this is a possibly unsound conclusion for shared theories.
                // the tradeoff is non-termination for unbounded objectives in the
                // presence of sharing.
                // 
                has_shared = false;
                best_efforts = 0;
                result = UNBOUNDED;
                break;
            }
            
            if (!is_fixed(x_j) && is_bounded(x_j) && 
                (upper_bound(x_j) - lower_bound(x_j) == max_gain)) {
                // can increase/decrease x_j up to upper/lower bound.
                if (inc) {
                    TRACE("opt", tout << "moved v" << x_j << " to upper bound\n";);
                }
                else {
                    max_gain.neg();
                    TRACE("opt", tout << "moved v" << x_j << " to lower bound\n";);
                }
                update_value(x_j, max_gain);
                SASSERT(!maintain_integrality || valid_assignment());
                SASSERT(satisfy_bounds());
                continue;
            }
            
            TRACE("opt", tout << "max: " << max << ", x_i: v" << x_i << ", x_j: v" << x_j << ", a_ij: " << a_ij << ", coeff: " << coeff << "\n";
                  if (upper(x_i)) tout << "upper x_i: " << upper_bound(x_i) << " ";
                  if (lower(x_i)) tout << "lower x_i: " << lower_bound(x_i) << " ";
                  tout << "value x_i: " << get_value(x_i) << "\n";
                  if (upper(x_j)) tout << "upper x_j: " << upper_bound(x_j) << " ";
                  if (lower(x_j)) tout << "lower x_j: " << lower_bound(x_j) << " ";
                  tout << "value x_j: " << get_value(x_j) << "\n";
                  );
            pivot<true>(x_i, x_j, a_ij, false);
                        
            SASSERT(is_non_base(x_i));
            SASSERT(is_base(x_j));
            
            bool inc_xi = inc?a_ij.is_neg():a_ij.is_pos();
            if (!move_to_bound(x_i, inc_xi, best_efforts, has_shared)) {
                TRACE("opt", tout << "can't move bound fully\n";);
                // break;                // break;

            }
            
            row & r2 = m_rows[get_var_row(x_j)];
            coeff.neg();
            add_tmp_row(r, coeff, r2);
            SASSERT(r.get_idx_of(x_j) == -1);
            SASSERT(!maintain_integrality || valid_assignment());
            SASSERT(satisfy_bounds());
        }
        TRACE("opt", display(tout););
        return (best_efforts>0 || ctx.get_cancel_flag())?BEST_EFFORT:result;
    }

    /**
       Move the variable x_i maximally towards its bound as long as 
       bounds of other variables are not violated.
       Returns false if an integer bound was truncated and no
       progress was made.
    */

    template<typename Ext>
    bool theory_arith<Ext>::move_to_bound(
        theory_var x_i,         // variable to move
        bool inc,               // increment variable or decrement
        unsigned& best_efforts, // is bound move a best effort?
        bool& has_shared) {     // does move include shared variables?
        inf_numeral min_gain, max_gain;
        if (is_int(x_i) && !get_value(x_i).is_int()) {
            ++best_efforts;
            return false;
        }
        init_gains(x_i, inc, min_gain, max_gain);        
        column & c   = m_columns[x_i];
        typename svector<col_entry>::iterator it  = c.begin_entries();
        typename svector<col_entry>::iterator end = c.end_entries();
        for (; it != end; ++it) {
            if (it->is_dead()) continue;
            row const & r = m_rows[it->m_row_id];
            theory_var s  = r.get_base_var();
            numeral const & coeff = r[it->m_row_idx].m_coeff;
            update_gains(inc, s, coeff, min_gain, max_gain);
            has_shared |= get_context().is_shared(get_enode(s));
        }
        bool result = false;
        if (safe_gain(min_gain, max_gain)) {
            TRACE("opt", tout << "Safe delta: " << max_gain << "\n";);
            SASSERT(!unbounded_gain(max_gain));
            if (!inc) {
                max_gain.neg();
            }
            update_value(x_i, max_gain);
            if (!min_gain.is_pos() || min_gain.is_one()) {
                ++best_efforts;
            }
            result = !max_gain.is_zero();
        }
        if (!result) {
            ++best_efforts;
        }
        return result;
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
   typename theory_arith<Ext>::max_min_t theory_arith<Ext>::max_min(theory_var v, bool max, bool maintain_integrality, bool& has_shared) {
        expr* e = get_enode(v)->get_owner();

        SASSERT(!maintain_integrality || valid_assignment());
        SASSERT(satisfy_bounds());
        SASSERT(!is_quasi_base(v));
        if ((max && at_upper(v)) || (!max && at_lower(v))) {
            TRACE("opt", display_var(tout << "At " << (max?"max: ":"min: ") << mk_pp(e, get_manager()) << " \n", v););
            return AT_BOUND; // nothing to be done...
        }
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
        max_min_t r = max_min(m_tmp_row, max, maintain_integrality, has_shared);
        if (r == OPTIMIZED) {
            TRACE("opt", tout << mk_pp(e, get_manager()) << " " << (max ? "max" : "min") << " value is: " << get_value(v) << "\n";
                  display_row(tout, m_tmp_row, true); display_row_info(tout, m_tmp_row););
            
            mk_bound_from_row(v, get_value(v), max ? B_UPPER : B_LOWER, m_tmp_row);            
        }
        else if (r == UNBOUNDED) {
            TRACE("opt", display_var(tout << "unbounded: " << mk_pp(e, get_manager()) << "\n", v););
        }
        else {
            TRACE("opt", display_var(tout << "not optimized: " << mk_pp(e, get_manager()) << "\n", v););
        }
        return r;
    }

    /**
       \brief Maximize & Minimize variables in vars.
       Return false if an inconsistency was detected.
    */
    template<typename Ext>
    bool theory_arith<Ext>::max_min(svector<theory_var> const & vars) { 
        bool succ = false;
        bool has_shared = false;
        svector<theory_var>::const_iterator it  = vars.begin();
        svector<theory_var>::const_iterator end = vars.end();
        for (; it != end; ++it) {
            if (max_min(*it, true, false, has_shared) == OPTIMIZED && !has_shared)
                succ = true;
            if (max_min(*it, false, false, has_shared) == OPTIMIZED && !has_shared)
                succ = true;
        }
        if (succ) {
            // process new bounds
            bool r = propagate_core();
            TRACE("opt", tout << "after max/min round:\n"; display(tout););
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
        SASSERT(valid_assignment());
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
        
        if ((OPTIMIZED == max_min(m_tmp_row, true)) && 
            is_zero_row(m_tmp_row, true, m_tmp_acc_lits, m_tmp_acc_eqs, m_tmp_lit_set, m_tmp_eq_set) &&
            (OPTIMIZED == max_min(m_tmp_row, false)) &&
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

#endif /* THEORY_ARITH_AUX_H_ */

