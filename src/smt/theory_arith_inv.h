/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_arith_inv.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-02.

Revision History:

--*/
#pragma once

#include "smt/theory_arith.h"
#include "ast/ast_pp.h"

namespace smt {

#ifdef Z3DEBUG
    template<typename Ext>
    bool theory_arith<Ext>::check_vector_sizes() const {
        SASSERT(m_columns.size() == m_data.size());
        SASSERT(m_value.size() == m_data.size());
        SASSERT(m_old_value.size() == m_data.size());
        SASSERT(m_unassigned_atoms.size() == m_data.size());
        SASSERT(m_var_pos.size() == m_data.size());
        SASSERT(m_bounds[0].size() == m_data.size());
        SASSERT(m_bounds[1].size() == m_data.size());
        return true;
    }

    /**
       \brief Check whether all entries of m_var_pos are -1
    */
    template<typename Ext>
    bool theory_arith<Ext>::check_null_var_pos() const {
        svector<int>::const_iterator it  = m_var_pos.begin();
        svector<int>::const_iterator end = m_var_pos.end();
        for (; it != end; ++it) {
            SASSERT(*it == -1);
        }
        return true;
    }

    /**
       \brief Return true if the given row has a variable different from r.m_base_var
       that has the given kind.
    */
    template<typename Ext>
    bool theory_arith<Ext>::has_var_kind(unsigned r_id, var_kind k) const {
        row const & r   = m_rows[r_id];
        theory_var base = r.m_base_var;
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead() && get_var_kind(it->m_var) == k && it->m_var != base)
                return true;
        }
        return false;
    }

    /**
       \brief Return true if the given row is well formed.
    */
    template<typename Ext>
    bool theory_arith<Ext>::wf_row(unsigned r_id) const {
        buffer<bool,false,1024> already_found;
        already_found.resize(get_num_vars(), false);
        row const & r = m_rows[r_id];
        if (r.m_base_var != null_theory_var) {
            int i = 0;
            theory_var s = r.m_base_var;
            SASSERT(is_base(s) || is_quasi_base(s));
            CTRACE("arith_bug", !(!is_base(s) || (!has_var_kind(r_id, BASE) && !has_var_kind(r_id, QUASI_BASE))),
                   display_row_info(tout, r_id););
            SASSERT(!is_base(s) || (!has_var_kind(r_id, BASE) && !has_var_kind(r_id, QUASI_BASE)));
            CTRACE("arith_bug", is_quasi_base(s) && has_var_kind(r_id, QUASI_BASE), display_row_info(tout, r_id););
            SASSERT(!is_quasi_base(s) || !has_var_kind(r_id, QUASI_BASE));
            SASSERT(r.is_coeff_of(s, numeral::one()));
            typename vector<row_entry>::const_iterator it  = r.begin_entries();
            typename vector<row_entry>::const_iterator end = r.end_entries();
            for (; it != end; ++it, ++i) {
                if (!it->is_dead()) {
                    CTRACE("row_bug", already_found[it->m_var], display_row_info(tout, r_id););
                    SASSERT(!already_found[it->m_var]);
                    already_found[it->m_var] = true;
                    column const & c = m_columns[it->m_var];
                    CTRACE("row_bug", it->m_coeff.is_zero(), display_row_info(tout, r_id););
                    SASSERT(!it->m_coeff.is_zero());
                    SASSERT(c[it->m_col_idx].m_row_id  == static_cast<int>(r_id));
                    SASSERT(c[it->m_col_idx].m_row_idx == i);
                }
            }
        }
        return true;
    }

    /**
       \brief Return true if all rows are well formed.
    */
    template<typename Ext>
    bool theory_arith<Ext>::wf_rows() const {
        unsigned num = m_rows.size();
        for (unsigned r_id = 0; r_id < num; r_id++) {
            SASSERT(wf_row(r_id));
            if (m_rows[r_id].m_base_var == null_theory_var) {
                SASSERT(std::find(m_dead_rows.begin(), m_dead_rows.end(), r_id) != m_dead_rows.end());
            }
        }
        return true;
    }

    /**
       \brief Return true if the column associated with v is well formed.
    */
    template<typename Ext>
    bool theory_arith<Ext>::wf_column(theory_var v) const { 
        column const & c = m_columns[v];
        int i = 0;
        typename svector<col_entry>::const_iterator it  = c.begin_entries();
        typename svector<col_entry>::const_iterator end = c.end_entries();
        for (; it != end; ++it, ++i) {
            if (!it->is_dead()) {
                row const & r = m_rows[it->m_row_id];
                CTRACE("wf_column", r.size() == 0, tout << "v" << v << ", it->m_row_id: " << it->m_row_id << "\n"; display_row_info(tout, r); display(tout););
                SASSERT(r.size() != 0);
                SASSERT(r[it->m_row_idx].m_var == v);
                SASSERT(r[it->m_row_idx].m_col_idx == i);
            }
        }
        SASSERT(!is_quasi_base(v) || c.size() == 1);
        return true;
    }

    /**
       \brief Return true if all columns are well formed.
     */
    template<typename Ext>
    bool theory_arith<Ext>::wf_columns() const {
        int num = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            SASSERT(wf_column(v));
        }
        return true;
    }

    /**
       \brief Return true if all rows evaluate to zero.
       
       \remark Quasi-base rows don't need to be checked.
    */
    template<typename Ext>
    bool theory_arith<Ext>::valid_row_assignment() const {
        TRACE("valid_row_assignment", display(tout););
        typename vector<row>::const_iterator it  = m_rows.begin();
        typename vector<row>::const_iterator end = m_rows.end();
        for (; it != end; ++it) {
            if (it->get_base_var() != null_theory_var) {
                SASSERT(valid_row_assignment(*it));
            }
        }
        return true;
    }

    template<typename Ext>
    bool theory_arith<Ext>::valid_row_assignment(row const & r) const {
        theory_var s = r.get_base_var();
        SASSERT(is_base(s) || is_quasi_base(s));
        if (s != null_theory_var && is_base(s)) {
            inf_numeral sum;
            typename vector<row_entry>::const_iterator it  = r.begin_entries();
            typename vector<row_entry>::const_iterator end = r.end_entries();
            for (; it != end; ++it) {
                if (!it->is_dead()) {
                    sum += it->m_coeff * m_value[it->m_var];
                }
            }
            CTRACE("valid_row_assignment_bug", !sum.is_zero(), tout << "checking: "; display_row_info(tout, r););
            SASSERT(sum.is_zero());
        }
        return true;
    }

    template<typename Ext>
    bool theory_arith<Ext>::satisfy_bounds() const {
        if (get_manager().limit().is_canceled())
            return true;
        int num = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            CTRACE("bound_bug", below_lower(v) || above_upper(v), display_var(tout, v); display(tout););
            SASSERT(!below_lower(v));
            SASSERT(!above_upper(v));
            if (below_lower(v) || above_upper(v)) return false;
        }
        return true;
    }

    template<typename Ext>
    bool theory_arith<Ext>::satisfy_integrality() const {
        int num = get_num_vars();
        for (theory_var v = 0; v < num; v++) {
            if (is_int(v) && !get_value(v).is_int()) {
                TRACE("bound_bug", display_var(tout, v); display(tout););
                return false;
            }
        }
        return true;
    }

    template<typename Ext>
    bool theory_arith<Ext>::valid_assignment() const {
        if (get_manager().limit().is_canceled())
            return true;
        if (valid_row_assignment() &&
            satisfy_bounds() &&
            satisfy_integrality()) {
            return true;
        }
        TRACE("arith", display(tout););
        return false;
    }

#endif

};


