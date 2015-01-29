/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_arith_pp.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-05.

Revision History:

--*/
#ifndef _THEORY_ARITH_PP_H_
#define _THEORY_ARITH_PP_H_

#include"theory_arith.h"
#include"ast_smt_pp.h"
#include"stats.h"

namespace smt {
    template<typename Ext>
    void theory_arith<Ext>::collect_statistics(::statistics & st) const {
        st.update("arith conflicts", m_stats.m_conflicts);
        st.update("add rows", m_stats.m_add_rows);
        st.update("pivots", m_stats.m_pivots);
        st.update("assert lower", m_stats.m_assert_lower);
        st.update("assert upper", m_stats.m_assert_upper);
        st.update("assert diseq", m_stats.m_assert_diseq);
        st.update("bound prop", m_stats.m_bound_props);
        st.update("fixed eqs", m_stats.m_fixed_eqs);
        st.update("offset eqs", m_stats.m_offset_eqs);
        st.update("gcd tests", m_stats.m_gcd_tests);
        st.update("ineq splits", m_stats.m_branches);
        st.update("gomory cuts", m_stats.m_gomory_cuts);
        st.update("max-min", m_stats.m_max_min);
        st.update("grobner", m_stats.m_gb_compute_basis);
        st.update("pseudo nonlinear", m_stats.m_nl_linear);
        st.update("nonlinear bounds", m_stats.m_nl_bounds);
        st.update("nonlinear horner", m_stats.m_nl_cross_nested);
        m_arith_eq_adapter.collect_statistics(st);
    }

    template<typename Ext>
    void theory_arith<Ext>::display(std::ostream & out) const {
        out << "Theory arithmetic:\n";
        display_vars(out);
        display_nl_monomials(out);
        display_rows(out, true);
        display_rows(out, false);
        display_atoms(out);
        display_asserted_atoms(out);
    }

    template<typename Ext>
    void theory_arith<Ext>::display_nl_monomials(std::ostream & out) const {
        if (m_nl_monomials.empty())
            return;
        out << "non linear monomials:\n";
        svector<theory_var>::const_iterator it  = m_nl_monomials.begin();
        svector<theory_var>::const_iterator end = m_nl_monomials.end();
        for (; it != end; ++it)
            display_var(out, *it);
    }

    template<typename Ext>
    void theory_arith<Ext>::display_row(std::ostream & out, unsigned r_id, bool compact) const {
        out << r_id << " ";
        display_row(out, m_rows[r_id], compact);
    }

    template<typename Ext>
    void theory_arith<Ext>::display_row(std::ostream & out, row const & r, bool compact) const {
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        out << "(v" << r.get_base_var() << ") : ";
        bool first = true;
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                if (first)
                    first = false;
                else
                    out << " + ";
                theory_var s      = it->m_var;
                numeral const & c = it->m_coeff;
                if (!c.is_one())
                    out << c << "*";
                if (compact) {
                    out << "v" << s;
                    if (is_fixed(s)) {
                        out << ":" << lower(s)->get_value();
                    }
                }
                else
                    display_var_flat_def(out, s);
            }
        }
        out << "\n";
    }


    template<typename Ext>
    void theory_arith<Ext>::display_rows(std::ostream & out, bool compact) const {
        if (compact)
            out << "rows (compact view):\n";
        else
            out << "rows (expanded view):\n";
        unsigned num = m_rows.size();
        for (unsigned r_id = 0; r_id < num; r_id++) {
            if (m_rows[r_id].m_base_var != null_theory_var) {
                display_row(out, r_id, compact);
            }
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::display_row_shape(std::ostream & out, row const & r) const {
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                numeral const & c = it->m_coeff;
                if (c.is_one())
                    out << "1";
                else if (c.is_minus_one())
                    out << "-";
                else if (c.is_int() && c.to_rational().is_small())
                    out << "i";
                else if (c.is_int() && !c.to_rational().is_small())
                    out << "I";
                else if (c.to_rational().is_small())
                    out << "r";
                else
                    out << "R";
            }
        }
        out << "\n";
    }

    template<typename Ext>
    bool theory_arith<Ext>::is_one_minus_one_row(row const & r) const {
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                numeral const & c = it->m_coeff;
                if (!c.is_one() && !c.is_minus_one())
                    return false;
            }
        }
        return true;
    }

    template<typename Ext>
    void theory_arith<Ext>::display_rows_shape(std::ostream & out) const {
        unsigned num = m_rows.size();
        unsigned num_trivial = 0;
        for (unsigned r_id = 0; r_id < num; r_id++) {
            row const & r = m_rows[r_id];
            if (r.m_base_var != null_theory_var) {
                if (is_one_minus_one_row(r)) 
                    num_trivial++;
                else
                    display_row_shape(out, r);
            }
        }
        out << "num. trivial: " << num_trivial << "\n";
    }

    template<typename Ext>
    void theory_arith<Ext>::display_rows_bignums(std::ostream & out) const {
        unsigned num = m_rows.size();
        for (unsigned r_id = 0; r_id < num; r_id++) {
            row const & r = m_rows[r_id];
            if (r.m_base_var != null_theory_var) {
                typename vector<row_entry>::const_iterator it  = r.begin_entries();
                typename vector<row_entry>::const_iterator end = r.end_entries();
                for (; it != end; ++it) {
                    if (!it->is_dead()) {
                        numeral const & c = it->m_coeff;
                        if (c.to_rational().is_big()) {
                            std::string str = c.to_rational().to_string();
                            if (str.length() > 48) 
                                out << str << "\n";
                        }
                    }
                }
            }
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::display_rows_stats(std::ostream & out) const {
        unsigned num_vars = get_num_vars();
        unsigned num_rows = 0;
        unsigned num_non_zeros  = 0;
        unsigned num_ones       = 0;
        unsigned num_minus_ones = 0;
        unsigned num_small_ints = 0;
        unsigned num_big_ints   = 0;
        unsigned num_small_rats = 0;
        unsigned num_big_rats   = 0;
        for (unsigned r_id = 0; r_id < m_rows.size(); r_id++) {
            row const & r = m_rows[r_id];
            if (r.m_base_var != null_theory_var) {
                num_rows++;
                typename vector<row_entry>::const_iterator it  = r.begin_entries();
                typename vector<row_entry>::const_iterator end = r.end_entries();
                for (; it != end; ++it) {
                    if (!it->is_dead()) {
                        numeral const & c = it->m_coeff;
                        num_non_zeros++;
                        if (c.is_one())
                            num_ones++;
                        else if (c.is_minus_one())
                            num_minus_ones++;
                        else if (c.is_int() && c.to_rational().is_small())
                            num_small_ints++;
                        else if (c.is_int() && !c.to_rational().is_small())
                            num_big_ints++;
                        else if (c.to_rational().is_small())
                            num_small_rats++;
                        else
                            num_big_rats++;
                    }
                }
            }
        }
        out << "A:        " << num_rows << " X " << num_vars << "\n";
        out << "avg. row: " << num_non_zeros / num_rows << ", num. non zeros: " << num_non_zeros << "\n";
        unsigned spc = 6;
        out.width(spc);
        out << 1 << "|";
        out.width(spc);
        out << -1 << "|";
        out.width(spc);
        out << "i";
        out << "|";
        out.width(spc);
        out << "I";
        out << "|";
        out.width(spc);
        out << "r";
        out << "|";
        out.width(spc);
        out << "R";
        out << "\n";

        out.width(spc);
        out << num_ones << "|";
        out.width(spc);
        out << num_minus_ones << "|";
        out.width(spc);
        out << num_small_ints;
        out << "|";
        out.width(spc);
        out << num_big_ints;
        out << "|";
        out.width(spc);
        out << num_small_rats;
        out << "|";
        out.width(spc);
        out << num_big_rats;
        out << "\n";
    }

    template<typename Ext>
    void theory_arith<Ext>::display_row_info(std::ostream & out, unsigned r_id) const {
        out << r_id << " ";
        display_row_info(out, m_rows[r_id]);
    }

    template<typename Ext>
    void theory_arith<Ext>::display_row_info(std::ostream & out, row const & r) const {
        display_row(out, r, true);
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        for (; it != end; ++it) 
            if (!it->is_dead())
                display_var(out, it->m_var);
    }

    /**
       \brief Display row after substituting fixed variables.
    */
    template<typename Ext>
    void theory_arith<Ext>::display_simplified_row(std::ostream & out, row const & r) const {
        bool has_rat_coeff = false;
        numeral k;
        typename vector<row_entry>::const_iterator it  = r.begin_entries();
        typename vector<row_entry>::const_iterator end = r.end_entries();
        out << "(v" << r.get_base_var() << ") : ";
        bool first = true;
        for (; it != end; ++it) {
            if (it->is_dead())
                continue;
            theory_var v      = it->m_var;
            numeral const & c = it->m_coeff;
            if (is_fixed(v)) {
                k += c * lower_bound(v).get_rational(); 
                continue;
            }
            if (!c.is_int())
                has_rat_coeff = true;
            if (first)
                first = false;
            else
                out << " + ";
            if (!c.is_one())
                out << c << "*";
            out << "v" << v;
        }
        if (!k.is_zero()) {
            if (!first)
                out << " + ";
            out << k;
        }
        out << "\n";
        if (has_rat_coeff) {
            typename vector<row_entry>::const_iterator it  = r.begin_entries();
            typename vector<row_entry>::const_iterator end = r.end_entries();
            for (; it != end; ++it) 
                if (!it->is_dead() && (is_base(it->m_var) || (!is_fixed(it->m_var) && (lower(it->m_var) || upper(it->m_var)))))
                    display_var(out, it->m_var);
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::display_var(std::ostream & out, theory_var v) const {
        out << "v";
        out.width(4);
        out << std::left << v;
        out << " #";
        out.width(4);
        out << get_enode(v)->get_owner_id();
        out << std::right;
        out << " lo:";
        out.width(10);
        if (lower(v)) {
            out << lower(v)->get_value();
        }
        else {
            out << "-oo";
        }
        out << ", up:";
        out.width(10);
        if (upper(v)) {
            out << upper(v)->get_value();
        }
        else {
            out << "oo";
        }
        out << ", value: ";
        out.width(10);
        out << get_value(v);
        out << ", occs: ";
        out.width(4);
        out << m_columns[v].size();
        out << ", atoms: ";
        out.width(4);
        out << m_var_occs[v].size();
        out << (is_int(v) ? ", int " : ", real");
        switch (get_var_kind(v)) {
        case NON_BASE:
            out << ", non-base  ";
            break;
        case QUASI_BASE:
            out << ", quasi-base";
            break;
        case BASE:
            out << ", base      ";
            break;
        }
        out << ", shared: " << get_context().is_shared(get_enode(v));
        out << ", unassigned: " << m_unassigned_atoms[v];
        out << ", rel: " << get_context().is_relevant(get_enode(v));
        out << ", def: ";
        display_var_flat_def(out, v);
        out << "\n";
    }

    template<typename Ext>
    void theory_arith<Ext>::display_vars(std::ostream & out) const {
        out << "vars:\n";
        int n = get_num_vars();
        for (theory_var v = 0; v < n; v++)
            display_var(out, v);
    }

    template<typename Ext>
    void theory_arith<Ext>::display_bound(std::ostream & out, bound * b, unsigned indent) const {
        for (unsigned i = 0; i < indent; i++) out << "  ";
        b->display(*this, out);
        out << "\n";
    }

    template<typename Ext>
    void theory_arith<Ext>::display_deps(std::ostream & out, v_dependency* dep) {
        ptr_vector<void> bounds;
        m_dep_manager.linearize(dep, bounds);
        m_tmp_lit_set.reset();
        m_tmp_eq_set.reset();
        ptr_vector<void>::const_iterator it  = bounds.begin();
        ptr_vector<void>::const_iterator end = bounds.end();
        for (; it != end; ++it) {
            bound * b = static_cast<bound*>(*it);
            out << " ";
            b->display(*this, out);
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::display_interval(std::ostream & out, interval const& i) {
        i.display(out);
        display_deps(out << " lo:", i.get_lower_dependencies());
        display_deps(out << " hi:", i.get_upper_dependencies());
    }

    template<typename Ext>
    void theory_arith<Ext>::display_atoms(std::ostream & out) const {
        out << "atoms:\n";
        for (unsigned i = 0; i < m_atoms.size(); i++)
            display_atom(out, m_atoms[i], false);
    }

    template<typename Ext>
    void theory_arith<Ext>::display_asserted_atoms(std::ostream & out) const {
        out << "asserted atoms:\n";
        for (unsigned i = 0; i < m_asserted_qhead; i++) {
            bound * b = m_asserted_bounds[i];
            if (b->is_atom()) 
                display_atom(out, static_cast<atom*>(b), true);
        }
        if (m_asserted_qhead < m_asserted_bounds.size()) {
            out << "delayed atoms:\n";
            for (unsigned i = m_asserted_qhead; i < m_asserted_bounds.size(); i++) {
                bound * b = m_asserted_bounds[i];
                if (b->is_atom()) 
                    display_atom(out, static_cast<atom*>(b), true);
            }
        }
    }

    template<typename Ext>
    void theory_arith<Ext>::display_atom(std::ostream & out, atom * a, bool show_sign) const {
        theory_var      v = a->get_var();
        inf_numeral const & k = a->get_k();
        enode *         e = get_enode(v);
        if (show_sign) {
            if (!a->is_true()) 
                out << "not ";
            else 
                out << "    ";
        }
        out << "v";
        out.width(3);
        out << std::left << v << " #";
        out.width(3);
        out << e->get_owner_id();
        out << std::right;
        out << " ";
        if (a->get_atom_kind() == A_LOWER)
            out << ">=";
        else
            out << "<=";
        out << " ";
        out.width(6);
        out << k << "    ";
        display_var_flat_def(out, v);
        out << "\n";
    }

    template<typename Ext>
    void theory_arith<Ext>::display_bounds_in_smtlib(std::ostream & out) const {
        ast_manager & m = get_manager();
        ast_smt_pp pp(m);
        pp.set_benchmark_name("lemma");
        int n = get_num_vars();
        for (theory_var v = 0; v < n; v++) {
            expr * n = get_enode(v)->get_owner();
            if (is_fixed(v)) {
                inf_numeral k_inf = lower_bound(v);
                rational k = k_inf.get_rational().to_rational();
                expr_ref eq(m);
                eq = m.mk_eq(n, m_util.mk_numeral(k, is_int(v)));
                pp.add_assumption(eq);
            }
            else {
                if (lower(v) != 0) {
                    inf_numeral k_inf = lower_bound(v);
                    rational k = k_inf.get_rational().to_rational();
                    expr_ref ineq(m);
                    if (k_inf.get_infinitesimal().is_zero())
                        ineq = m_util.mk_le(m_util.mk_numeral(k, is_int(v)), n);
                    else
                        ineq = m_util.mk_lt(m_util.mk_numeral(k, is_int(v)), n);
                    pp.add_assumption(ineq);
                }
                if (upper(v) != 0) {
                    inf_numeral k_inf = upper_bound(v);
                    rational k = k_inf.get_rational().to_rational();
                    expr_ref ineq(m);
                    if (k_inf.get_infinitesimal().is_zero())
                        ineq = m_util.mk_le(n, m_util.mk_numeral(k, is_int(v)));
                    else
                        ineq = m_util.mk_lt(n, m_util.mk_numeral(k, is_int(v)));
                    pp.add_assumption(ineq);
                }
            }
        }
        pp.display(out, m.mk_true());
    }

    template<typename Ext>
    void theory_arith<Ext>::display_bounds_in_smtlib() const {
        char buffer[128];
        static int id = 0;
#ifdef _WINDOWS
        sprintf_s(buffer, ARRAYSIZE(buffer), "arith_%d.smt", id);
#else
        sprintf(buffer, "arith_%d.smt", id);
#endif
        std::ofstream out(buffer);
        display_bounds_in_smtlib(out);
        out.close();
        id++;
    }

};

#endif /* _THEORY_ARITH_PP_H_ */

