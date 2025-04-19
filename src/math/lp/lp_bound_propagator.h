/*
  Copyright (c) 2017 Microsoft Corporation
  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson   (levnach)
*/
#pragma once
#include <utility>
#include "math/lp/lp_settings.h"
#include "util/uint_set.h"
#include "math/lp/implied_bound.h"
#include "util/vector.h"
namespace lp {
    
template <typename T>
class lp_bound_propagator {
    uint_set m_visited_rows;
    // these maps map a column index to the corresponding index in ibounds
    u_map<unsigned> m_improved_lower_bounds;
    u_map<unsigned> m_improved_upper_bounds;

    T& m_imp;
    std_vector<implied_bound>& m_ibounds;

    map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>> m_val2fixed_row;
    // works for rows of the form x + y + sum of fixed = 0
    map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>> m_row2index_pos;
    // works for rows of the form x - y + sum of fixed = 0    
    map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>> m_row2index_neg;

    const vector<column_type>*                         m_column_types = nullptr;
    // returns true iff there is only one non-fixed column in the row
    bool only_one_nfixed(unsigned r, unsigned& x) {
        x = UINT_MAX;
        for (const auto& c: lp().get_row(r)) {
            if (column_is_fixed(c.var()))
                continue;
            if (x != UINT_MAX)
                return false;
            x = c.var();
        }
        return x != UINT_MAX;
    }
public:
    const lar_solver& lp() const { return m_imp.lp(); }
    lar_solver& lp() { return m_imp.lp(); }
    bool upper_bound_is_available(unsigned j) const {
        switch (get_column_type(j)) {
        case column_type::fixed:
        case column_type::boxed:
        case column_type::upper_bound:
            return true;
        default:
            return false;
        }
    }
    bool lower_bound_is_available(unsigned j) const {
        switch (get_column_type(j)) {
        case column_type::fixed:
        case column_type::boxed:
        case column_type::lower_bound:
            return true;
        default:
            return false;
        }
    }
private:
    void try_add_equation_with_internal_fixed_tables(unsigned r1) {
        unsigned v1, v2;
        if (!only_one_nfixed(r1, v1))
            return;
        unsigned r2 = UINT_MAX;
        if (!m_val2fixed_row.find(val(v1), r2) || r2 >= lp().row_count()) {
            m_val2fixed_row.insert(val(v1), r1);
            return;
        }
        if (!only_one_nfixed(r2, v2) || val(v1) != val(v2) || is_int(v1) != is_int(v2)) {
            m_val2fixed_row.insert(val(v1), r1);
            return;
        }
        if (v1 == v2)
            return;
#if Z3DEBUG
        SASSERT(val(v1) == val(v2));
        unsigned debv1, debv2;
        SASSERT(only_one_nfixed(r1, debv1) && only_one_nfixed(r2, debv2));
        SASSERT(debv1 == v1 && debv2 == v2);
        SASSERT(ival(v1).y == ival(v2).y);
#endif
        explanation ex;
        explain_fixed_in_row(r1, ex);
        explain_fixed_in_row(r2, ex);
        TRACE("eq", print_row(tout, r1); print_row(tout, r2); tout << v1 << " == " << v2 << " = " << val(v1) << "\n");
        add_eq_on_columns(ex, v1, v2, true);
    }

    static bool is_not_set(unsigned j) { return j == UINT_MAX; }
    static bool is_set(unsigned j) { return j != UINT_MAX; }

    void reset_cheap_eq_eh() {
        m_row2index_pos.reset();           
        m_row2index_neg.reset();
    }

    struct reset_cheap_eq {
        lp_bound_propagator& p;
        reset_cheap_eq(lp_bound_propagator& p) : p(p) {}
        ~reset_cheap_eq() { p.reset_cheap_eq_eh(); }
    };

public:
    lp_bound_propagator(T& imp, std_vector<implied_bound> & ibounds) : m_imp(imp), m_ibounds(ibounds) {}

    const std_vector<implied_bound>& ibounds() const { return m_ibounds; }

    void init() {
        m_improved_upper_bounds.reset();
        m_improved_lower_bounds.reset();
        m_ibounds.clear();
        m_column_types = &lp().get_column_types();
    }
   
    column_type get_column_type(unsigned j) const {
        return (*m_column_types)[j];
    }

    const impq& get_lower_bound(unsigned j) const {
        return lp().get_lower_bound(j);
    }

    const mpq& get_lower_bound_rational(unsigned j) const {
        return lp().get_lower_bound(j).x;
    }

    const impq& get_upper_bound(unsigned j) const {
        return lp().get_upper_bound(j);
    }

    const mpq& get_upper_bound_rational(unsigned j) const {
        return lp().get_upper_bound(j).x;
    }

    // require also the zero infinitesemal part
    bool column_is_fixed(lpvar j) const {
        return (*m_column_types)[j] == column_type::fixed && get_lower_bound(j).y.is_zero();
    }


    void add_bound(mpq const& v, unsigned j, bool is_low, bool strict, std::function<u_dependency* ()> explain_bound) {
        lconstraint_kind kind = is_low ? GE : LE;
        if (strict)
            kind = static_cast<lconstraint_kind>(kind / 2);

        if (!m_imp.bound_is_interesting(j, kind, v))
            return;
        if (is_low) {
            unsigned k;
            if (m_improved_lower_bounds.find(j, k)) {
                auto& found_bound = m_ibounds[k];
                if (v > found_bound.m_bound || (v == found_bound.m_bound && !found_bound.m_strict && strict)) {

                    found_bound.m_bound = v;
                    found_bound.m_strict = strict;
                    found_bound.set_explain(explain_bound);
                    TRACE("add_bound", lp().print_implied_bound(found_bound, tout););
                }
            } else {
                m_improved_lower_bounds.insert(j, static_cast<unsigned>(m_ibounds.size()));
                m_ibounds.push_back(implied_bound(v, j, is_low, strict, explain_bound));
                TRACE("add_bound", lp().print_implied_bound(m_ibounds.back(), tout););
            }
        } else {  // the upper bound case
            unsigned k;
            if (m_improved_upper_bounds.find(j, k)) {
                auto& found_bound = m_ibounds[k];
                if (v < found_bound.m_bound || (v == found_bound.m_bound && !found_bound.m_strict && strict)) {

                    found_bound.m_bound = v;
                    found_bound.m_strict = strict;
                    found_bound.set_explain(explain_bound);
                    TRACE("add_bound", lp().print_implied_bound(found_bound, tout););
                }
            } else {
                m_improved_upper_bounds.insert(j, static_cast<unsigned>(m_ibounds.size()));
                m_ibounds.push_back(implied_bound(v, j, is_low, strict, explain_bound));
                TRACE("add_bound", lp().print_implied_bound(m_ibounds.back(), tout););
            }
        }
    }

    void consume(const mpq& a, constraint_index ci) {
        m_imp.consume(a, ci);
    }

    const mpq& val(unsigned j) const {
        return lp().get_column_value(j).x; // figure out why it is safe to return .x
    }
    
    const impq& ival(unsigned j) const {
        return lp().get_column_value(j); // figure out why it is safe to return .x
    }

    unsigned column(unsigned row, unsigned index) {
        return lp().get_row(row)[index].var();
    }


    bool is_equal(lpvar j, lpvar k) const {
        return m_imp.is_equal(col_to_imp(j), col_to_imp(k));
    }

    void clear_for_eq() {
        m_visited_rows.reset();
    }

    bool add_eq_on_columns(const explanation& exp, lpvar je, lpvar ke, bool is_fixed) {
        SASSERT(je != ke && is_int(je) == is_int(ke));
        SASSERT(ival(je) == ival(ke));

        TRACE("eq",
              tout << "reported idx " << je << ", " << ke << "\n";
              lp().print_expl(tout, exp);
              tout << "theory_vars v" << lp().local_to_external(je) << " == v" << lp().local_to_external(ke) << "\n";);

        bool added = m_imp.add_eq(je, ke, exp, is_fixed);
        if (added) {
            if (is_fixed)
                lp().stats().m_fixed_eqs++;
            else
                lp().stats().m_offset_eqs++;
        }
        return added;
    }

    // column to theory_var
    unsigned col_to_imp(unsigned j) const {
        return lp().local_to_external(j);
    }

    // theory_var to column
    unsigned imp_to_col(unsigned j) const {
        return lp().external_to_local(j);
    }

    bool is_int(lpvar j) const {
        return lp().column_is_int(j);
    }

    void explain_fixed_in_row(unsigned row, explanation& ex) {
        TRACE("eq", tout << lp().get_row(row) << std::endl);
        for (const auto& c : lp().get_row(row))
            if (lp().column_is_fixed(c.var()))
                lp().explain_fixed_column(c.var(), ex);
    }

    unsigned explain_fixed_in_row_and_get_base(unsigned row, explanation& ex) {
        unsigned base = UINT_MAX;
        TRACE("eq", tout << lp().get_row(row) << std::endl);
        for (const auto& c : lp().get_row(row)) {
            if (lp().column_is_fixed(c.var())) {
                lp().explain_fixed_column(c.var(), ex);
            } 
            else if (lp().is_base(c.var())) {
                base = c.var();
            }
        }
        return base;
    }
    
#ifdef Z3DEBUG
    bool all_fixed_in_row(unsigned row) const {
        for (const auto& c : lp().get_row(row))
            if (!lp().column_is_fixed(c.var()))
                return false;
        return true;
    }

    // bounded by 2
    unsigned num_of_non_fixed_in_row(unsigned row_index) const {
        unsigned n_of_nfixed = 0;
        for (const auto& c : lp().get_row(row_index)) {
            if (column_is_fixed(c.var()))
                continue;
            n_of_nfixed++;
            if (n_of_nfixed > 1)
                return n_of_nfixed;
        }
            
        return n_of_nfixed;
    }   
#endif
    // Let nf is the number of non-fixed columns in the row.
    // Then the function returns min(nf, 3).
    // if nf == 0, the row is of the form sum of fixed = 0
    // if nf == 1, the row is of the form x + sum of fixed = 0, where x is not fixed base
    // if nf == 2, the row is of the form x + ay + sum of fixed = 0, x is a non fixed base and y is not fixed 
    // y_sign is set to a, if abs(a)= 1, and 0 otherwise

    unsigned extract_non_fixed(unsigned row_index, unsigned& x, unsigned& y, int& y_sign) const {
        unsigned nf = 0;  // number of non-fixed columns
        y = UINT_MAX;
        const auto& row = lp().get_row(row_index);
        x = lp().get_base_column_in_row(row_index);
        if (!column_is_fixed(x)) {
            nf++;
        } else {
            // we have a fixed base column, exiting
            return 0;
        }

        for (const auto& c : row) {
            unsigned j = c.var();
            if (j == x) continue;
            if (column_is_fixed(j))
                continue;
            if (++nf > 2)
                return nf;
            SASSERT(is_not_set(y));
            y = j;
            if (c.coeff().is_one()) {
                y_sign = 1;
            } else if (c.coeff().is_minus_one()) {
                y_sign = -1;
            } else {
                // y has a coefficient other than 1 or -1
                y_sign = 0;
                return nf; // maybe be too low but we don't care
            }
        }

        return nf;
    }

    void try_add_equation_with_lp_fixed_tables(unsigned row_index, unsigned v_j) {
        SASSERT(lp().get_base_column_in_row(row_index) == v_j);
        SASSERT(num_of_non_fixed_in_row(row_index) == 1 || column_is_fixed(v_j));
        if (column_is_fixed(v_j)) {
            return;
        }
        unsigned j = null_lpvar;
        if (!lp().find_in_fixed_tables(val(v_j), is_int(v_j), j)) {
            try_add_equation_with_internal_fixed_tables(row_index);
            return;
        } 
        TRACE("eq",
              tout << "v_j = ";
              lp().print_column_info(v_j, tout) << std::endl;
              tout << "found j " << j << std::endl; lp().print_column_info(j, tout) << std::endl;
              print_row(tout, row_index) << std::endl;
              );
        explanation ex;  
        explain_fixed_in_row(row_index, ex);
        lp().explain_fixed_column(j, ex);
        add_eq_on_columns(ex, j, v_j, true);
    }

    void cheap_eq_on_nbase(unsigned row_index) {
        reset_cheap_eq _reset(*this);
        TRACE("eq", tout << "row_index = " << row_index << "\n";
                    print_row(tout, row_index) << "\n";);
        if (!check_insert(m_visited_rows, row_index))
            return;
        unsigned x, y;
        int y_sign;
        unsigned nf = extract_non_fixed(row_index, x, y, y_sign);
        if (nf == 0 || nf > 2)
            return;
        if (nf == 1) {
            SASSERT(is_not_set(y));
            try_add_equation_with_lp_fixed_tables(row_index, x);
            return;
        }
        if (y_sign == 0) {
            // the coefficient before y is not 1 or -1
            return;
        }
        SASSERT(y_sign == -1 || y_sign == 1);
        SASSERT(lp().is_base(y) == false);
        auto& table = y_sign == 1 ? m_row2index_pos : m_row2index_neg;
        table.insert(val(x), row_index);        
        TRACE("eq", tout << "y = " << y << "\n";);    

        for (const column_cell& c : lp().get_column(y)) {
            unsigned i = c.var();  // the running index of the row
            if (i == row_index)
                continue;
            if (!check_insert(m_visited_rows, i))
                continue;
            unsigned y_nb;
            nf = extract_non_fixed(i, x, y_nb, y_sign);
            if (nf != 2 || y_sign == 0)
                continue;

            SASSERT(y_nb == y);
            SASSERT(y_sign == 1 || y_sign == -1);
            auto& table = y_sign == 1 ? m_row2index_pos : m_row2index_neg;
            const auto& v = val(x);
            unsigned found_i;;
            
            if (!table.find(v, found_i)) {
                table.insert(v, i);
            } else {
                explanation ex;
                unsigned base_of_found = lp().get_base_column_in_row(found_i);
                if (is_int(x) != is_int(base_of_found) || ival(x).y != ival(base_of_found).y)
                    continue;
                explain_fixed_in_row(found_i, ex);
                explain_fixed_in_row(i, ex);
                TRACE("eq", {
                    print_row(tout, i);
                    print_row(tout, found_i) << "\n";
                    lp().print_column_info(base_of_found, tout);
                    lp().print_column_info(x, tout) << "\n";
                });
                add_eq_on_columns(ex, x, base_of_found, false);
            }
        }
    }

    std::ostream& print_row(std::ostream& out, unsigned row_index) const {
        bool first = true;
        for (const auto& c : lp().A_r().m_rows[row_index]) {
            if (lp().column_is_fixed(c.var()))
                continue;
            if (c.coeff().is_one()) {
                if (!first)
                    out << "+";
            } else if (c.coeff().is_minus_one())
                out << "-";
            out << lp().get_variable_name(c.var()) << " ";
            first = false;
        }
        out << "\n";
        return out;
    }

    template <typename C>
    bool check_insert(C& table, unsigned j) {
        if (table.contains(j))
            return false;
        table.insert(j);
        return true;
    }
};
}  // namespace lp
