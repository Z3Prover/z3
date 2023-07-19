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
namespace lp {
template <typename T>
class lp_bound_propagator {
	hashtable<unsigned, u_hash, u_eq> m_visited_rows;
    // these maps map a column index to the corresponding index in ibounds
    std::unordered_map<unsigned, unsigned> m_improved_lower_bounds;
    std::unordered_map<unsigned, unsigned> m_improved_upper_bounds;

    T& m_imp;
    vector<implied_bound> m_ibounds;

    map<impq, unsigned, obj_hash<impq>, default_eq<impq>> m_val2fixed_row;

    bool is_fixed_row(unsigned r, unsigned& x) {
        x = UINT_MAX;
        const auto& row = lp().get_row(r);
        for (unsigned k = 0; k < row.size(); k++) {
            const auto& c = row[k];
            if (column_is_fixed(c.var()))
                continue;
            if (x != UINT_MAX)
                return false;
            x = c.var();
        }
        return x != UINT_MAX;
    }

    void try_add_equation_with_internal_fixed_tables(unsigned r1) {
        unsigned v1, v2;
        if (!is_fixed_row(r1, v1))
            return;
        unsigned r2 = UINT_MAX;
        if (!m_val2fixed_row.find(val(v1), r2) || r2 >= lp().row_count()) {
            m_val2fixed_row.insert(val(v1), r1);
            return;
        }
        if (!is_fixed_row(r2, v2) || val(v1) != val(v2) || is_int(v1) != is_int(v2)) {
            m_val2fixed_row.insert(val(v1), r1);
            return;
        }
        if (v1 == v2)
            return;

        explanation ex;
        explain_fixed_in_row(r1, ex);
        explain_fixed_in_row(r2, ex);
        TRACE("eq", print_row(tout, r1); print_row(tout, r2); tout << v1 << " == " << v2 << " = " << val(v1) << "\n");
        add_eq_on_columns(ex, v1, v2, true);
    }

    static bool not_set(unsigned j) { return j == UINT_MAX; }
    static bool is_set(unsigned j) { return j != UINT_MAX; }

    void reset_cheap_eq_eh() {
        for (auto e : m_row2index) {
            dealloc(e.m_key);
        }
        m_row2index.reset();   
    }

    struct reset_cheap_eq {
        lp_bound_propagator& p;
        reset_cheap_eq(lp_bound_propagator& p) : p(p) {}
        ~reset_cheap_eq() { p.reset_cheap_eq_eh(); }
    };

   public:
    lp_bound_propagator(T& imp) : m_imp(imp) {}

    const vector<implied_bound>& ibounds() const { return m_ibounds; }

    void init() {
        m_improved_upper_bounds.clear();
        m_improved_lower_bounds.clear();
        m_ibounds.reset();
    }

    const lar_solver& lp() const { return m_imp.lp(); }
    lar_solver& lp() { return m_imp.lp(); }

    column_type get_column_type(unsigned j) const {
        return m_imp.lp().get_column_type(j);
    }

    const impq& get_lower_bound(unsigned j) const {
        return m_imp.lp().get_lower_bound(j);
    }

    const mpq& get_lower_bound_rational(unsigned j) const {
        return m_imp.lp().get_lower_bound(j).x;
    }

    const impq& get_upper_bound(unsigned j) const {
        return m_imp.lp().get_upper_bound(j);
    }

    const mpq& get_upper_bound_rational(unsigned j) const {
        return m_imp.lp().get_upper_bound(j).x;
    }

    // require also the zero infinitesemal part
    bool column_is_fixed(lpvar j) const {
        return lp().column_is_fixed(j) && get_lower_bound(j).y.is_zero();
    }

    void try_add_bound(mpq const& v, unsigned j, bool is_low, bool coeff_before_j_is_pos, unsigned row_or_term_index, bool strict) {
        j = m_imp.lp().column_to_reported_index(j);

        lconstraint_kind kind = is_low ? GE : LE;
        if (strict)
            kind = static_cast<lconstraint_kind>(kind / 2);

        if (!m_imp.bound_is_interesting(j, kind, v))
            return;
        unsigned k;  // index to ibounds
        if (is_low) {
            if (try_get_value(m_improved_lower_bounds, j, k)) {
                auto& found_bound = m_ibounds[k];
                if (v > found_bound.m_bound || (v == found_bound.m_bound && !found_bound.m_strict && strict)) {
                    found_bound = implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict);
                    TRACE("try_add_bound", m_imp.lp().print_implied_bound(found_bound, tout););
                }
            } else {
                m_improved_lower_bounds[j] = m_ibounds.size();
                m_ibounds.push_back(implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict));
                TRACE("try_add_bound", m_imp.lp().print_implied_bound(m_ibounds.back(), tout););
            }
        } else {  // the upper bound case
            if (try_get_value(m_improved_upper_bounds, j, k)) {
                auto& found_bound = m_ibounds[k];
                if (v < found_bound.m_bound || (v == found_bound.m_bound && !found_bound.m_strict && strict)) {
                    found_bound = implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict);
                    TRACE("try_add_bound", m_imp.lp().print_implied_bound(found_bound, tout););
                }
            } else {
                m_improved_upper_bounds[j] = m_ibounds.size();
                m_ibounds.push_back(implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict));
                TRACE("try_add_bound", m_imp.lp().print_implied_bound(m_ibounds.back(), tout););
            }
        }
    }

    void consume(const mpq& a, constraint_index ci) {
        m_imp.consume(a, ci);
    }

    const impq& val(unsigned j) const {
        return lp().get_column_value(j);
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

    std::ostream& print_expl(std::ostream& out, const explanation& exp) const {
        for (auto p : exp)
            lp().constraints().display(
                out, [this](lpvar j) { return lp().get_variable_name(j); }, p.ci());
        return out;
    }

    bool add_eq_on_columns(const explanation& exp, lpvar j, lpvar k, bool is_fixed) {
        SASSERT(j != k);
        unsigned je = lp().column_to_reported_index(j);
        unsigned ke = lp().column_to_reported_index(k);
        TRACE("cheap_eq",
              tout << "reporting eq " << j << ", " << k << "\n";
              tout << "reported idx " << je << ", " << ke << "\n";
              print_expl(tout, exp);
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
        return lp().local_to_external(lp().column_to_reported_index(j));
    }

    // theory_var to column
    unsigned imp_to_col(unsigned j) const {
        return lp().external_to_column_index(j);
    }

    bool is_int(lpvar j) const {
        return lp().column_is_int(j);
    }

    void explain_fixed_in_row(unsigned row, explanation& ex) const {
        TRACE("cheap_eq", tout << lp().get_row(row) << std::endl);
        for (const auto& c : lp().get_row(row))
            if (lp().is_fixed(c.var()))
                explain_fixed_column(c.var(), ex);
    }

    unsigned explain_fixed_in_row_and_get_base(unsigned row, explanation& ex) const {
        unsigned base = UINT_MAX;
        TRACE("cheap_eq", tout << lp().get_row(row) << std::endl);
        for (const auto& c : lp().get_row(row)) {
            if (lp().is_fixed(c.var())) {
                explain_fixed_column(c.var(), ex);
            } else if (lp().is_base(c.var())) {
                base = c.var();
            }
        }
        return base;
    }

    void explain_fixed_column(unsigned j, explanation& ex) const {
        SASSERT(column_is_fixed(j));
        constraint_index lc, uc;
        lp().get_bound_constraint_witnesses_for_column(j, lc, uc);
        ex.push_back(lc);
        ex.push_back(uc);
    }

    // If the row has exactly two non fixed columns,
    // and one of those is base, fill the base and nbase and return true.
    // Otherwise return false.
    bool get_two_nfixed(unsigned row_index, const row_cell<mpq>** base, const row_cell<mpq>** nbase) const {
        unsigned n_of_nfixed = 0;
        *base = nullptr;
        for (const auto& c : lp().get_row(row_index)) {
            if (lp().column_is_fixed(c.var()))
                continue;
            n_of_nfixed++;
            if (n_of_nfixed > 2)
                return false;

            if (lp().is_base(c.var())) {
                *base = &c;
            } else {
                *nbase = &c;
            }
        }
        return n_of_nfixed == 2 && *base != nullptr;
    }

    // the row is of the form x + a*y + sum of fixed = 0, where x and y are non fixed,
    // x is a base, and y is not a base variable. The pair (value of x,a)
    // is the key of the m_row2index. 
    struct row {
        const impq* m_base_val;
        const mpq* m_nbase_coeff;
        row(const impq* base_val, const mpq* nbase_coeff) : m_base_val(base_val), m_nbase_coeff(nbase_coeff) {}
        row() {}
        row(const row& r) : m_base_val(r.m_base_val), m_nbase_coeff(r.m_nbase_coeff) {}
        unsigned hash() const { return combine_hash(m_base_val->hash(), m_nbase_coeff->hash()); }
        bool operator==(const row& r) const {
            return *(r.m_base_val) == *m_base_val && *(r.m_nbase_coeff) == *m_nbase_coeff;
        }
    };

    map<row*, unsigned, obj_ptr_hash<row>, deref_eq<row>> m_row2index;
    
    void cheap_eq_tree(unsigned row_index) {
        reset_cheap_eq _reset(*this);
        TRACE("cheap_eq_det", tout << "row_index = " << row_index << "\n";);
        if (!check_insert(m_visited_rows, row_index))
            return;
        const row_cell<mpq>*base_cell, *non_base_cell;
        if (!get_two_nfixed(row_index, &base_cell, &non_base_cell))
            return;
        unsigned j = non_base_cell->var();
        for (const column_cell& c : lp().get_column(j)) {
            unsigned i = c.var();  // the running index of the row
            m_visited_rows.insert(i);
            if (!get_two_nfixed(i, &base_cell, &non_base_cell))
                continue;
            row r(&val(base_cell->var()), &(non_base_cell->coeff()));
            const auto* entry = m_row2index.find_core(&r);
            if (entry == nullptr) {
                row* nr = new row(r);
                m_row2index.insert(nr, i);
            } else {
                explanation ex;
                unsigned found_i = entry->get_data().m_value;
                unsigned j0 = explain_fixed_in_row_and_get_base(found_i, ex);
                explain_fixed_in_row(i, ex);
                TRACE("eq", { print_row(tout, i); print_row(tout, found_i) << "\n";
                              lp().print_column_info(j0, tout);
                              lp().print_column_info(base_cell->var(), tout) << "\n"; 
                            });
                add_eq_on_columns(ex, j0, base_cell->var(), false);
            }
        }

        // rows_of_j.push_back(row(row_index, *base_cell, *non_base_cell));
        // m_visited_rows.insert(row_index);
        // get_j_rows(non_base_cell->var(), rows_of_j);
        // if (rows_of_j.size() <= 1) {
        //     return;
        // }
        // vector<unsigned> index;
        // for (unsigned i = 0; i < rows_of_j.size(); i++) {
        //     index.push_back(i);
        // }
        // std::sort(index.begin(), index.end(), [&](unsigned i, unsigned j) {
        //     return rows_of_j[i].m_nbase.coeff() < rows_of_j[j].m_nbase.coeff();
        // });
        // // the map of values of the base variable of the group with the same coefficient
        // map<mpq, unsigned, obj_hash<mpq>, default_eq<mpq>> val_to_index;
        // const row* group_row;
        
        // for (unsigned i = 0; i < index.size(); i++) {
        //     const row& r = rows_of_j[index[i]];
        //     TRACE("eq",  print_row(tout, r.m_row_index); tout << "r.m_base.var() = " << r.m_base.var() <<"\n";);
        //     if (i == 0 || r.m_nbase.coeff() != rows_of_j[index[i - 1]].m_nbase.coeff()) {
        //         val_to_index.reset();
        //         val_to_index.insert(val(r.m_base.var()), index[i]);
        //         group_row = &rows_of_j[index[i]];
        //     } else {
        //         unsigned prev_j;
        //         if (val_to_index.find(val(r.m_base.var()), prev_j)) {
        //             explanation ex;
        //             explain_fixed_in_row(group_row->m_row_index, ex);
        //             explain_fixed_in_row(r.m_row_index, ex);
        //             TRACE("eq", print_row(tout, group_row->m_row_index); print_row(tout, r.m_row_index); 
        //             tout << group_row->m_base.var() << " == " << r.m_base.var() << " = " << val(r.m_base.var()) << "\n");
        //             add_eq_on_columns(ex, group_row->m_base.var(), r.m_base.var(), false);
        //         }
        //     }
        // }
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
