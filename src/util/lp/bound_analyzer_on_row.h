/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include "util/vector.h"
#include "implied_bound.h"
#include "test_bound_analyzer.h"
#include "util/lp/bound_propagator.h"
// We have an equality : sum by j of row[j]*x[j] = rs
// We try to pin a var by pushing the total by using the variable bounds
// In a loop we drive the partial sum down, denoting the variables of this process by _u.
// In the same loop trying to pin variables by pushing the partial sum up, denoting the variable related to it by _l
namespace lp {
template <typename C> // C plays a role of a container
class bound_analyzer_on_row {
    const C&                           m_row;
    bound_propagator &                 m_bp;
    unsigned                           m_row_or_term_index;
    int                                m_column_of_u; // index of an unlimited from above monoid
    // -1 means that such a value is not found, -2 means that at least two of such monoids were found
    int                                m_column_of_l; // index of an unlimited from below monoid
    impq                               m_rs;

public :
    // constructor
    bound_analyzer_on_row(
        const C & it,
        unsigned  bj, // basis column for the row
        const numeric_pair<mpq>& rs,
        unsigned row_or_term_index,
        bound_propagator & bp
                          )
        :
        m_row(it),
        m_bp(bp),
        m_row_or_term_index(row_or_term_index),
        m_column_of_u(-1),
        m_column_of_l(-1),
        m_rs(rs)
    {}


    unsigned j;
    void analyze() {
        for (const auto & c : m_row) {
            if ((m_column_of_l == -2) && (m_column_of_u == -2))
                break;
            analyze_bound_on_var_on_coeff(c.var(), c.coeff());
        }
        if (m_column_of_u >= 0)
            limit_monoid_u_from_below();
        else if (m_column_of_u == -1)
            limit_all_monoids_from_below();

        if (m_column_of_l >= 0)
            limit_monoid_l_from_above();
        else if (m_column_of_l == -1)
            limit_all_monoids_from_above();
    }

    bool bound_is_available(unsigned j, bool lower_bound) {
        return (lower_bound && lower_bound_is_available(j)) ||
            (!lower_bound && upper_bound_is_available(j));
    }

    bool upper_bound_is_available(unsigned j) const {
        switch (m_bp.get_column_type(j))
            {
            case column_type::fixed:
            case column_type::boxed:
            case column_type::upper_bound:
                return true;
            default:
                return false;
            }
    }

    bool lower_bound_is_available(unsigned j) const {
        switch (m_bp.get_column_type(j))
            {
            case column_type::fixed:
            case column_type::boxed:
            case column_type::lower_bound:
                return true;
            default:
                return false;
            }
    }

    const impq & ub(unsigned j) const {
        lp_assert(upper_bound_is_available(j));
        return m_bp.get_upper_bound(j);
    }
    const impq & lb(unsigned j) const {
        lp_assert(lower_bound_is_available(j));
        return m_bp.get_lower_bound(j);
    }


    const mpq & monoid_max_no_mult(bool a_is_pos, unsigned j, bool & strict) const {
        if (a_is_pos) {
            strict = !is_zero(ub(j).y);
            return ub(j).x;
        }
        strict = !is_zero(lb(j).y);
        return lb(j).x;
    }
    mpq monoid_max(const mpq & a, unsigned j) const {
        if (is_pos(a)) {
            return a * ub(j).x;
        }
        return a * lb(j).x;
    }
    mpq monoid_max(const mpq & a, unsigned j, bool & strict) const {
        if (is_pos(a)) {
            strict = !is_zero(ub(j).y);
            return a * ub(j).x;
        }
        strict = !is_zero(lb(j).y);
        return a * lb(j).x;
    }
    const mpq & monoid_min_no_mult(bool a_is_pos, unsigned j, bool & strict) const {
        if (!a_is_pos) {
            strict = !is_zero(ub(j).y);
            return ub(j).x;
        }
        strict = !is_zero(lb(j).y);
        return lb(j).x;
    }

    mpq monoid_min(const mpq & a, unsigned j, bool& strict) const {
        if (is_neg(a)) {
            strict = !is_zero(ub(j).y);
            return a * ub(j).x;
        }
        
        strict = !is_zero(lb(j).y);
        return a * lb(j).x;
    }

    mpq monoid_min(const mpq & a, unsigned j) const {
        if (is_neg(a)) {
            return a * ub(j).x;
        }
        
        return a * lb(j).x;
    }
    

    void limit_all_monoids_from_above() {
        int strict = 0;
        mpq total;
        lp_assert(is_zero(total));
        for (const auto& p : m_row) {
            bool str;
            total -= monoid_min(p.coeff(), p.var(), str);
            if (str)
                strict++;
        }

        
        for (const auto &p : m_row) {
            bool str;
            bool a_is_pos = is_pos(p.coeff());
            mpq bound = total / p.coeff() + monoid_min_no_mult(a_is_pos, p.var(), str);
            if (a_is_pos) {
                limit_j(p.var(), bound, true, false, strict - static_cast<int>(str) > 0);
            }
            else {
                limit_j(p.var(), bound, false, true, strict - static_cast<int>(str) > 0);
            }
        }
    }

    void limit_all_monoids_from_below() {
        int strict = 0;
        mpq total;
        lp_assert(is_zero(total));
        for (const auto &p : m_row) {
            bool str;
            total -= monoid_max(p.coeff(), p.var(), str);
            if (str)
                strict++;
        }

        for (const auto& p : m_row) {
            bool str;
            bool a_is_pos = is_pos(p.coeff());
            mpq bound = total / p.coeff() + monoid_max_no_mult(a_is_pos, p.var(), str);
            bool astrict = strict - static_cast<int>(str) > 0; 
            if (a_is_pos) {
                limit_j(p.var(), bound, true, true, astrict);
            }
            else {
                limit_j(p.var(), bound, false, false, astrict);
            }
        }
    }

    
    void limit_monoid_u_from_below() {
        // we are going to limit from below the monoid m_column_of_u,
        // every other monoid is impossible to limit from below
        mpq u_coeff;
        unsigned j;
        mpq bound = -m_rs.x;
        bool strict = false;
        for (const auto& p : m_row) {
            j = p.var();
            if (j == static_cast<unsigned>(m_column_of_u)) {
                u_coeff = p.coeff();
                continue;
            }
            bool str;
            bound -= monoid_max(p.coeff(), j, str);
            if (str)
                strict = true;
        }

        bound /= u_coeff;
        
        if (numeric_traits<impq>::is_pos(u_coeff)) {
            limit_j(m_column_of_u, bound, true, true, strict);
        } else {
            limit_j(m_column_of_u, bound, false, false, strict);
        }
    }


    void limit_monoid_l_from_above() {
        // we are going to limit from above the monoid m_column_of_l,
        // every other monoid is impossible to limit from above
        mpq l_coeff;
        unsigned j;
        mpq bound = -m_rs.x;
        bool strict = false;
        for (const auto &p : m_row) {
            j = p.var();
            if (j == static_cast<unsigned>(m_column_of_l)) {
                l_coeff = p.coeff();
                continue;
            }

            bool str;
            bound -= monoid_min(p.coeff(), j, str);
            if (str)
                strict = true;
        }
        bound /= l_coeff;
        if (is_pos(l_coeff)) {
            limit_j(m_column_of_l, bound, true, false, strict);
        } else {
            limit_j(m_column_of_l, bound, false, true, strict);
        }
    }
    
    // // it is the coefficient before the bounded column
    // void provide_evidence(bool coeff_is_pos) {
    //     /*
    //     auto & be = m_ibounds.back();
    //     bool lower_bound = be.m_lower_bound;
    //     if (!coeff_is_pos)
    //         lower_bound = !lower_bound;
    //     auto it = m_row.clone();
    //     mpq a; unsigned j;
    //     while (it->next(a, j)) {
    //         if (be.m_j == j) continue;
    //         lp_assert(bound_is_available(j, is_neg(a) ? lower_bound : !lower_bound));
    //         be.m_vector_of_bound_signatures.emplace_back(a, j, numeric_traits<impq>::
    //                                                      is_neg(a)? lower_bound: !lower_bound);
    //     }
    //     delete it;
    //     */
    // }

    void limit_j(unsigned j, const mpq& u, bool coeff_before_j_is_pos, bool is_lower_bound, bool strict){
        m_bp.try_add_bound(u, j, is_lower_bound, coeff_before_j_is_pos, m_row_or_term_index, strict);
    }

    
    void advance_u(unsigned j) {
        if (m_column_of_u == -1)
            m_column_of_u = j;
        else
            m_column_of_u = -2;
    }
    
    void advance_l(unsigned j) {
        if (m_column_of_l == -1)
            m_column_of_l = j;
        else
            m_column_of_l = -2;
    }
    
    void analyze_bound_on_var_on_coeff(int j, const mpq &a) {
        switch (m_bp.get_column_type(j)) {
        case column_type::lower_bound:
            if (numeric_traits<mpq>::is_pos(a))
                advance_u(j);
            else 
                advance_l(j);
            break;
        case column_type::upper_bound:
            if(numeric_traits<mpq>::is_neg(a))
                advance_u(j);
            else
                advance_l(j);
            break;
        case column_type::free_column:
            advance_u(j);
            advance_l(j);
            break;
        default:
            break;
        }
    }

    static void analyze_row(const C & row,
                            unsigned bj, // basis column for the row
                            const numeric_pair<mpq>& rs,
                            unsigned row_or_term_index,
                            bound_propagator & bp
                            ) {
        bound_analyzer_on_row a(row, bj, rs, row_or_term_index, bp);
        a.analyze();
    }

};
}

