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
#if 0
#pragma once
#include "util/vector.h"
#include "math/lp/implied_bound.h"
#include "math/lp/lp_settings.h"
#include <functional>
// this class is for testing only

// We have an equality : sum by j of row[j]*x[j] = rs
// We try to pin a var by pushing the total by using the variable bounds
// In a loop we drive the partial sum down, denoting the variables of this process by _u.
// In the same loop trying to pin variables by pushing the partial sum up, denoting the variable related to it by _l

// here in addition we assume that all coefficient in the row are positive
namespace lp {

class test_bound_analyzer {
    linear_combination_iterator<mpq> & m_it;
    std::function<impq (unsigned)>& m_lower_bounds;
    std::function<impq (unsigned)>& m_upper_bounds;
    std::function<column_type (unsigned)> m_column_types;
    vector<implied_bound> & m_implied_bounds;
    vector<mpq> m_coeffs;
    int m_coeff_sign;
    vector<unsigned> m_index;
    unsigned m_row_or_term_index;
    std::function<bool (unsigned, bool, mpq &, bool & strict)> & m_try_get_found_bound;
public :
    // constructor
    test_bound_analyzer(linear_combination_iterator<mpq> &it,
                            std::function<impq (unsigned) > &   lower_bounds,
                            std::function<impq (unsigned)>  & upper_bounds,
                            std::function<column_type (unsigned)> column_types,
                        vector<implied_bound> & evidence_vector,
                        unsigned row_or_term_index,
                        std::function<bool (unsigned, bool, mpq &, bool & strict)> & try_get_found_bound) :
    m_it(it),
    m_lower_bounds(lower_bounds),
    m_upper_bounds(upper_bounds),
    m_column_types(column_types),
    m_implied_bounds(evidence_vector),
    m_row_or_term_index(row_or_term_index),
    m_try_get_found_bound(try_get_found_bound)
    {
        m_it.reset();
        unsigned i;
        mpq a;
        while (m_it.next(a, i) ) {
            m_coeffs.push_back(a);
            m_index.push_back(i);
        }
    }

    static int sign (const mpq & t)  { return is_pos(t) ? 1: -1;}

    void analyze() {
        // We have the equality sum by j of row[j]*x[j] = m_rs
        // We try to pin a var by pushing the total of the partial sum down, denoting the variable of this process by _u.
        for (unsigned i = 0; i < m_index.size(); i++) {
            analyze_i(i);
        }
    }
    void analyze_i(unsigned i) {
        // set the m_coeff_is_pos
        m_coeff_sign = sign(m_coeffs[i]);
        analyze_i_for_lower(i);
        analyze_i_for_upper(i);
    }

    void analyze_i_for_upper(unsigned i) {
        mpq l;
        bool strict = false;
        lp_assert(is_zero(l));
        for (unsigned k = 0; k < m_index.size(); k++) {
            if (k == i)
                continue;
            mpq lb;
            bool str;
            if (!upper_bound_of_monoid(k, lb, str)) {
                return;
            }
            l += lb;
            if (str)
                strict = true;
        }
        l /= m_coeffs[i];
        unsigned j = m_index[i];
        switch(m_column_types(j)) {
        case column_type::fixed:
        case column_type::boxed:
        case column_type::upper_bound:
            {
                const auto & lb = m_upper_bounds(j);
                if (l > lb.x || (l == lb.x && !(is_zero(lb.y) && strict))) {
                    break; // no improvement on the existing upper bound
                }
            }
        default:
            m_implied_bounds.push_back(implied_bound(l, j, false, is_pos(m_coeffs[i]), m_row_or_term_index, strict));
        }
    }


    bool lower_bound_of_monoid(unsigned k, mpq & lb, bool &strict) const {
        int s = - m_coeff_sign * sign(m_coeffs[k]);
        unsigned j = m_index[k];
        if (s > 0) {
            switch(m_column_types(j)) {
            case column_type::fixed:
            case column_type::boxed:
            case column_type::lower_bound:
                lb = -m_coeffs[k] * m_lower_bounds(j).x;
                strict = !is_zero(m_lower_bounds(j).y);
                return true;
            default:
                return false;
            }
        }

        switch(m_column_types(j)) {
        case column_type::fixed:
        case column_type::boxed:
        case column_type::upper_bound:
                lb = -m_coeffs[k] * m_upper_bounds(j).x;
                strict = !is_zero(m_upper_bounds(j).y);
                return true;
            default:
                return false;
        }
    }

    bool upper_bound_of_monoid(unsigned k, mpq & lb, bool & strict) const {
        int s = - m_coeff_sign * sign(m_coeffs[k]);
        unsigned j = m_index[k];
        if (s > 0) {
            switch(m_column_types(j)) {
            case column_type::fixed:
            case column_type::boxed:
            case column_type::upper_bound:
                lb = -m_coeffs[k] * m_upper_bounds(j).x;
                strict = !is_zero(m_upper_bounds(j).y);

                return true;
            default:
                return false;
            }
        }

        switch(m_column_types(j)) {
        case column_type::fixed:
        case column_type::boxed:
        case column_type::lower_bound:
                lb = -m_coeffs[k] * m_lower_bounds(j).x;
                strict = !is_zero(m_lower_bounds(j).y);
                return true;
            default:
                return false;
        }
    }

    void analyze_i_for_lower(unsigned i) {
        mpq l;
        lp_assert(is_zero(l));
        bool strict = false;
        for (unsigned k = 0; k < m_index.size(); k++) {
            if (k == i)
                continue;
            mpq lb;
            bool str;
            if (!lower_bound_of_monoid(k, lb, str)) {
                return;
            }
            if (str)
                strict = true;
            l += lb;
        }
        l /= m_coeffs[i];
        unsigned j = m_index[i];
        switch(m_column_types(j)) {
        case column_type::fixed:
        case column_type::boxed:
        case column_type::lower_bound:
            {
                const auto & lb = m_lower_bounds(j);
                if (l < lb.x || (l == lb.x && !(is_zero(lb.y) && strict))) {
                    break; // no improvement on the existing upper bound
                }
            }
        default:
            m_implied_bounds.push_back(implied_bound(l, j, true, is_pos(m_coeffs[i]), m_row_or_term_index, strict));
        }
    }

    bool lower_bound_is_available(unsigned j) const {
        switch(m_column_types(j)) {
        case column_type::fixed:
        case column_type::boxed:
        case column_type::lower_bound:
            return true;
        default:
            return false;
        }
    }

    bool upper_bound_is_available(unsigned j) const {
        switch(m_column_types(j)) {
        case column_type::fixed:
        case column_type::boxed:
        case column_type::upper_bound:
            return true;
        default:
            return false;
        }
    }

    bool try_get_best_avail_bound(unsigned j, bool is_lower_bound, mpq & best_bound, bool & strict_of_best_bound) const {
        if (m_try_get_found_bound(j, is_lower_bound, best_bound, strict_of_best_bound)) {
            return true;
        }
        if (is_lower_bound) {
            if (lower_bound_is_available(j)) {
                best_bound = m_lower_bounds(j).x;
                strict_of_best_bound = !is_zero(m_lower_bounds(j).y);
                return true;
            }
        } else {
            if (upper_bound_is_available(j)) {
                best_bound = m_upper_bounds(j).x;
                strict_of_best_bound = !is_zero(m_lower_bounds(j).y);
                return true;
            }
        }
        return false;
    }

    bool bound_is_new(unsigned j, const mpq& b, bool is_lower_bound, bool strict) const {
        mpq best_bound;
        bool strict_of_best_bound;
        if (try_get_best_avail_bound(j, is_lower_bound, best_bound, strict_of_best_bound)) {
            if (is_lower_bound) {
                if (b > best_bound || ( b != best_bound && (strict && !strict_of_best_bound))) // the second clouse stands for strong inequality
                     return true; 
            } else {
                if (b < best_bound || ( b == best_bound  && (strict && !strict_of_best_bound)))
                    return true;
            }
            return false;
        }
        return true;
    }

};

}
#endif
