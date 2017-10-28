/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
#include "util/vector.h"
#include "util/lp/linear_combination_iterator.h"
#include "implied_bound.h"
#include <functional>
#include "util/lp/bound_propagator_int.h"
// We have an inequality : sum by j of row[j]*x[j] <= rs
// We try to pin a var by pushing the total by using the variable bounds
// In a loop we drive the partial sum down, denoting the variables of this process by _u.
// In the same loop trying to pin variables by pushing the partial sum up, denoting the variable related to it by _l
namespace lp {
template <typename T>
class bound_analyzer_on_int_ineq {
    linear_combination_iterator<T> & m_it;
    bound_propagator_int<T> & m_bp;
    unsigned           m_inequality_index;
    int                m_column_of_u; // index of an unlimited from above monoid
    // -1 means that such a value is not found, -2 means that at least two of such monoids were found
    int                m_column_of_l; // index of an unlimited from below monoid
    T               m_rs;

public :
    // constructor
    bound_analyzer_on_int_ineq(
        linear_combination_iterator<T> &it,
        const T& rs,
        unsigned ineq_index,
        bound_propagator_int<T> & bp
                          )
        :
        m_it(it),
        m_bp(bp),
        m_inequality_index(ineq_index),
        m_column_of_u(-1),
        m_column_of_l(-1),
        m_rs(rs)
    {
        TRACE("ba_int", bp.print_ineq(tout, ineq_index); tout << "\n";
              unsigned j;
              m_it.reset();
              while (m_it.next(j)) {
                  tout << "dom of " << bp.var_name(j) << " = ";
                  bp.print_var_domain(tout,j);
              }
              );
        
    }


    unsigned j;
    void analyze() {
        
        T a; unsigned j;
        m_it.reset();
        while (((m_column_of_l != -2) || (m_column_of_u != -2)) && m_it.next(a, j))
            analyze_bound_on_var_on_coeff(j, a);

        TRACE("ba_int", tout << "m_column_of_u = " << m_column_of_u << ", m_column_of_l = " <<
              m_column_of_l << '\n';);
        
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

    T ub(unsigned j) const {
        T b;
        bool r = m_bp.get_upper_bound(j, b);
        lp_assert(r);
        return b;
    }
    
    T lb(unsigned j) const {
        T b;
        bool r= m_bp.get_lower_bound(j, b);
        lp_assert(r);
        return b;
    }


    T monoid_max_no_mult(bool a_is_pos, unsigned j) const {
        if (a_is_pos) {
            return ub(j);
        }
        return lb(j);
    }
    T monoid_max(const T & a, unsigned j) const {
        if (is_pos(a)) {
            return a * ub(j);
        }
        return a * lb(j);
    }
    
    T monoid_min_no_mult(bool a_is_pos, unsigned j) const {
        if (!a_is_pos) {
            return ub(j);
        }
        return lb(j);
    }

    T monoid_min(const T & a, unsigned j) const {
        if (is_neg(a)) {
            return a * ub(j);
        }
        
        return a * lb(j);
    }
    

    void limit_all_monoids_from_above() {
        TRACE("ba_int",);
        T total = m_rs;
        m_it.reset();
        T a; unsigned j;
        while (m_it.next(a, j)) {
            total -= monoid_min(a, j);
        }
        TRACE("ba_int", tout << "total = " << total << '\n';);

        m_it.reset();
        while (m_it.next(a, j)) {
            bool a_is_pos = is_pos(a);
            T bound = total / a + monoid_min_no_mult(a_is_pos, j);
            if (a_is_pos) {
                limit_j(j, bound, false);
            }
            else {
                limit_j(j, bound, true);
            }
        }
    }

    void limit_all_monoids_from_below() {
        TRACE("ba_int",);

        T total = m_rs;
        m_it.reset();
        T a; unsigned j;
        while (m_it.next(a, j)) {
            total -= monoid_max(a, j);
        }
        m_it.reset();
        while (m_it.next(a, j)) {
            bool a_is_pos = is_pos(a);
            T bound = total / a + monoid_max_no_mult(a_is_pos, j);
            if (a_is_pos) {
                limit_j(j, bound, true);
            }
            else {
                limit_j(j, bound, false);
            }
        }
    }

    
    void limit_monoid_u_from_below() {
        // we are going to limit from below the monoid m_column_of_u,
        // every other monoid is impossible to limit from below
        T u_coeff, a;
        unsigned j;
        T bound = -m_rs;
        m_it.reset();
        while (m_it.next(a, j)) {
            if (j == static_cast<unsigned>(m_column_of_u)) {
                u_coeff = a;
                continue;
            }
            bound -= monoid_max(a, j);
        }

        bound /= u_coeff;
        
        if (numeric_traits<T>::is_pos(u_coeff)) {
            limit_j(m_column_of_u, bound, true);
        } else {
            limit_j(m_column_of_u, bound, false);
        }
    }


    void limit_monoid_l_from_above() {
        // we are going to limit from above the monoid m_column_of_l,
        // every other monoid is impossible to limit from above
        T l_coeff, a;
        unsigned j;
        T bound = m_rs;
        m_it.reset();
        while (m_it.next(a, j)) {
            if (j == static_cast<unsigned>(m_column_of_l)) {
                l_coeff = a;
                continue;
            }
            bound -= monoid_min(a, j);
        }
        bound /= l_coeff;
        if (is_pos(l_coeff)) {
            limit_j(m_column_of_l, bound, false);
        } else {
            limit_j(m_column_of_l, bound, true);
        }
    }
    
    // // it is the coefficent before the bounded column
    // void provide_evidence(bool coeff_is_pos) {
    //     /*
    //     auto & be = m_ibounds.back();
    //     bool lower_bound = be.m_lower_bound;
    //     if (!coeff_is_pos)
    //         lower_bound = !lower_bound;
    //     auto it = m_it.clone();
    //     T a; unsigned j;
    //     while (it->next(a, j)) {
    //         if (be.m_j == j) continue;
    //         lp_assert(bound_is_available(j, is_neg(a) ? lower_bound : !lower_bound));
    //         be.m_vector_of_bound_signatures.emplace_back(a, j, numeric_traits<T>::
    //                                                      is_neg(a)? lower_bound: !lower_bound);
    //     }
    //     delete it;
    //     */
    // }

    void limit_j(unsigned j, const T& u, bool is_lower_bound){
        TRACE("ba_int", tout<<  "j="<< m_bp.var_name(j) << ", u= "<< u << ", is_lower_bound = " << is_lower_bound<<"\n";);

        if (is_lower_bound)
            m_bp.add_bound(ceil(u), j, is_lower_bound, m_inequality_index);
        else
            m_bp.add_bound(floor(u), j, is_lower_bound, m_inequality_index);
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
    
    void analyze_bound_on_var_on_coeff(int j, const T &a) {
        if (!m_bp.has_upper_bound(j)) {
            if (is_pos(a))
                advance_u(j);
            else 
                advance_l(j);
        }
        if (!m_bp.has_lower_bound(j)) {
            if(is_neg(a))
                advance_u(j);
            else
                advance_l(j);
        }
    }

    static void analyze(linear_combination_iterator<T> &it,
                        const T& rs,
                        unsigned ineq_index,
                        bound_propagator_int<T> & bp
                        ) {
        TRACE("ba_int", tout << "ddd = " << ++lp_settings::ddd << std::endl;);
        bound_analyzer_on_int_ineq a(it, rs, ineq_index, bp);
        a.analyze();
    }

};
}
