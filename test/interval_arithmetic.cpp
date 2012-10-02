/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    interval_arithmetic.cpp

Abstract:

    Test interval arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2006-12-05.

Revision History:

--*/
#include<iostream>
#include"interval_arithmetic.h"
#include"trace.h"


template<class number, class epsilon>
void tst_ext_number() {
    typedef ext_number<number, epsilon> num;
    num zero;
    num one(1);
    num eps(num::epsilon());
    num m_eps(num::epsilon().neg());
    num two(number(2));
    num half(number(1,2));
    num inf = num::infinity();
    num eps1 = num::epsilon();
    num three(number(3));
    num three_e = num::plus(three, num::epsilon());
    SASSERT(zero.get_sign() == num::ZERO);
    SASSERT(one.get_sign() == num::POSITIVE);
    SASSERT(m_eps.get_sign() == num::NEGATIVE);
    SASSERT(inf.get_sign() == num::POSITIVE);
    SASSERT(zero.is_zero());
    SASSERT(!one.is_zero());
    SASSERT(!inf.is_zero());
    SASSERT(inf.is_infinite());
    SASSERT(!one.is_infinite());
    SASSERT(one.is_pos());
    SASSERT(m_eps.is_neg());
    SASSERT(one != zero);
    SASSERT(inf != one);
    SASSERT(inf != zero);
    SASSERT(zero == zero);
    SASSERT(zero < one);
    SASSERT(eps < two);
    SASSERT(zero < eps);
    SASSERT(zero < inf);
    SASSERT(zero == min(zero, eps));
    SASSERT(zero == min(zero, inf));
    SASSERT(eps == max(zero, eps));
    SASSERT(inf == max(zero, inf));
    SASSERT(min(zero,eps) == min(eps,zero));
    SASSERT(num::plus(zero, eps) == eps);
    SASSERT(num::plus(zero, one) == one);
    SASSERT(num::plus(zero, inf) == inf);
    SASSERT(num::plus(inf, inf) == inf);
    SASSERT(inf.neg() < inf);
    SASSERT(inf.neg() < zero);
    SASSERT(num::minus(zero, one) == one.neg());
    SASSERT(num::minus(zero, eps) == eps.neg());
    SASSERT(num::minus(zero, inf) == inf.neg());
    SASSERT(num::minus(zero, inf.neg()) == inf);
    SASSERT(num::minus(inf, inf.neg()) == inf);

    // sup_mult, inf_mult
    SASSERT(sup_mult(zero, one) == zero);
    SASSERT(sup_mult(one, one) == one);
    SASSERT(sup_mult(one, one.neg()) == one.neg());
    SASSERT(inf_mult(zero, one) == zero);
    SASSERT(inf_mult(one, one) == one);
    SASSERT(inf_mult(one, one.neg()) == one.neg());

    // sup_div, inf_div 
    SASSERT(one < sup_div(three_e, three));
    SASSERT(inf_div(three, three_e) < one);
    SASSERT(inf_div(three_e, three) < two);
    SASSERT(inf_div(three.neg(), three_e.neg()) < one);
    SASSERT(one < sup_div(three_e.neg(), three.neg()));
    SASSERT(inf_div(three_e.neg(), three.neg()) < two);

    // sup_power, inf_power
    SASSERT(sup_power(one,3) == one);
    SASSERT(sup_power(one,3) > zero);
    SASSERT(sup_power(num::plus(one, num::epsilon()),3) > one);

    SASSERT(sup_power(one,2) == one);
    SASSERT(sup_power(one,2) > zero);
    SASSERT(sup_power(num::plus(one, num::epsilon()),2) > one);

    // sup_root, inf_root    
    SASSERT(sup_root(one,2) >= zero);
    SASSERT(inf_root(one,2) <= one);
    SASSERT(sup_root(zero,2) >= zero);
    SASSERT(inf_root(zero,2) <= zero);

}

template<class number, class epsilon>
void tst_interval()
{
    typedef interval<number, epsilon> interval;
    typedef ext_number<number, epsilon> ext_num;
    ext_num m_inf(ext_num::infinity().neg());
    ext_num m_three(ext_num(3).neg());
    ext_num m_three_m_e(ext_num::plus(ext_num(3), ext_num::epsilon()).neg());
    ext_num m_three_p_e(ext_num::plus(ext_num(3), ext_num::epsilon().neg()).neg()); 
    ext_num m_eps(ext_num::epsilon().neg());
    ext_num zero(0);
    ext_num eps(ext_num::epsilon());
    ext_num three(ext_num(3));
    ext_num three_m_e(ext_num::minus(ext_num(3), ext_num::epsilon())); 
    ext_num three_p_e(ext_num::plus(ext_num(3), ext_num::epsilon())); 
    ext_num inf(ext_num::infinity());
    ext_num nums[] = { m_inf, m_three_m_e, m_three, m_three_p_e, m_eps, zero, eps, three_m_e, three, three_p_e, inf };

    unsigned n_nums = 11;
    //
    // add_lower
    // add_upper
    //
    for (unsigned i = 0; i < n_nums; ++i) {
        for (unsigned j = i+1; j < n_nums; ++j) {

            for (unsigned k = 0; k < n_nums; ++k) {
                interval i1(nums[i], nums[j]);
                bool ok = i1.add_lower(nums[k]);
                TRACE("interval_arithmetic", tout << "lower: " << ok << " " 
                      << nums[k] << " " << i1 << std::endl;);
            }

            for (unsigned k = 0; k < n_nums; ++k) {
                interval i1(nums[i], nums[j]);
                bool ok = i1.add_upper(nums[k]);
                TRACE("interval_arithmetic", tout << "upper: " << ok << " " 
                      << nums[k] << " " << i1 << std::endl;);
            }
        }
    }

    //
    // +
    // *
    // -
    // quotient
    //
    for (unsigned i = 0; i < n_nums; ++i) {
        for (unsigned j = i+1; j < n_nums; ++j) {
            interval i1(nums[i],nums[j]);
            
            interval x = i1.power(0);
            interval y = i1.power(1);
            interval z = i1.power(2);
            interval x1 = i1.power(3);

            for (unsigned k = 0; k < n_nums; ++k) {
                for (unsigned l = k+1; l < n_nums; ++l) {
                    interval i2(nums[k],nums[l]);
                    interval i3 = i1 + i2;
                    interval i4 = i1 - i2;
                    interval i5 = i1 * i2;
                    TRACE("interval_arithmetic", tout << i1 << " + " << i2 << " = " << i3 << std::endl;);
                    TRACE("interval_arithmetic", tout << i1 << " - " << i2 << " = " << i4 << std::endl;);
                    TRACE("interval_arithmetic", tout << i1 << " * " << i2 << " = " << i5 << std::endl;);
                    SASSERT(i5 == i2 * i1);
                    vector<interval, true> intervals;
                    interval::quotient(i1, i2, intervals);
                    TRACE("interval_arithmetic", 
                          tout << i1 << " / " << i2 << " = " ;
                          for (unsigned idx = 0; idx < intervals.size(); ++idx) {
                              tout << intervals[idx] << " ";
                          }
                          tout << std::endl;
                          );

                    unsigned changed_bounds;
                    x = i1;
                    y = i2;
                    z = i3;
                    TRACE("interval_arithmetic", tout << "check: " << i1 << "=" << i2 << "*" << i3 << std::endl;);
                    if (interval::check_mult(x, y, z, changed_bounds)) {
                        TRACE("interval_arithmetic", tout << x << "=" << y << "*" << z << std::endl;);
                        SASSERT (!!(changed_bounds & 0x1) == (x.low() != i1.low()));
                        SASSERT (!!(changed_bounds & 0x2) == (x.high() != i1.high()));
                        SASSERT (!!(changed_bounds & 0x4) == (y.low() != i2.low()));
                        SASSERT (!!(changed_bounds & 0x8) == (y.high() != i2.high()));
                        SASSERT (!!(changed_bounds & 0x10) == (z.low() != i3.low()));
                        SASSERT (!!(changed_bounds & 0x20) == (z.high() != i3.high()));                            
                    }
                    else {
                        TRACE("interval_arithmetic", tout << "unsat" << std::endl;);
                    }

                    x = i1;
                    y = i2;
                    if (interval::check_power(x, y, 3, changed_bounds)) {
                        TRACE("interval_arithmetic", 
                              tout << "check: " << i1 << "=" << i2 << "^3" << " -> " 
                              << x << " = " << y << "^3" << std::endl;);
                    }
                    else {
                        TRACE("interval_arithmetic", tout << "unsat: " << i1 << "=" << i2 << "^4" << std::endl;);
                    }


                    x = i1;
                    y = i2;
					if (interval::check_power(x, y, 4, changed_bounds)) {
                        TRACE("interval_arithmetic", 
                              tout << "check: " << i1 << "=" << i2 << "^4" << " -> " 
                              << x << " = " << y << "^4" << std::endl;);
                    }
                    else {
                        TRACE("interval_arithmetic", tout << "unsat: " << i1 << "=" << i2 << "^4" << std::endl;);
                    }
                }
            }
        }
    }


    // check_mult(i1, i2, i3, change_bounds);

    // check_power(i1, i2, power, changed_bounds);
}

struct eps1 { rational operator()() { return rational(1); } };
struct eps0 { inf_rational operator()() { return inf_rational(rational(0),true); } };

void tst_interval_arithmetic() {
    TRACE("interval_arithmetic", tout << "starting interval_arithmetic test...\n";);
    tst_ext_number<rational, eps1>();
    tst_ext_number<inf_rational, eps0>();
    tst_interval<rational, eps1>();
    tst_interval<inf_rational, eps0>();
}
