/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    set of viable values as wrap-around interval

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

    
--*/
#pragma once


#include "math/polysat/viable_set.h"
#include "math/interval/mod_interval_def.h"

namespace polysat {

      dd::find_t viable_set::find_hint(rational const& d, rational& val) const {
        if (is_empty())
            return dd::find_t::empty;         
        if (contains(d))
            val = d;
        else 
            val = lo;
        if (lo + 1 == hi || hi == 0 && is_max(lo))
            return dd::find_t::singleton;            
        return dd::find_t::multiple;
    }

    bool viable_set::is_max(rational const& a) const {
        return a + 1 == rational::power_of_two(m_num_bits);
    }
    
    void viable_set::intersect_eq(rational const& a, bool is_positive) {
        if (is_positive) 
            intersect_fixed(a);        
        else 
            intersect_diff(a);        
    }

    bool viable_set::intersect_eq(rational const& a, rational const& b, bool is_positive) {
        if (!a.is_odd()) {
            std::function<bool(rational const&)> eval = [&](rational const& x) {
                return is_positive == (mod(a * x + b, p2()) == 0);
            };       
            return narrow(eval);            
        }
        if (b == 0)
            intersect_eq(b, is_positive);
        else {
            rational a_inv;
            VERIFY(a.mult_inverse(m_num_bits, a_inv));
            intersect_eq(mod(a_inv * -b, p2()), is_positive);
        }
        return true;
    }

    bool viable_set::intersect_le(rational const& a, rational const& b, rational const& c, rational const& d, bool is_positive) {
        // x <= 0
        if (a.is_odd() && b == 0 && c == 0 && d == 0)
            intersect_eq(b, is_positive);
        else if (a == 1 && b == 0 && c == 0) {
            // x <= d or x > d
            if (is_positive)
                intersect_ule(d);
            else 
                intersect_ugt(d);
        }
        else if (a == 0 && c == 1 && d == 0) {
            // x >= b or x < b
            if (is_positive)
                intersect_uge(b);
            else
                intersect_ult(b);
        }
        // TBD: can also handle wrap-around semantics (for signed comparison)
        else {
            std::function<bool(rational const&)> eval = [&](rational const& x) {
                return is_positive == mod(a * x + b, p2()) <= mod(c * x + d, p2());
            };       
            return narrow(eval);
        }
        return true;
    }

    rational viable_set::prev(rational const& p) const {
        if (p > 0)
            return p - 1;
        else
            return rational::power_of_two(m_num_bits) - 1;
    }

    rational viable_set::next(rational const& p) const {
        if (is_max(p))
	    return rational(0);
        else
            return p + 1;
    }

    bool viable_set::narrow(std::function<bool(rational const&)>& eval) {
        unsigned budget = 10;
        while (budget > 0 && !is_empty() && !eval(lo)) {
            --budget;
            intersect_diff(lo);
        }
        while (budget > 0 && !is_empty() && !eval(prev(hi))) {
            --budget;
            intersect_diff(prev(hi));
        }
        return 0 < budget;
    }


}


