/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pb_rewriter_def.h

Abstract:

    Basic rewriting rules for PB constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2013-14-12

Notes:

--*/
#ifndef _PB_REWRITER_DEF_H_
#define _PB_REWRITER_DEF_H_

#include"pb_rewriter.h"


template<typename PBU>
void pb_rewriter_util<PBU>::display(std::ostream& out, typename PBU::args_t& args, typename PBU::numeral& k, bool is_eq) {
    for (unsigned i = 0; i < args.size(); ++i) {
        out << args[i].second << " * ";
        m_util.display(out, args[i].first);
        out << " ";
        if (i+1 < args.size()) out << "+ ";
    }
    out << (is_eq?" = ":" >= ") << k << "\n";
}

template<typename PBU>
void pb_rewriter_util<PBU>::unique(typename PBU::args_t& args, typename PBU::numeral& k, bool is_eq) {
    
    TRACE("pb_verbose", display(tout << "pre-unique:", args, k, is_eq););
    for (unsigned i = 0; i < args.size(); ++i) {
        if (m_util.is_negated(args[i].first)) {
            args[i].first = m_util.negate(args[i].first);
            k -= args[i].second;
            args[i].second = -args[i].second;
        }
    }
    // remove constants
    for (unsigned i = 0; i < args.size(); ++i) {
        if (m_util.is_true(args[i].first)) {
            k -= args[i].second;
            std::swap(args[i], args[args.size()-1]);
            args.pop_back();
            --i;
        }
        else if (m_util.is_false(args[i].first)) {
            std::swap(args[i], args[args.size()-1]);
            args.pop_back();                
            --i;
        }
    }
    // sort and coalesce arguments:
    typename PBU::compare cmp;
    std::sort(args.begin(), args.end(), cmp);

    // coallesce
    unsigned i, j;
    for (i = 0, j = 1; j < args.size(); ++j) {
        if (args[i].first == args[j].first) {
            args[i].second += args[j].second;
        }
        else {
            ++i;
            args[i] = args[j];
        }
    }
    args.resize(i+1);

    // remove 0s.
    for (i = 0, j = 0; j < args.size(); ++j) {
        if (!args[j].second.is_zero()) {
            if (i != j) {
                args[i] = args[j];
            }
            ++i;
        }
    }
    args.resize(i);
    TRACE("pb_verbose", display(tout << "post-unique:", args, k, is_eq););
}

template<typename PBU>
lbool pb_rewriter_util<PBU>::normalize(typename PBU::args_t& args, typename PBU::numeral& k, bool is_eq) {
    TRACE("pb_verbose", display(tout << "pre-normalize:", args, k, is_eq););

    DEBUG_CODE(
        bool found = false;
        for (unsigned i = 0; !found && i < args.size(); ++i) {
            found = args[i].second.is_zero();
        }
        if (found) display(verbose_stream(), args, k, is_eq);
        SASSERT(!found););

    // 
    // Ensure all coefficients are positive:
    //    c*l + y >= k 
    // <=> 
    //    c*(1-~l) + y >= k
    // <=>
    //    c - c*~l + y >= k
    // <=> 
    //    -c*~l + y >= k - c
    // 
    typename PBU::numeral sum(0);
    for (unsigned i = 0; i < args.size(); ++i) {
        typename PBU::numeral c = args[i].second;
        if (c.is_neg()) {
            args[i].second = -c;
            args[i].first = m_util.negate(args[i].first);
            k -= c;
        }
        sum += args[i].second;
    }
    // detect tautologies:
    if (!is_eq && k <= PBU::numeral::zero()) {
        args.reset();
        k = PBU::numeral::zero();
        return l_true;
    }
    if (is_eq && k.is_zero() && args.empty()) {
        return l_true;
    }

    // detect infeasible constraints:
    if (sum < k) {
        args.reset();
        k = PBU::numeral::one();
        return l_false;
    }

    if (is_eq && k == sum) {
        for (unsigned i = 0; i < args.size(); ++i) {
            args[i].second = PBU::numeral::one();
        }
        typename PBU::numeral num(args.size()); 
        k = num;
        return l_undef;
    }
    
    bool all_int = true;
    for (unsigned i = 0; all_int && i < args.size(); ++i) {
        all_int = args[i].second.is_int();
    }
    
    if (!all_int) {
        // normalize to integers.
        typename PBU::numeral d(denominator(k));
        for (unsigned i = 0; i < args.size(); ++i) {
            d = lcm(d, denominator(args[i].second));
        }
        SASSERT(!d.is_one());
        k *= d;
        for (unsigned i = 0; i < args.size(); ++i) {
            args[i].second *= d;
        }            
    }

    if (is_eq) {
        TRACE("pb_verbose", display(tout << "post-normalize:", args, k, is_eq););
        return l_undef;
    }
    
    // Ensure the largest coefficient is not larger than k:
    sum = PBU::numeral::zero();
    for (unsigned i = 0; i < args.size(); ++i) {
        typename PBU::numeral c = args[i].second;
        if (c > k) {
            args[i].second = k;
        }
        sum += args[i].second;
    }
    SASSERT(!args.empty());
    
    // normalize tight inequalities to unit coefficients.
    if (sum == k) {
        for (unsigned i = 0; i < args.size(); ++i) {
            args[i].second = PBU::numeral::one();
        }
        typename PBU::numeral num(args.size()); 
        k = num;
    }
    
    // apply cutting plane reduction:
    typename PBU::numeral g(0);
    for (unsigned i = 0; !g.is_one() && i < args.size(); ++i) {
        typename PBU::numeral c = args[i].second;
        if (c != k) {
            if (g.is_zero()) {
                g = c;
            }
            else {
                g = gcd(g, c);
            }
        }
    }
    if (g.is_zero()) {
        // all coefficients are equal to k.
        for (unsigned i = 0; i < args.size(); ++i) {
            SASSERT(args[i].second == k);
            args[i].second = PBU::numeral::one();
        }
        k = PBU::numeral::one();
    }
    else if (g > PBU::numeral::one()) {
        
        //
        // Example 5x + 5y + 2z + 2u >= 5
        // becomes 3x + 3y + z + u >= 3
        // 
        typename PBU::numeral k_new = div(k, g);    
        if (!(k % g).is_zero()) {     // k_new is the ceiling of k / g.
            k_new++;
        }
        for (unsigned i = 0; i < args.size(); ++i) {
            SASSERT(args[i].second.is_pos());
            typename PBU::numeral c = args[i].second;
            if (c == k) {
                c = k_new;
            }
            else {
                c = div(c, g);
            }
            args[i].second = c;
            SASSERT(args[i].second.is_pos());
        }
        k = k_new;            
    }
    //
    // normalize coefficients that fall within a range
    // k/n <= ... < k/(n-1) for some n = 1,2,...
    //
    // e.g, k/n <= min <= max < k/(n-1)
    //      k/min <= n, n-1 < k/max
    // .    floor(k/max) = ceil(k/min) - 1  
    // .    floor(k/max) < k/max
    //
    // example: k = 5, min = 3, max = 4: 5/3 -> 2   5/4 -> 1, n = 2
    // replace all coefficients by 1, and k by 2.
    //
    if (!k.is_one()) {
        typename PBU::numeral min = args[0].second, max = args[0].second;
        for (unsigned i = 1; i < args.size(); ++i) {
            if (args[i].second < min) min = args[i].second;
            if (args[i].second > max) max = args[i].second;
        }            
        SASSERT(min.is_pos());
        typename PBU::numeral n0 = k/max;
        typename PBU::numeral n1 = floor(n0);
        typename PBU::numeral n2 = ceil(k/min) - PBU::numeral::one();
        if (n1 == n2 && !n0.is_int()) {
            IF_VERBOSE(3, display(verbose_stream() << "set cardinality\n", args, k, is_eq););
            
            for (unsigned i = 0; i < args.size(); ++i) {
                args[i].second = PBU::numeral::one();
            }
            k = n1 + PBU::numeral::one();
        }
    }
    TRACE("pb_verbose", display(tout << "post-normalize:", args, k, is_eq););
    return l_undef;
}

template<typename PBU>
void pb_rewriter_util<PBU>::prune(typename PBU::args_t& args, typename PBU::numeral& k, bool is_eq) {
    if (is_eq) {
        return;
    }
    typename PBU::numeral nlt(0);
    unsigned occ = 0;
    for (unsigned i = 0; nlt < k && i < args.size(); ++i) {
        if (args[i].second < k) {
            nlt += args[i].second;
            ++occ;
        }
    }
    if (0 < occ && nlt < k) {        
        for (unsigned i = 0; i < args.size(); ++i) {
            if (args[i].second < k) {
                args[i] = args.back();
                args.pop_back();
                --i;
            }
        }
        unique(args, k, is_eq);
        normalize(args, k, is_eq);
    }    
}

#endif
