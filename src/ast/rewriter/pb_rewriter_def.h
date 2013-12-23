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
void pb_rewriter_util<PBU>::display(std::ostream& out, typename PBU::args_t& args, typename PBU::numeral& k) {
    for (unsigned i = 0; i < args.size(); ++i) {
        out << args[i].second << " * ";
        m_util.display(out, args[i].first);
        out << " ";
        if (i+1 < args.size()) out << "+ ";
    }
    out << " >= " << k << "\n";
}

template<typename PBU>
void pb_rewriter_util<PBU>::unique(typename PBU::args_t& args, typename PBU::numeral& k) {
    
    TRACE("pb", display(tout << "pre-unique:", args, k););
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
    PBU::compare cmp;
    std::sort(args.begin(), args.end(), cmp);
    
    unsigned i = 0, j = 1;
    for (; j < args.size(); ++i) {
        SASSERT(j > i);
        for (; j < args.size() && args[j].first == args[i].first; ++j) {
            args[i].second += args[j].second;
        }
        if (args[i].second.is_zero()) {
            --i;
        }
        if (j < args.size()) {
            args[i+1].first = args[j].first;
            args[i+1].second = args[j].second;
            ++j;
        }
    }
    if (i + 1 < args.size()) {
        args.resize(i+1);
    }
    TRACE("pb", display(tout << "post-unique:", args, k););
}

template<typename PBU>
lbool pb_rewriter_util<PBU>::normalize(typename PBU::args_t& args, typename PBU::numeral& k) {
    TRACE("pb", display(tout << "pre-normalize:", args, k););

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
    PBU::numeral sum(0);
    for (unsigned i = 0; i < args.size(); ++i) {
        PBU::numeral c = args[i].second;
        if (c.is_neg()) {
            args[i].second = -c;
            args[i].first = m_util.negate(args[i].first);
            k -= c;
        }
        sum += args[i].second;
    }
    // detect tautologies:
    if (k <= PBU::numeral::zero()) {
        args.reset();
        k = PBU::numeral::zero();
        return l_true;
    }
    // detect infeasible constraints:
    if (sum < k) {
        args.reset();
        k = PBU::numeral::one();
        return l_false;
    }
    
    bool all_int = true;
    for (unsigned i = 0; all_int && i < args.size(); ++i) {
        all_int = args[i].second.is_int();
    }
    
    if (!all_int) {
        // normalize to integers.
        PBU::numeral d(denominator(k));
        for (unsigned i = 0; i < args.size(); ++i) {
            d = lcm(d, denominator(args[i].second));
        }
        SASSERT(!d.is_one());
        k *= d;
        for (unsigned i = 0; i < args.size(); ++i) {
            args[i].second *= d;
        }            
    }
    
    // Ensure the largest coefficient is not larger than k:
    sum = PBU::numeral::zero();
    for (unsigned i = 0; i < args.size(); ++i) {
        PBU::numeral c = args[i].second;
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
        k = PBU::numeral(args.size());
    }
    
    // apply cutting plane reduction:
    PBU::numeral g(0);
    for (unsigned i = 0; !g.is_one() && i < args.size(); ++i) {
        PBU::numeral c = args[i].second;
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
        IF_VERBOSE(3, verbose_stream() << "cut " << g << "\n";
                   display(verbose_stream(), args, k);
                   );
        
        //
        // Example 5x + 5y + 2z + 2u >= 5
        // becomes 3x + 3y + z + u >= 3
        // 
        PBU::numeral k_new = div(k, g);    
        if (!(k % g).is_zero()) {     // k_new is the ceiling of k / g.
            k_new++;
        }
        for (unsigned i = 0; i < args.size(); ++i) {
            SASSERT(args[i].second.is_pos());
            PBU::numeral c = args[i].second;
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
        PBU::numeral min = args[0].second, max = args[0].second;
        for (unsigned i = 1; i < args.size(); ++i) {
            if (args[i].second < min) min = args[i].second;
            if (args[i].second > max) max = args[i].second;
        }            
        PBU::numeral n0 = k/max;
        PBU::numeral n1 = floor(n0);
        PBU::numeral n2 = ceil(k/min) - PBU::numeral::one();
        if (n1 == n2 && !n0.is_int()) {
            IF_VERBOSE(3, display(verbose_stream() << "set cardinality\n", args, k););
            
            for (unsigned i = 0; i < args.size(); ++i) {
                args[i].second = PBU::numeral::one();
            }
            k = n1 + PBU::numeral::one();
        }
    }
    return l_undef;
}


template<typename PBU>
void pb_rewriter_util<PBU>::prune(typename PBU::args_t& args, typename PBU::numeral& k) {

    PBU::numeral nlt(0);
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
        normalize(args, k);
    }    
}

#endif
