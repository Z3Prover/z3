/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    dd_pdd.cpp

Abstract:

    Poly DD package 

Author:

    Nikolaj Bjorner (nbjorner) 2019-12-24
    Lev Nachmanson (levnach) 2019-12-24

Revision History:

--*/
#include "math/dd/dd_pdd.h"
#include "math/interval/dep_intervals.h"

namespace dd {
typedef dep_intervals::interval interval;
typedef dep_intervals::with_deps_t w_dep;
// calculates the interval of a pdd expression based on the given intervals of the variables
class pdd_interval {
    dep_intervals m_dep_intervals;
    std::function<interval (unsigned, bool)> m_var2interval;
    
public:
    
    pdd_interval(reslimit& lim): m_dep_intervals(lim) {}

    dep_intervals& m() { return m_dep_intervals; }

    std::function<interval (unsigned, bool)>& var2interval() { return m_var2interval; } // setter
    const std::function<interval (unsigned, bool)>& var2interval() const { return m_var2interval; } // getter

    template <w_dep wd>
    void get_interval(pdd const& p, scoped_dep_interval& ret) {
        if (p.is_val()) {
            m_dep_intervals.set_interval_for_scalar(ret.get(), p.val());
            return;
        }
        bool deps = wd == w_dep::with_deps;
        interval a = m_var2interval(p.var(), deps);
        scoped_dep_interval hi(m()), lo(m()), t(m());
        get_interval<wd>(p.hi(), hi);
        get_interval<wd>(p.lo(), lo);
        if (deps) {
            interval_deps_combine_rule combine_rule;
            m_dep_intervals.mul(hi, a, t, combine_rule);
            m_dep_intervals.combine_deps(hi, a, combine_rule, t); 
            combine_rule.reset();
            m_dep_intervals.add(t, lo, ret, combine_rule);
            m_dep_intervals.combine_deps(t, lo, combine_rule, ret);
        } else {
            m_dep_intervals.mul(hi, a, t);
            m_dep_intervals.add(t, lo, ret);
        }
    }
	// f meant to be called when the separation happens
    template <typename T>
    bool separated_from_zero(pdd const& p, u_dependency*& dep, std::function<void (const T)>& f) {
        return m_dep_intervals.check_interval_for_conflict_on_zero(get_interval<w_dep::with_deps>(p), dep, f);
    }

};
}
