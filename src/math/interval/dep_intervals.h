/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

    dep_intervals.h

  Abstract:

    intervals with depedency tracking.

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:

   extracted from nla_intervals.h

  --*/

#pragma once
#include "util/dependency.h"
#include "util/region.h"
#include "util/rational.h"
#include "util/rlimit.h"
#include "math/interval/interval.h"

class dep_intervals {
public:
    enum with_deps_t { with_deps, without_deps };

private:
    class im_config {
        unsynch_mpq_manager& m_manager;
        u_dependency_manager& m_dep_manager;

    public:
        typedef unsynch_mpq_manager numeral_manager;

        struct interval {
            interval() :
                m_lower(), m_upper(),
                m_lower_open(1), m_upper_open(1),
                m_lower_inf(1), m_upper_inf(1),
                m_lower_dep(nullptr), m_upper_dep(nullptr) {}
            mpq   m_lower;
            mpq   m_upper;
            unsigned  m_lower_open : 1;
            unsigned  m_upper_open : 1;
            unsigned  m_lower_inf : 1;
            unsigned  m_upper_inf : 1;
            u_dependency* m_lower_dep; // justification for the lower bound
            u_dependency* m_upper_dep; // justification for the upper bound
        };

        void add_deps(interval const& a, interval const& b, interval_deps_combine_rule const& deps, interval& i) const {
            i.m_lower_dep = lower_is_inf(i) ? nullptr : mk_dependency(a, b, deps.m_lower_combine);
            i.m_upper_dep = upper_is_inf(i) ? nullptr : mk_dependency(a, b, deps.m_upper_combine);
        }

        void add_deps(interval const& a, interval_deps_combine_rule const& deps, interval& i) const {
            i.m_lower_dep = lower_is_inf(i) ? nullptr : mk_dependency(a, deps.m_lower_combine);
            i.m_upper_dep = upper_is_inf(i) ? nullptr : mk_dependency(a, deps.m_upper_combine);
        }


        // Should be NOOPs for precise mpq types.
        // For imprecise types (e.g., floats) it should set the rounding mode.
        void round_to_minus_inf() {}
        void round_to_plus_inf() {}
        void set_rounding(bool to_plus_inf) {}

        // Getters
        mpq const& lower(interval const& a) const { return a.m_lower; }
        mpq const& upper(interval const& a) const { return a.m_upper; }
        mpq& lower(interval& a) { return a.m_lower; }
        mpq& upper(interval& a) { return a.m_upper; }
        bool lower_is_open(interval const& a) const { return a.m_lower_open; }
        bool upper_is_open(interval const& a) const { return a.m_upper_open; }
        bool lower_is_inf(interval const& a) const { return a.m_lower_inf; }
        bool upper_is_inf(interval const& a) const { return a.m_upper_inf; }
        bool is_inf(interval const& a) const { return upper_is_inf(a) && lower_is_inf(a); }
        bool is_zero(interval const& a) const {
            return (!lower_is_inf(a)) && (!upper_is_inf(a)) &&
                (!lower_is_open(a)) && (!upper_is_open(a)) &&
                unsynch_mpq_manager::is_zero(a.m_lower) &&
                unsynch_mpq_manager::is_zero(a.m_upper);
        }

        // Setters
        void set_lower(interval& a, mpq const& n) const { m_manager.set(a.m_lower, n); }
        void set_upper(interval& a, mpq const& n) const { m_manager.set(a.m_upper, n); }
        void set_lower(interval& a, rational const& n) const { set_lower(a, n.to_mpq()); }
        void set_upper(interval& a, rational const& n) const { set_upper(a, n.to_mpq()); }
        void set_lower_is_open(interval& a, bool v) const { a.m_lower_open = v; }
        void set_upper_is_open(interval& a, bool v) const { a.m_upper_open = v; }
        void set_lower_is_inf(interval& a, bool v) const { a.m_lower_inf = v; }
        void set_upper_is_inf(interval& a, bool v) const { a.m_upper_inf = v; }

        // Reference to numeral manager
        numeral_manager& m() const { return m_manager; }

        im_config(numeral_manager& m, u_dependency_manager& d) :m_manager(m), m_dep_manager(d) {}
    private:
        u_dependency* mk_dependency(interval const& a, interval const& b, deps_combine_rule bd) const {
            u_dependency* dep = nullptr;
            if (dep_in_lower1(bd)) {
                dep = m_dep_manager.mk_join(dep, a.m_lower_dep);
            }
            if (dep_in_lower2(bd)) {
                dep = m_dep_manager.mk_join(dep, b.m_lower_dep);
            }
            if (dep_in_upper1(bd)) {
                dep = m_dep_manager.mk_join(dep, a.m_upper_dep);
            }
            if (dep_in_upper2(bd)) {
                dep = m_dep_manager.mk_join(dep, b.m_upper_dep);
            }
            return dep;
        }

        u_dependency* mk_dependency(interval const& a, deps_combine_rule bd) const {
            u_dependency* dep = nullptr;
            if (dep_in_lower1(bd)) {
                dep = m_dep_manager.mk_join(dep, a.m_lower_dep);
            }
            if (dep_in_upper1(bd)) {
                dep = m_dep_manager.mk_join(dep, a.m_upper_dep);
            }
            return dep;
        }
    };

public:
    mutable unsynch_mpq_manager         m_num_manager;
    mutable u_dependency_manager        m_dep_manager;
    im_config                           m_config;
    mutable interval_manager<im_config> m_imanager;

    typedef interval_manager<im_config>::interval interval;

    unsynch_mpq_manager& num_manager() { return m_num_manager; }
    const unsynch_mpq_manager& num_manager() const { return m_num_manager; }
    
    u_dependency* mk_leaf(unsigned d) { return m_dep_manager.mk_leaf(d); }
    u_dependency* mk_join(u_dependency* a, u_dependency* b) { return m_dep_manager.mk_join(a, b); }

    template <enum with_deps_t wd>
    void mul(const rational& r, const interval& a, interval& b) const {
        if (r.is_zero()) return;
        m_imanager.mul(r.to_mpq(), a, b);
        if (wd == with_deps) {
            if (r.is_pos()) {
                b.m_lower_dep = a.m_lower_dep;
                b.m_upper_dep = a.m_upper_dep;
            }
            else {
                b.m_upper_dep = a.m_lower_dep;
                b.m_lower_dep = a.m_upper_dep;
            }
        }
    }

    void mul(const interval& a, const interval& b, interval& c, interval_deps_combine_rule& deps) { m_imanager.mul(a, b, c, deps); }
    void add(const interval& a, const interval& b, interval& c, interval_deps_combine_rule& deps) { m_imanager.add(a, b, c, deps); }
    
    void combine_deps(interval const& a, interval const& b, interval_deps_combine_rule const& deps, interval& i) const {
        SASSERT(&a != &i && &b != &i);
        m_config.add_deps(a, b, deps, i);
    }

    void combine_deps(interval const& a, interval_deps_combine_rule const& deps, interval& i) const {
        SASSERT(&a != &i);
        m_config.add_deps(a, deps, i);
    }

public:
    u_dependency_manager& dep_manager() { return m_dep_manager; }

    dep_intervals(reslimit& lim) :
        m_config(m_num_manager, m_dep_manager),
        m_imanager(lim, im_config(m_num_manager, m_dep_manager))
    {}

    std::ostream& display(std::ostream& out, const interval& i) const;
    void set_lower(interval& a, rational const& n) const { m_config.set_lower(a, n.to_mpq()); }
    void set_upper(interval& a, rational const& n) const { m_config.set_upper(a, n.to_mpq()); }
    void set_lower_is_open(interval& a, bool strict) { m_config.set_lower_is_open(a, strict); }
    void set_lower_is_inf(interval& a, bool inf) { m_config.set_lower_is_inf(a, inf); }
    void set_upper_is_open(interval& a, bool strict) { m_config.set_upper_is_open(a, strict); }
    void set_upper_is_inf(interval& a, bool inf) { m_config.set_upper_is_inf(a, inf); }
    bool is_zero(const interval& a) const { return m_config.is_zero(a); }
    bool upper_is_inf(const interval& a) const { return m_config.upper_is_inf(a); }
    bool lower_is_inf(const interval& a) const { return m_config.lower_is_inf(a); }
    bool lower_is_open(const interval& a) const { return m_config.lower_is_open(a); }
    bool upper_is_open(const interval& a) const { return m_config.upper_is_open(a); }
    void add(const rational& r, interval& a) const;
    void mul(const interval& a, const interval& b, interval& c) { m_imanager.mul(a, b, c); }
    void add(const interval& a, const interval& b, interval& c) { m_imanager.add(a, b, c); }

    template <enum with_deps_t wd>
    void set(interval& a, const interval& b) const {
        m_imanager.set(a, b);
        if (wd == with_deps) {
            a.m_lower_dep = b.m_lower_dep;
            a.m_upper_dep = b.m_upper_dep;
        }
    }

    template <enum with_deps_t wd>
    interval power(const interval& a, unsigned n) {
        interval b;
        if (with_deps == wd) {
            interval_deps_combine_rule combine_rule;
            m_imanager.power(a, n, b, combine_rule);
            combine_deps(a, combine_rule, b);
        }
        else {
            m_imanager.power(a, n, b);
        }
        TRACE("dep_intervals", tout << "power of "; display(tout, a) << " = ";
              display(tout, b) << "\n"; );
        return b;
    }

    template <enum with_deps_t wd>
    void copy_upper_bound(const interval& a, interval& i) const {
        SASSERT(a.m_upper_inf == false);
        i.m_upper_inf = false;
        m_config.set_upper(i, a.m_upper);
        i.m_upper_open = a.m_upper_open;
        if (wd == with_deps) {
            i.m_upper_dep = a.m_upper_dep;
        }
    }

    template <enum with_deps_t wd>
    void copy_lower_bound(const interval& a, interval& i) const {
        SASSERT(a.m_lower_inf == false);
        i.m_lower_inf = false;
        m_config.set_lower(i, a.m_lower);
        i.m_lower_open = a.m_lower_open;
        if (wd == with_deps) {
            i.m_lower_dep = a.m_lower_dep;
        }
    }


    void set_zero_interval_deps_for_mult(interval&);
    void set_zero_interval(interval&, u_dependency* dep = nullptr) const;
    bool is_inf(const interval& i) const { return m_config.is_inf(i); }
    bool separated_from_zero_on_lower(const interval&) const;
    bool separated_from_zero_on_upper(const interval&) const;
    inline bool separated_from_zero(const interval& i) const {
        return separated_from_zero_on_upper(i) || separated_from_zero_on_lower(i);
    }
    // if the separation happens then call f()
    template <typename T> 
    bool check_interval_for_conflict_on_zero(const interval& i, u_dependency* dep, std::function<void (const T&)> f) {
        return check_interval_for_conflict_on_zero_lower(i, dep, f) || check_interval_for_conflict_on_zero_upper(i, dep, f);
    }
    template <typename T> 
    bool check_interval_for_conflict_on_zero_lower(const interval& i, u_dependency* dep, std::function<void (const T&)> f) {
        if (!separated_from_zero_on_lower(i)) {
            return false;
        }
        TRACE("dep_intervals", display(tout, i););
        dep = m_dep_manager.mk_join(dep, i.m_lower_dep);
        T expl;
        linearize(dep, expl);
        f(expl);
        return true;
    }
    template <typename T> 
    bool check_interval_for_conflict_on_zero_upper(const interval& i, u_dependency* dep, std::function<void (const T&)> f) {
        if (!separated_from_zero_on_upper(i))
            return false;
        TRACE("dep_intervals", display(tout, i););
        dep = m_dep_manager.mk_join(dep, i.m_upper_dep);
        T expl;
        linearize(dep, expl);
        f(expl);
        return true;
    }
    mpq const& lower(interval const& a) const { return m_config.lower(a); }
    mpq const& upper(interval const& a) const { return m_config.upper(a); }
    bool is_empty(interval const& a) const;
    void set_interval_for_scalar(interval&, const rational&);
    template <typename T> 
    void linearize(u_dependency* dep, T& expl) const {
        vector<unsigned, false> v;
        m_dep_manager.linearize(dep, v);
        for (unsigned ci: v)
            expl.push_back(ci);
    }

    void reset() { m_dep_manager.reset(); }
    
    template <enum with_deps_t wd> interval intersect(const interval& a, const interval& b) const {
        interval i;
        update_lower_for_intersection<wd>(a, b, i);
        update_upper_for_intersection<wd>(a, b, i);
        return i;
    }

    template <enum with_deps_t wd>
    void update_lower_for_intersection(const interval& a, const interval& b, interval& i) const {
        if (a.m_lower_inf) {
            if (b.m_lower_inf)
                return;
            copy_lower_bound<wd>(b, i);
            return;
        }
        if (b.m_lower_inf) {
            SASSERT(!a.m_lower_inf);
            copy_lower_bound<wd>(a, i);
            return;
        }
        if (m_num_manager.lt(a.m_lower, b.m_lower)) {
            copy_lower_bound<wd>(b, i);
            return;
        }
        if (m_num_manager.gt(a.m_lower, b.m_lower)) {
            copy_lower_bound<wd>(a, i);
            return;
        }
        SASSERT(m_num_manager.eq(a.m_lower, b.m_lower));
        if (a.m_lower_open) { // we might consider to look at b.m_lower_open too here
            copy_lower_bound<wd>(a, i);
            return;
        }
        copy_lower_bound<wd>(b, i);
    }

    template <enum with_deps_t wd>
    void update_upper_for_intersection(const interval& a, const interval& b, interval& i) const {
        if (a.m_upper_inf) {
            if (b.m_upper_inf)
                return;
            copy_upper_bound<wd>(b, i);
            return;
        }
        if (b.m_upper_inf) {
            SASSERT(!a.m_upper_inf);
            copy_upper_bound<wd>(a, i);
            return;
        }
        if (m_num_manager.gt(a.m_upper, b.m_upper)) {
            copy_upper_bound<wd>(b, i);
            return;
        }
        if (m_num_manager.lt(a.m_upper, b.m_upper)) {
            copy_upper_bound<wd>(a, i);
            return;
        }
        SASSERT(m_num_manager.eq(a.m_upper, b.m_upper));
        if (a.m_upper_open) { // we might consider to look at b.m_upper_open too here
            copy_upper_bound<wd>(a, i);
            return;
        }

        copy_upper_bound<wd>(b, i);
    }
};
