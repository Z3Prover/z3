/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#pragma once
#include "util/dependency.h"
#include "util/small_object_allocator.h"
#include "math/lp/nla_common.h"
#include "math/lp/lar_solver.h"
#include "math/interval/interval.h"


namespace nla {
class core;

class intervals : common {
    class ci_value_manager {
    public:
        void inc_ref(lp::constraint_index const & v) {
        }

        void dec_ref(lp::constraint_index const & v) {
        }
    };

    struct ci_dependency_config {
        typedef ci_value_manager        value_manager;
        typedef small_object_allocator  allocator;
        static const bool ref_count = false;
        typedef lp::constraint_index value;
    };
        
    typedef dependency_manager<ci_dependency_config> ci_dependency_manager;

    typedef ci_dependency_manager::dependency ci_dependency;

    class im_config {
        unsynch_mpq_manager&        m_manager;
        ci_dependency_manager&       m_dep_manager;

    public:
        typedef unsynch_mpq_manager numeral_manager;
            

        struct interval {
            interval():
                m_lower(), m_upper(), 
                m_lower_open(1), m_upper_open(1), 
                m_lower_inf(1), m_upper_inf(1), 
                m_lower_dep(nullptr), m_upper_dep(nullptr) {}
            mpq   m_lower;
            mpq   m_upper;
            unsigned  m_lower_open:1;
            unsigned  m_upper_open:1;
            unsigned  m_lower_inf:1;
            unsigned  m_upper_inf:1;
            ci_dependency * m_lower_dep; // justification for the lower bound
            ci_dependency * m_upper_dep; // justification for the upper bound
        };

        void add_deps(interval const& a, interval const& b,
                      interval_deps_combine_rule const& deps, interval& i) const {
            i.m_lower_dep = lower_is_inf(i) ? nullptr : mk_dependency(a, b, deps.m_lower_combine);
            i.m_upper_dep = upper_is_inf(i) ? nullptr : mk_dependency(a, b, deps.m_upper_combine);
        }

        
        // Should be NOOPs for precise mpq types.
        // For imprecise types (e.g., floats) it should set the rounding mode.
        void round_to_minus_inf() {}
        void round_to_plus_inf() {}
        void set_rounding(bool to_plus_inf) {}
            
        // Getters
        mpq const & lower(interval const & a) const { return a.m_lower; }
        mpq const & upper(interval const & a) const { return a.m_upper; }
        mpq & lower(interval & a) { return a.m_lower; }
        mpq & upper(interval & a) { return a.m_upper; }
        bool lower_is_open(interval const & a) const { return a.m_lower_open; }
        bool upper_is_open(interval const & a) const { return a.m_upper_open; }
        bool lower_is_inf(interval const & a) const { return a.m_lower_inf; }
        bool upper_is_inf(interval const & a) const { return a.m_upper_inf; }
        bool is_inf(interval const & a) const { return upper_is_inf(a) && lower_is_inf(a); }
        bool is_zero(interval const & a) const {
            return (!lower_is_inf(a)) && (!upper_is_inf(a)) &&
                (!lower_is_open(a)) && (!upper_is_open(a)) && 
                unsynch_mpq_manager::is_zero(a.m_lower) &&
                unsynch_mpq_manager::is_zero(a.m_upper); }

            
        // Setters
        void set_lower(interval & a, mpq const & n) const { m_manager.set(a.m_lower, n); }
        void set_upper(interval & a, mpq const & n) const { m_manager.set(a.m_upper, n); }
        void set_lower(interval & a, rational const & n) const { set_lower(a, n.to_mpq()); }
        void set_upper(interval & a, rational const & n) const { set_upper(a, n.to_mpq()); }
        void set_lower_is_open(interval & a, bool v) const { a.m_lower_open = v; }
        void set_upper_is_open(interval & a, bool v) const { a.m_upper_open = v; }
        void set_lower_is_inf(interval & a, bool v) const { a.m_lower_inf = v; }
        void set_upper_is_inf(interval & a, bool v) const { a.m_upper_inf = v; }
            
        // Reference to numeral manager
        numeral_manager & m() const { return m_manager; }
            
        im_config(numeral_manager & m, ci_dependency_manager& d):m_manager(m), m_dep_manager(d) {}
    private:
        ci_dependency* mk_dependency(interval const& a, interval const& b, deps_combine_rule bd) const {
            ci_dependency* dep = nullptr;
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
    };

    small_object_allocator      m_alloc;
    ci_value_manager            m_val_manager;
    unsynch_mpq_manager         m_num_manager;
    mutable ci_dependency_manager       m_dep_manager;
    im_config                   m_config;
    mutable interval_manager<im_config> m_imanager;
    region                      m_region;

public:
    typedef interval_manager<im_config>::interval interval;
private:
    void set_var_interval(lpvar v, interval & b) const;
    ci_dependency* mk_dep(lp::constraint_index ci) const;
    lp::lar_solver& ls();
    const lp::lar_solver& ls() const;
public:
    intervals(core* c, reslimit& lim) :
        common(c),
        m_alloc("intervals"),
        m_dep_manager(m_val_manager, m_alloc),
        m_config(m_num_manager, m_dep_manager),
        m_imanager(lim, im_config(m_num_manager, m_dep_manager))
    {}
    interval mul(const svector<lpvar>&) const;
    void get_explanation_of_upper_bound_for_monomial(lpvar j, svector<lp::constraint_index>& expl) const;
    void get_explanation_of_lower_bound_for_monomial(lpvar j, svector<lp::constraint_index>& expl) const;
    std::ostream& print_explanations(const svector<lp::constraint_index> &, std::ostream&) const;
    std::ostream& display(std::ostream& out, const intervals::interval& i) const;
    void set_lower(interval & a, rational const & n) const { m_config.set_lower(a, n.to_mpq()); }
    void set_upper(interval & a, rational const & n) const { m_config.set_upper(a, n.to_mpq()); }
    void set_lower_is_open(interval & a, bool strict) { m_config.set_lower_is_open(a, strict); }
    void set_lower_is_inf(interval & a, bool inf) { m_config.set_lower_is_inf(a, inf); }
    void set_upper_is_open(interval & a, bool strict) { m_config.set_upper_is_open(a, strict); }
    void set_upper_is_inf(interval & a, bool inf) { m_config.set_upper_is_inf(a, inf); }
    bool is_zero(const interval& a) const { return m_config.is_zero(a); }
    void mul(const rational& r, const interval& a, interval& b) const {       
        m_imanager.mul(r.to_mpq(), a, b);
        if (r.is_pos()) {
            b.m_lower_dep = a.m_lower_dep;
            b.m_upper_dep = a.m_upper_dep;
        } else {
            SASSERT(r.is_neg());
            b.m_upper_dep = a.m_lower_dep;
            b.m_lower_dep = a.m_upper_dep;
        }
    }

    void add(const rational& r, interval& a) const {
        if (!a.m_lower_inf) {
            m_config.set_lower(a, a.m_lower + r);
        }
        if (!a.m_upper_inf) {
            m_config.set_upper(a, a.m_upper + r);
        }
    }

    void mul(const interval& a, const interval& b, interval& c) { m_imanager.mul(a, b, c); }
    void add(const interval& a, const interval& b, interval& c) { m_imanager.add(a, b, c); }
    void add(const interval& a, const interval& b, interval& c, interval_deps_combine_rule& deps) { m_imanager.add(a, b, c, deps); }
    void set(interval& a, const interval& b) const {
        m_imanager.set(a, b);
        a.m_lower_dep = b.m_lower_dep;
        a.m_upper_dep = b.m_upper_dep;
    }
    void mul(const interval& a, const interval& b, interval& c, interval_deps_combine_rule& deps) { m_imanager.mul(a, b, c, deps); }
    void combine_deps(interval const& a, interval const& b, interval_deps_combine_rule const& deps, interval& i) const {
        SASSERT(&a != &i && &b != &i);
        m_config.add_deps(a, b, deps, i);
    }

    bool is_tighter_on_lower(const interval& a, const interval& b) const {
        if (lower_is_inf(a))
            return false;
        if (lower_is_inf(b))
            return true;
        if (rational(lower(a)) < rational(lower(b)))
            return true;
        if (lower(a) > lower(b))
            return false;

        if (!a.m_lower_open)
            return false;
        if (b.m_lower_open)
            return false;

        return true;
    }

    bool is_tighter_on_upper(const interval& a, const interval& b) const {
        if (upper_is_inf(a))
            return false;
        if (upper_is_inf(b))
            return true;
        if (rational(upper(a)) > rational(upper(b)))
            return true;
        if (rational(upper(a)) < rational(upper(b)))
            return false;

        if (!a.m_upper_open)
            return false;
        if (b.m_upper_open)
            return false;

        return true;
    }
    
    bool is_tighter(const interval& a, const interval& b) const {
        return (is_tighter_on_lower(a, b) && !is_tighter_on_upper(b, a)) ||
            (is_tighter_on_upper(a, b) && is_tighter_on_lower(b, a));
    }
    
    bool upper_is_inf(const interval& a) const { return m_config.upper_is_inf(a); }
    bool lower_is_inf(const interval& a) const { return m_config.lower_is_inf(a); }    
    void set_var_interval_with_deps(lpvar, interval &) const;
    void set_zero_interval_deps_for_mult(interval&);
    bool is_inf(const interval& i) const { return m_config.is_inf(i); }
    bool check_interval_for_conflict_on_zero(const interval & i);
    bool check_interval_for_conflict_on_zero_lower(const interval & i);
    bool check_interval_for_conflict_on_zero_upper(const interval & i);
    mpq const & lower(interval const & a) const { return m_config.lower(a); }
    mpq const & upper(interval const & a) const { return m_config.upper(a); }
}; // end of intervals
} // end of namespace nla
