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
#include "util/region.h"
#include "math/lp/nla_common.h"
#include "math/lp/lar_solver.h"
#include "math/interval/interval.h"
#include "util/dependency.h"


namespace nla {
class core;

class intervals {
    typedef common::ci_dependency_manager ci_dependency_manager;
    typedef ci_dependency_manager::dependency ci_dependency;

    class im_config {
        unsynch_mpq_manager& m_manager;
        common::ci_dependency_manager& m_dep_manager;

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
            ci_dependency* m_lower_dep; // justification for the lower bound
            ci_dependency* m_upper_dep; // justification for the upper bound
        };

        void add_deps(interval const& a, interval const& b,
            interval_deps_combine_rule const& deps, interval& i) const {
            i.m_lower_dep = lower_is_inf(i) ? nullptr : mk_dependency(a, b, deps.m_lower_combine);
            i.m_upper_dep = upper_is_inf(i) ? nullptr : mk_dependency(a, b, deps.m_upper_combine);
        }

        void add_deps(interval const& a,
            interval_deps_combine_rule const& deps, interval& i) const {
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

        im_config(numeral_manager& m, ci_dependency_manager& d) :m_manager(m), m_dep_manager(d) {}
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

        ci_dependency* mk_dependency(interval const& a, deps_combine_rule bd) const {
            ci_dependency* dep = nullptr;
            if (dep_in_lower1(bd)) {
                dep = m_dep_manager.mk_join(dep, a.m_lower_dep);
            }
            if (dep_in_upper1(bd)) {
                dep = m_dep_manager.mk_join(dep, a.m_upper_dep);
            }
            return dep;
        }

    };

    region                              m_alloc;
    common::ci_value_manager            m_val_manager;
    mutable unsynch_mpq_manager         m_num_manager;
    mutable ci_dependency_manager       m_dep_manager;
    im_config                           m_config;
    mutable interval_manager<im_config> m_imanager;
    core* m_core;

public:
    ci_dependency_manager& dep_manager() { return m_dep_manager; }
    typedef interval_manager<im_config>::interval interval;
private:
    ci_dependency* mk_dep(lp::constraint_index ci) const;
    ci_dependency* mk_dep(lp::explanation const&) const;
    lp::lar_solver& ls();
    const lp::lar_solver& ls() const;
public:
    enum with_deps_t { with_deps, without_deps };

    intervals(core* c, reslimit& lim) :
        m_alloc(),
        m_dep_manager(m_val_manager, m_alloc),
        m_config(m_num_manager, m_dep_manager),
        m_imanager(lim, im_config(m_num_manager, m_dep_manager)),
        m_core(c)
    {}
    ci_dependency* mk_join(ci_dependency* a, ci_dependency* b) { return m_dep_manager.mk_join(a, b); }
    ci_dependency* mk_leaf(lp::constraint_index ci) { return m_dep_manager.mk_leaf(ci); }

    std::ostream& print_dependencies(ci_dependency*, std::ostream&) const;
    std::ostream& display(std::ostream& out, const intervals::interval& i) const;
    void set_lower(interval& a, rational const& n) const { m_config.set_lower(a, n.to_mpq()); }
    void set_upper(interval& a, rational const& n) const { m_config.set_upper(a, n.to_mpq()); }
    void set_lower_is_open(interval& a, bool strict) { m_config.set_lower_is_open(a, strict); }
    void set_lower_is_inf(interval& a, bool inf) { m_config.set_lower_is_inf(a, inf); }
    void set_upper_is_open(interval& a, bool strict) { m_config.set_upper_is_open(a, strict); }
    void set_upper_is_inf(interval& a, bool inf) { m_config.set_upper_is_inf(a, inf); }
    bool is_zero(const interval& a) const { return m_config.is_zero(a); }


    template <enum with_deps_t wd>
    void mul(const rational& r, const interval& a, interval& b) const {
        m_imanager.mul(r.to_mpq(), a, b);
        if (wd == with_deps) {
            if (r.is_pos()) {
                b.m_lower_dep = a.m_lower_dep;
                b.m_upper_dep = a.m_upper_dep;
            }
            else {
                SASSERT(r.is_neg());
                b.m_upper_dep = a.m_lower_dep;
                b.m_lower_dep = a.m_upper_dep;
            }
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

    template <enum with_deps_t wd>
    void set(interval& a, const interval& b) const {
        m_imanager.set(a, b);
        if (wd == with_deps) {
            a.m_lower_dep = b.m_lower_dep;
            a.m_upper_dep = b.m_upper_dep;
        }
    }

    void mul_two_intervals(const interval& a, const interval& b, interval& c, interval_deps_combine_rule& deps) { m_imanager.mul(a, b, c, deps); }

    void combine_deps(interval const& a, interval const& b, interval_deps_combine_rule const& deps, interval& i) const {
        SASSERT(&a != &i && &b != &i);
        m_config.add_deps(a, b, deps, i);
    }

    void combine_deps(interval const& a, interval_deps_combine_rule const& deps, interval& i) const {
        SASSERT(&a != &i);
        m_config.add_deps(a, deps, i);
    }

    template <enum with_deps_t wd>
    interval power(const interval& a, unsigned n) {
        interv b;
        if (with_deps == wd) {
            interval_deps_combine_rule combine_rule;
            m_imanager.power(a, n, b, combine_rule);
            combine_deps(a, combine_rule, b);
        }
        else {
            m_imanager.power(a, n, b);
        }
        TRACE("nla_horner_details", tout << "power of "; display(tout, a) << " = ";
        display(tout, b) << "\n"; );
        return b;
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

    template <enum with_deps_t wd>
    void set_var_interval(lpvar v, interval& b) const {
        TRACE("nla_intervals_details", m_core->print_var(v, tout) << "\n";);
        lp::constraint_index ci;
        rational val;
        bool is_strict;
        if (ls().has_lower_bound(v, ci, val, is_strict)) {
            m_config.set_lower(b, val);
            m_config.set_lower_is_open(b, is_strict);
            m_config.set_lower_is_inf(b, false);
            if (wd == with_deps) b.m_lower_dep = mk_dep(ci);
        }
        else {
            m_config.set_lower_is_open(b, true);
            m_config.set_lower_is_inf(b, true);
            if (wd == with_deps) b.m_lower_dep = nullptr;
        }
        if (ls().has_upper_bound(v, ci, val, is_strict)) {
            m_config.set_upper(b, val);
            m_config.set_upper_is_open(b, is_strict);
            m_config.set_upper_is_inf(b, false);
            if (wd == with_deps) b.m_upper_dep = mk_dep(ci);
        }
        else {
            m_config.set_upper_is_open(b, true);
            m_config.set_upper_is_inf(b, true);
            if (wd == with_deps) b.m_upper_dep = nullptr;
        }
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

    template <enum with_deps_t wd>
    interval intersect(const interval& a, const interval& b) const {
        interval i;
        TRACE("nla_interval_compare", tout << "a="; display(tout, a) << "\nb="; display(tout, b););
        update_lower_for_intersection<wd>(a, b, i);
        TRACE("nla_interval_compare", tout << "i="; display(tout, i) << "\n";);
        update_upper_for_intersection<wd>(a, b, i);
        TRACE("nla_interval_compare", tout << "i="; display(tout, i) << "\n";);
        return i;
    }

    template <enum with_deps_t wd>
    bool interval_from_term(const nex& e, interval& i) const {
        rational a, b;
        lp::lar_term norm_t = expression_to_normalized_term(&e.to_sum(), a, b);
        lp::explanation exp;
        if (m_core->explain_by_equiv(norm_t, exp)) {
            set_zero_interval(i);
            TRACE("nla_intervals", tout << "explain_by_equiv\n";);
            return true;
        }
        lpvar j = find_term_column(norm_t, a);
        if (j + 1 == 0)
            return false;

        set_var_interval<without_deps>(j, i);
        interv bi;
        mul<wd>(a, i, bi);
        add(b, bi);
        set<wd>(i, bi);

        TRACE("nla_intervals",
            m_core->m_lar_solver.print_column_info(j, tout) << "\n";
        tout << "a=" << a << ", b=" << b << "\n";
        tout << e << ", interval = "; display(tout, i););
        return true;
    }

    template <enum with_deps_t wd>
    interval interval_of_sum_no_term(const nex_sum& e) {
        const nex* inf_e = get_inf_interval_child(e);
        if (inf_e) {
            return interv();
        }
        interv a = interval_of_expr<wd>(e[0], 1);
        for (unsigned k = 1; k < e.size(); k++) {
            TRACE("nla_intervals_details_sum", tout << "e[" << k << "]= " << *e[k] << "\n";);
            interv b = interval_of_expr<wd>(e[k], 1);
            interv c;

            TRACE("nla_intervals_details_sum", tout << "a = "; display(tout, a) << "\nb = "; display(tout, b) << "\n";);
            if (wd == with_deps) {
                interval_deps_combine_rule combine_rule;
                add(a, b, c, combine_rule);
                combine_deps(a, b, combine_rule, c);
            }
            else {
                add(a, b, c);
            }
            set<wd>(a, c);
            TRACE("nla_intervals_details_sum", tout << *e[k] << ", ";
            display(tout, a); tout << "\n";);
        }
        TRACE("nla_intervals_details", tout << "e=" << e << "\n";
        tout << " interv = "; display(tout, a););
        return a;
    }

    template <enum with_deps_t wd>
    interval interval_of_sum(const nex_sum& e) {
        TRACE("nla_intervals_details", tout << "e=" << e << "\n";);
        interv i_e = interval_of_sum_no_term<wd>(e);
        if (e.is_a_linear_term()) {
            SASSERT(e.is_sum() && e.size() > 1);
            interv i_from_term;
            if (interval_from_term<wd>(e, i_from_term)) {
                interv r = intersect<wd>(i_e, i_from_term);
                TRACE("nla_intervals_details", tout << "intersection="; display(tout, r) << "\n";);
                if (is_empty(r)) {
                    SASSERT(false); // not implemented
                }
                return r;

            }
        }
        return i_e;
    }

    template <enum with_deps_t wd>
    interval interval_of_mul(const nex_mul& e) {
        TRACE("nla_intervals_details", tout << "e = " << e << "\n";);
        const nex* zero_interval_child = get_zero_interval_child(e);
        if (zero_interval_child) {
            interv a = interval_of_expr<wd>(zero_interval_child, 1);
            set_zero_interval_deps_for_mult(a);
            TRACE("nla_intervals_details", tout << "zero_interval_child = " << *zero_interval_child << std::endl << "a = "; display(tout, a); );
            return a;
        }

        interv a;
        set_interval_for_scalar(a, e.coeff());
        TRACE("nla_intervals_details", tout << "a = "; display(tout, a); );
        for (const auto& ep : e) {
            interv b = interval_of_expr<wd>(ep.e(), ep.pow());
            TRACE("nla_intervals_details", tout << "ep = " << ep << ", "; display(tout, b); );
            interv c;
            interval_deps_combine_rule comb_rule;
            mul_two_intervals(a, b, c, comb_rule);
            TRACE("nla_intervals_details", tout << "c before combine_deps() "; display(tout, c););
            combine_deps(a, b, comb_rule, c);
            TRACE("nla_intervals_details", tout << "a "; display(tout, a););
            TRACE("nla_intervals_details", tout << "c "; display(tout, c););
            set<wd>(a, c);
            TRACE("nla_intervals_details", tout << "part mult "; display(tout, a););
        }
        TRACE("nla_intervals_details", tout << "e=" << e << "\n";
        tout << " return "; display(tout, a););
        return a;
    }

    template <enum with_deps_t wd>
    interval interval_of_expr(const nex* e, unsigned p) {
        interv a;
        switch (e->type()) {
        case expr_type::SCALAR:
            set_interval_for_scalar(a, to_scalar(e)->value());
            if (p != 1) {
                return power<wd>(a, p);
            }
            return a;
        case expr_type::SUM: {
            interv b = interval_of_sum<wd>(e->to_sum());
            if (p != 1)
                return power<wd>(b, p);
            return b;
        }
        case expr_type::MUL: {
            interv b = interval_of_mul<with_deps>(e->to_mul());
            if (p != 1)
                return power<wd>(b, p);
            return b;
        }
        case expr_type::VAR:
            set_var_interval<wd>(e->to_var().var(), a);
            if (p != 1)
                return power<wd>(a, p);;
            return a;
        default:
            TRACE("nla_intervals_details", tout << e->type() << "\n";);
            UNREACHABLE();
            return interval();
        }
    }

    bool upper_is_inf(const interval& a) const { return m_config.upper_is_inf(a); }
    bool lower_is_inf(const interval& a) const { return m_config.lower_is_inf(a); }

    void set_zero_interval_deps_for_mult(interval&);
    void set_zero_interval_with_explanation(interval&, const lp::explanation& exp) const;
    void set_zero_interval(interval&) const;
    bool is_inf(const interval& i) const { return m_config.is_inf(i); }
    bool separated_from_zero_on_lower(const interval&) const;
    bool separated_from_zero_on_upper(const interval&) const;
    inline  bool separated_from_zero(const interval& i) const {
        return separated_from_zero_on_upper(i) ||
            separated_from_zero_on_lower(i);
    }
    bool check_interval_for_conflict_on_zero(const interval& i, ci_dependency*);
    bool check_interval_for_conflict_on_zero_lower(const interval& i, ci_dependency*);
    bool check_interval_for_conflict_on_zero_upper(const interval& i, ci_dependency*);
    mpq const& lower(interval const& a) const { return m_config.lower(a); }
    mpq const& upper(interval const& a) const { return m_config.upper(a); }
    inline bool is_empty(interval const& a) const {
        if (a.m_lower_inf || a.m_upper_inf)
            return false;
        if (m_num_manager.gt(a.m_lower, a.m_upper))
            return true;
        if (m_num_manager.lt(a.m_lower, a.m_upper))
            return false;
        if (a.m_lower_open || a.m_upper_open)
            return true;
        return false;
    }
    void reset() { m_alloc.reset(); }
    bool check_nex(const nex*, ci_dependency*);
    typedef interval interv;
    void set_interval_for_scalar(interv&, const rational&);
    const nex* get_zero_interval_child(const nex_mul&) const;
    const nex* get_inf_interval_child(const nex_sum&) const;
    bool has_zero_interval(const nex&) const;
    bool has_inf_interval(const nex&) const;
    bool mul_has_inf_interval(const nex_mul&) const;
    static lp::lar_term expression_to_normalized_term(const nex_sum*, rational& a, rational& b);
    static void add_linear_to_vector(const nex*, vector<std::pair<rational, lpvar>>&);
    static void add_mul_of_degree_one_to_vector(const nex_mul*, vector<std::pair<rational, lpvar>>&);
    lpvar find_term_column(const lp::lar_term&, rational& a) const;
}; // end of intervals
} // end of namespace nla
