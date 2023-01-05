/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

Notes:

TODO: Investigate in depth a notion of phase caching for variables.
The Linear solver can be used to supply a phase in some cases.
In other cases, the phase of a variable assignment across branches
might be used in a call to is_viable. With phase caching on, it may
just check if the cached phase is viable without detecting that it is a propagation.

TODO: improve management of the fallback univariate solvers:
      - use a solver pool and recycle the least recently used solver
      - incrementally add/remove constraints
      - set resource limit of univariate solver

TODO: plan to fix the FI "pumping":
    1. simple looping detection and bitblasting fallback.  -- done
    2. intervals at multiple bit widths
        - for equations, this will give us exact solutions for all coefficients
        - for inequalities, a coefficient 2^k*a means that intervals are periodic because the upper k bits of x are irrelevant;
          storing the interval for x[K-k:0] would take care of this.

--*/


#include "util/debug.h"
#include "math/polysat/viable.h"
#include "math/polysat/solver.h"
#include "math/polysat/number.h"
#include "math/polysat/univariate/univariate_solver.h"

namespace polysat {

    using namespace viable_query;

    struct inf_fi : public inference {
        viable& v;
        pvar var;
        inf_fi(viable& v, pvar var) : v(v), var(var) {}
        std::ostream& display(std::ostream& out) const override {
            return out << "Forbidden intervals for v" << var << ": " << viable::var_pp(v, var);
        }
    };

    viable::viable(solver& s):
        s(s),
        m_forbidden_intervals(s) {
    }

    viable::~viable() {
        for (entry* e : m_alloc)
            dealloc(e);
    }

    void viable::push_var(unsigned bit_width) {
        m_units.push_back(nullptr);
        m_equal_lin.push_back(nullptr);
        m_diseq_lin.push_back(nullptr);
    }

    void viable::pop_var() {
        m_units.pop_back();
        m_equal_lin.pop_back();
        m_diseq_lin.pop_back();
    }

    viable::entry* viable::alloc_entry() {
        if (m_alloc.empty())
            return alloc(entry);
        auto* e = m_alloc.back();
        e->side_cond.reset();
        e->coeff = 1;
        e->refined = nullptr;
        m_alloc.pop_back();
        return e;
    }

    void viable::pop_viable() {
        auto const& [v, k, e] = m_trail.back();
        SASSERT(well_formed(m_units[v]));
        switch (k) {
        case entry_kind::unit_e:
            entry::remove_from(m_units[v], e);
            SASSERT(well_formed(m_units[v]));
            break;
        case entry_kind::equal_e:
            entry::remove_from(m_equal_lin[v], e);
            break;
        case entry_kind::diseq_e:
            entry::remove_from(m_diseq_lin[v], e);
            break;
        default:
            UNREACHABLE();
            break;
        }
        m_alloc.push_back(e);
        m_trail.pop_back();
    }

    void viable::push_viable() {
        auto& [v, k, e] = m_trail.back();
        SASSERT(e->prev() != e || !m_units[v]);
        SASSERT(e->prev() != e || e->next() == e);
        SASSERT(k == entry_kind::unit_e);
        (void)k;
        SASSERT(well_formed(m_units[v]));
        if (e->prev() != e) {
            entry* pos = e->prev();
            e->init(e);
            pos->insert_after(e);
            if (e->interval.lo_val() < m_units[v]->interval.lo_val())
                m_units[v] = e;
        }
        else
            m_units[v] = e;
        SASSERT(well_formed(m_units[v]));
        m_trail.pop_back();
    }

    bool viable::intersect(pdd const& p, pdd const& q, signed_constraint const& sc) {
        pvar v = null_var;
        bool first = true;
        bool prop = false;
        if (p.is_unilinear())
            v = p.var();
        else if (q.is_unilinear())
            v = q.var(), first = false;
        else
            return prop;

    try_viable:
        if (intersect(v, sc)) {
            rational val;
            switch (find_viable(v, val)) {
            case find_t::singleton:
                propagate(v, val);
                prop = true;
                break;
            case find_t::empty:
                SASSERT(s.is_conflict());
                return true;
            default:
                break;
            }
        }
        if (first && q.is_unilinear() && q.var() != v) {
            v = q.var();
            first = false;
            goto try_viable;
        }
        return prop;
    }

    void viable::propagate(pvar v, rational const& val) {
        // NOTE: all propagations must be justified by a prefix of \Gamma,
        //       otherwise dependencies may be missed during conflict resolution.
        //       The propagation reason for v := val consists of the following constraints:
        //       - source constraint (already on \Gamma)
        //       - side conditions
        //       - i.lo() == i.lo_val() for each unit interval i
        //       - i.hi() == i.hi_val() for each unit interval i

        // NSB review:
        // the bounds added by x < p and p < x in forbidden_intervals
        // match_non_max, match_non_zero
        // use values that are approximations. Then the propagations in
        // try_assign_eval are incorrect.
        // For example, x > p means x has forbidden interval [0, p + 1[,
        // the numeric interval is [0, 1[, but p + 1 == 1 is not ensured
        // even p may have free variables.
        // the proper side condition on p + 1 is -1 > p or -2 >= p or p + 1 != 0
        // I am disabling match_non_max and match_non_zero from forbidden_interval
        // The narrowing rules in ule_constraint already handle the bounds propagaitons
        // as it propagates p != -1 and 0 != q (p < -1, q > 0),
        //
        
        for (auto const& c : get_constraints(v)) {
            s.try_assign_eval(c);
        }
        for (auto const& i : units(v)) {
            s.try_assign_eval(s.eq(i.lo(), i.lo_val()));
            s.try_assign_eval(s.eq(i.hi(), i.hi_val()));
        }
        s.assign_propagate(v, val);
    }

    bool viable::intersect(pvar v, signed_constraint const& c) {
        entry* ne = alloc_entry();
        if (!m_forbidden_intervals.get_interval(c, v, *ne)) {
            m_alloc.push_back(ne);
            return false;
        }
        else if (ne->interval.is_currently_empty()) {
            m_alloc.push_back(ne);
            return false;
        }
        else if (ne->coeff == 1) {
            return intersect(v, ne);
        }
        else if (ne->coeff == -1) {
            insert(ne, v, m_diseq_lin, entry_kind::diseq_e);
            return true;
        }
        else {
            insert(ne, v, m_equal_lin, entry_kind::equal_e);
            return true;
        }
    }

    void viable::insert(entry* e, pvar v, ptr_vector<entry>& entries, entry_kind k) {
        SASSERT(well_formed(m_units[v]));
        m_trail.push_back({ v, k, e });
        s.m_trail.push_back(trail_instr_t::viable_add_i);
        e->init(e);
        if (!entries[v])
            entries[v] = e;
        else
            e->insert_after(entries[v]);
        SASSERT(entries[v]->invariant());
        SASSERT(well_formed(m_units[v]));
    }

    bool viable::intersect(pvar v, entry* ne) {
        // SASSERT(!s.is_assigned(v));  // TODO: do we get unsoundness if this condition is violated? (see comment on cyclic dependencies in solver::pop_levels)
        entry* e = m_units[v];
        if (e && e->interval.is_full()) {
            m_alloc.push_back(ne);
            return false;
        }

        if (ne->interval.is_currently_empty()) {
            m_alloc.push_back(ne);
            return false;
        }

        auto create_entry = [&]() {
            m_trail.push_back({ v, entry_kind::unit_e, ne });
            s.m_trail.push_back(trail_instr_t::viable_add_i);
            ne->init(ne);
            return ne;
        };

        auto remove_entry = [&](entry* e) {
            m_trail.push_back({ v, entry_kind::unit_e, e });
            s.m_trail.push_back(trail_instr_t::viable_rem_i);
            e->remove_from(m_units[v], e);
        };

        if (ne->interval.is_full()) {
            while (m_units[v])
                remove_entry(m_units[v]);
            m_units[v] = create_entry();
            return true;
        }

        if (!e)
            m_units[v] = create_entry();
        else {
            entry* first = e;
            do {
                if (e->interval.currently_contains(ne->interval)) {
                    m_alloc.push_back(ne);
                    return false;
                }
                while (ne->interval.currently_contains(e->interval)) {
                    entry* n = e->next();
                    remove_entry(e);
                    if (!m_units[v]) {
                        m_units[v] = create_entry();
                        return true;
                    }
                    if (e == first)
                        first = n;
                    e = n;
                }
                SASSERT(e->interval.lo_val() != ne->interval.lo_val());
                if (e->interval.lo_val() > ne->interval.lo_val()) {
                    if (first->prev()->interval.currently_contains(ne->interval)) {
                        m_alloc.push_back(ne);
                        return false;
                    }
                    e->insert_before(create_entry());
                    if (e == first)
                        m_units[v] = e->prev();
                    SASSERT(well_formed(m_units[v]));
                    return true;
                }
                e = e->next();
            }
            while (e != first);
            // otherwise, append to end of list
            first->insert_before(create_entry());
        }
        SASSERT(well_formed(m_units[v]));
        return true;
    }

    bool viable::refine_viable(pvar v, rational const& val) {
        return refine_equal_lin(v, val) && refine_disequal_lin(v, val);
    }

    /**
    * Traverse all interval constraints with coefficients to check whether current value 'val' for
    * 'v' is feasible. If not, extract a (maximal) interval to block 'v' from being assigned val.
    *
    * To investigate:
    * - side conditions are stronger than for unit intervals. They constrain the lower and upper bounds to
    *   be precisely the assigned values. This is to ensure that lo/hi that are computed based on lo_val
    *   and division with coeff are valid. Is there a more relaxed scheme?
    */
    bool viable::refine_equal_lin(pvar v, rational const& val) {
        // LOG_H2("refine-equal-lin with v" << v << ", val = " << val);
        entry const* e = m_equal_lin[v];
        if (!e)
            return true;
        entry const* first = e;
        auto& m = s.var2pdd(v);
        unsigned const N = m.power_of_2();
        rational const& max_value = m.max_value();
        rational const& mod_value = m.two_to_N();

        // Rotate the 'first' entry, to prevent getting stuck in a refinement loop
        // with an early entry when a later entry could give a better interval.
        m_equal_lin[v] = m_equal_lin[v]->next();

        auto delta_l = [&](rational const& coeff_val) {
            return floor((coeff_val - e->interval.lo_val()) / e->coeff);
        };
        auto delta_u = [&](rational const& coeff_val) {
            return floor((e->interval.hi_val() - coeff_val - 1) / e->coeff);
        };

        // naive widening. TODO: can we accelerate this?
        // condition e->interval.hi_val() < coeff_val is
        // to ensure that widening is performed on the same interval
        // similar for e->interval.lo_val() > coeff_val
        // needs a proof.
        auto increase_hi = [&](rational& hi) {
            while (hi < max_value) {
                rational coeff_val = mod(e->coeff * hi, mod_value);
                if (!e->interval.currently_contains(coeff_val))
                    break;
                if (e->interval.hi_val() < coeff_val)
                    break;
                hi += delta_u(coeff_val) + 1;
            }
        };
        auto decrease_lo = [&](rational& lo) {
            while (lo > 1) {
                rational coeff_val = mod(e->coeff * (lo - 1), mod_value);
                if (!e->interval.currently_contains(coeff_val))
                    break;
                if (e->interval.lo_val() > coeff_val)
                    break;
                rational d = delta_l(coeff_val);
                if (d.is_zero())
                    break;
                lo -= d;
            }
        };
        do {
            rational coeff_val = mod(e->coeff * val, mod_value);
            if (e->interval.currently_contains(coeff_val)) {
                LOG("refine-equal-lin for src: " << lit_pp(s, e->src));
                LOG("forbidden interval v" << v << " " << num_pp(s, v, val) << "    " << num_pp(s, v, e->coeff, true) << " * " << e->interval);

                if (mod(e->interval.hi_val() + 1, mod_value) == e->interval.lo_val()) {
                    // We have an equation:  a * v == b
                    rational const a = e->coeff;
                    rational const b = e->interval.hi_val();
                    LOG("refine-equal-lin: equation detected: " << dd::val_pp(m, a, true) << " * v" << v << " == " << dd::val_pp(m, b, false));
                    unsigned const parity_a = get_parity(a, N);
                    unsigned const parity_b = get_parity(b, N);
                    // LOG("a " << a << " parity " << parity_a);
                    // LOG("b " << b << " parity " << parity_b);
                    if (parity_a > parity_b) {
                        // No solution
                        LOG("refined: no solution due to parity");
                        entry* ne = alloc_entry();
                        ne->refined = e;
                        ne->src = e->src;
                        ne->side_cond = e->side_cond;
                        ne->coeff = 1;
                        ne->interval = eval_interval::full();
                        intersect(v, ne);
                        return false;
                    }
                    if (parity_a == 0) {
                        // "fast path" for odd a
                        rational a_inv;
                        VERIFY(a.mult_inverse(N, a_inv));
                        rational const hi = mod(a_inv * b, mod_value);
                        rational const lo = mod(hi + 1, mod_value);
                        LOG("refined to [" << num_pp(s, v, lo) << ", " << num_pp(s, v, hi) << "[");
                        SASSERT_EQ(mod(a * hi, mod_value), b);  // hi is the solution
                        entry* ne = alloc_entry();
                        ne->refined = e;
                        ne->src = e->src;
                        ne->side_cond = e->side_cond;
                        ne->coeff = 1;
                        ne->interval = eval_interval::proper(m.mk_val(lo), lo, m.mk_val(hi), hi);
                        SASSERT(ne->interval.currently_contains(val));
                        intersect(v, ne);
                        return false;
                    }
                    // 2^k * v == a_inv * b
                    // 2^k solutions because only the lower N-k bits of v are fixed.
                    //
                    // Smallest solution is v0 == a_inv * (b >> k)
                    // Solutions are of the form v_i = v0 + 2^(N-k) * i for i in { 0, 1, ..., 2^k - 1 }.
                    // Forbidden intervals: [v_i + 1; v_{i+1}[  == [ v_i + 1; v_i + 2^(N-k) [
                    // We need the interval that covers val:
                    //      v_i + 1 <= val < v_i + 2^(N-k)
                    //
                    // TODO: create one interval for v[N-k:] instead of 2^k intervals for v.
                    unsigned const k = parity_a;
                    rational const a_inv = a.pseudo_inverse(N);
                    unsigned const N_minus_k = N - k;
                    rational const two_to_N_minus_k = rational::power_of_two(N_minus_k);
                    rational const v0 = mod(a_inv * machine_div2k(b, k), two_to_N_minus_k);
                    SASSERT(mod(val, two_to_N_minus_k) != v0);  // val is not a solution
                    rational const vi = v0 + clear_lower_bits(mod(val - v0, mod_value), N_minus_k);
                    rational const lo = mod(vi + 1, mod_value);
                    rational const hi = mod(vi + two_to_N_minus_k, mod_value);
                    LOG("refined to [" << num_pp(s, v, lo) << ", " << num_pp(s, v, hi) << "[");
                    SASSERT_EQ(mod(a * (lo - 1), mod_value), b);  // lo-1 is a solution
                    SASSERT_EQ(mod(a * hi, mod_value), b);  // hi is a solution
                    entry* ne = alloc_entry();
                    ne->refined = e;
                    ne->src = e->src;
                    ne->side_cond = e->side_cond;
                    ne->coeff = 1;
                    ne->interval = eval_interval::proper(m.mk_val(lo), lo, m.mk_val(hi), hi);
                    SASSERT(ne->interval.currently_contains(val));
                    intersect(v, ne);
                    return false;
                }

                rational lo = val - delta_l(coeff_val);
                rational hi = val + delta_u(coeff_val) + 1;

                if (e->interval.lo_val() < e->interval.hi_val()) {
                    increase_hi(hi);
                    decrease_lo(lo);
                }
                else if (e->interval.lo_val() <= coeff_val) {
                    rational lambda_u = floor((max_value - coeff_val) / e->coeff);
                    hi = val + lambda_u + 1;
                    if (hi > max_value)
                        hi = 0;
                    decrease_lo(lo);
                }
                else {
                    SASSERT(coeff_val < e->interval.hi_val());
                    rational lambda_l = floor(coeff_val / e->coeff);
                    lo = val - lambda_l;
                    increase_hi(hi);
                }
                LOG("refined to [" << num_pp(s, v, lo) << ", " << num_pp(s, v, hi) << "[");
                SASSERT(hi <= mod_value);
                bool full = (lo == 0 && hi == mod_value);
                if (hi == mod_value)
                    hi = 0;
                entry* ne = alloc_entry();
                ne->refined = e;
                ne->src = e->src;
                ne->side_cond = e->side_cond;
                ne->coeff = 1;
                if (full)
                    ne->interval = eval_interval::full();
                else
                    ne->interval = eval_interval::proper(m.mk_val(lo), lo, m.mk_val(hi), hi);
                intersect(v, ne);
                return false;
            }
            e = e->next();
        }
        while (e != first);
        return true;
    }

    bool viable::refine_disequal_lin(pvar v, rational const& val) {
        // LOG_H2("refine-disequal-lin with v" << v << ", val = " << val);
        entry const* e = m_diseq_lin[v];
        if (!e)
            return true;
        entry const* first = e;
        rational const& max_value = s.var2pdd(v).max_value();
        rational const mod_value = max_value + 1;

        // Rotate the 'first' entry, to prevent getting stuck in a refinement loop
        // with an early entry when a later entry could give a better interval.
        m_diseq_lin[v] = m_diseq_lin[v]->next();

        do {
            LOG("refine-disequal-lin for src: " << e->src);
            // We compute an interval if the concrete value 'val' violates the constraint:
            //      p*val + q >  r*val + s  if e->src.is_positive()
            //      p*val + q >= r*val + s  if e->src.is_negative()
            // Note that e->interval is meaningless in this case,
            // we just use it to transport the values p,q,r,s
            rational const& p = e->interval.lo_val();
            rational const& q_ = e->interval.lo().val();
            rational const& r = e->interval.hi_val();
            rational const& s_ = e->interval.hi().val();
            SASSERT(p != r && p != 0 && r != 0);

            rational const a = mod(p * val + q_, mod_value);
            rational const b = mod(r * val + s_, mod_value);
            rational const np = mod_value - p;
            rational const nr = mod_value - r;
            int const corr = e->src.is_negative() ? 1 : 0;

            auto delta_l = [&](rational const& val) {
                rational num = a - b + corr;
                rational l1 = floor(b / r);
                rational l2 = val;
                if (p > r)
                    l2 = ceil(num / (p - r)) - 1;
                rational l3 = ceil(num / (p + nr)) - 1;
                rational l4 = ceil((mod_value - a) / np) - 1;
                rational d1 = l3;
                rational d2 = std::min(l1, l2);
                rational d3 = std::min(l1, l4);
                rational d4 = std::min(l2, l4);
                rational dmax = std::max(std::max(d1, d2), std::max(d3, d4));
                return std::min(val, dmax);
            };
            auto delta_u = [&](rational const& val) {
                rational num = a - b + corr;
                rational h1 = floor(b / nr);
                rational h2 = max_value - val;
                if (r > p)
                    h2 = ceil(num / (r - p)) - 1;
                rational h3 = ceil(num / (np + r)) - 1;
                rational h4 = ceil((mod_value - a) / p) - 1;
                rational d1 = h3;
                rational d2 = std::min(h1, h2);
                rational d3 = std::min(h1, h4);
                rational d4 = std::min(h2, h4);
                rational dmax = std::max(std::max(d1, d2), std::max(d3, d4));
                return std::min(max_value - val, dmax);
            };

            if (a > b || (e->src.is_negative() && a == b)) {
                rational lo = val - delta_l(val);
                rational hi = val + delta_u(val) + 1;

                LOG("refine-disequal-lin: " << " [" << lo << ", " << hi << "[");

                SASSERT(0 <= lo && lo <= val);
                SASSERT(val <= hi && hi <= mod_value);
                if (hi == mod_value) hi = 0;
                pdd lop = s.var2pdd(v).mk_val(lo);
                pdd hip = s.var2pdd(v).mk_val(hi);
                entry* ne = alloc_entry();
                ne->refined = e;
                ne->src = e->src;
                ne->side_cond = e->side_cond;
                ne->coeff = 1;
                ne->interval = eval_interval::proper(lop, lo, hip, hi);
                intersect(v, ne);
                return false;
            }
            e = e->next();
        }
        while (e != first);
        return true;
    }

    bool viable::has_viable(pvar v) {
        refined:
        auto* e = m_units[v];

#define CHECK_RETURN(val) { if (refine_viable(v, val)) return true; else goto refined; }

        if (!e)
            CHECK_RETURN(rational::zero());
        entry* first = e;
        entry* last = e->prev();

        if (e->interval.is_full())
            return false;
        // quick check: last interval doesn't wrap around, so hi_val
        // has not been covered
        if (last->interval.lo_val() < last->interval.hi_val())
            CHECK_RETURN(last->interval.hi_val());

        do {
            if (e->interval.is_full())
                return false;
            entry* n = e->next();
            if (n == e)
                CHECK_RETURN(e->interval.hi_val());
            if (!n->interval.currently_contains(e->interval.hi_val()))
                CHECK_RETURN(e->interval.hi_val());
            if (n == first) {
                if (e->interval.lo_val() > e->interval.hi_val())
                    return false;
                CHECK_RETURN(e->interval.hi_val());
            }
            e = n;
        }
        while (e != first);
        return false;
#undef CHECK_RETURN
    }

    bool viable::is_viable(pvar v, rational const& val) {
        auto* e = m_units[v];
        if (!e)
            return refine_viable(v, val);
        entry* first = e;
        entry* last = first->prev();
        if (last->interval.currently_contains(val))
            return false;
        for (; e != last; e = e->next()) {
            if (e->interval.currently_contains(val))
                return false;
            if (val < e->interval.lo_val())
                return refine_viable(v, val);
        }
        return refine_viable(v, val);
    }

    find_t viable::find_viable(pvar v, rational& lo) {
        rational hi;
        switch (find_viable(v, lo, hi)) {
        case l_true:
            return (lo == hi) ? find_t::singleton : find_t::multiple;
        case l_false:
            return find_t::empty;
        default:
            return find_t::resource_out;
        }
    }

    lbool viable::find_viable(pvar v, rational& lo, rational& hi) {
        std::pair<rational&, rational&> args{lo, hi};
        return query<query_t::find_viable>(v, args);
    }

    lbool viable::min_viable(pvar v, rational& lo) {
        return query<query_t::min_viable>(v, lo);
    }

    lbool viable::max_viable(pvar v, rational& hi) {
        return query<query_t::max_viable>(v, hi);
    }

    bool viable::has_upper_bound(pvar v, rational& out_hi, vector<signed_constraint>& out_c) {
        entry const* first = m_units[v];
        entry const* e = first;
        bool found = false;
        out_c.reset();
        if (!e)
            return false;
        do {
            found = false;
            do {
                if (!e->refined) {
                    auto const& lo = e->interval.lo();
                    auto const& hi = e->interval.hi();
                    if (lo.is_val() && hi.is_val()) {
                        if (out_c.empty() && lo.val() > hi.val()) {
                            out_c.push_back(e->src);
                            out_hi = lo.val() - 1;
                            found = true;
                        }
                        else if (!out_c.empty() && lo.val() <= out_hi && out_hi < hi.val()) {
                            out_c.push_back(e->src);
                            out_hi = lo.val() - 1;
                            found = true;                        
                        }
                    }
                }
                e = e->next();
            }
            while (e != first);
        }
        while (found);
        return !out_c.empty();
    }

    bool viable::has_lower_bound(pvar v, rational& out_lo, vector<signed_constraint>& out_c) {
        entry const* first = m_units[v];
        entry const* e = first;
        bool found = false;
        out_c.reset();
        if (!e)
            return false;
        do {
            found = false;
            do {
                if (!e->refined) {
                    auto const& lo = e->interval.lo();
                    auto const& hi = e->interval.hi();
                    if (lo.is_val() && hi.is_val()) {
                        if (out_c.empty() && hi.val() != 0 && (lo.val() == 0 || lo.val() > hi.val())) {
                            out_c.push_back(e->src);
                            out_lo = hi.val();
                            found = true;
                        }
                        else if (!out_c.empty() && lo.val() <= out_lo && out_lo < hi.val()) {
                            out_c.push_back(e->src);
                            out_lo = hi.val();
                            found = true;
                        }
                    }
                }
                e = e->next();
            }
            while (e != first);
        }
        while (found);
        return !out_c.empty();
    }

    bool viable::has_max_forbidden(pvar v, signed_constraint const& c, rational& out_lo, rational& out_hi, vector<signed_constraint>& out_c) {
        out_c.reset();
        entry const* first = m_units[v];
        entry const* e = first;
        if (!e)
            return false;

        do {
            if (e->src == c) 
                break;
            e = e->next();
        }
        while (e != first);

        if (e->src != c)
            return false;
        entry const* e0 = e;

        do {
            entry const* n = e->next();
            while (n != e0) {
                entry const* n1 = n->next();
                if (n1 == e)
                    break;
                if (!e->interval.currently_contains(n1->interval.lo_val()))
                    if (e->interval.hi_val() != n1->interval.lo_val())
                        break;
                n = n1;
            }
            if (e == n) {
                SASSERT_EQ(e, e0);
                // VERIFY(false);
                return false;
            }

            if (e == e0) {
                out_lo = n->interval.lo_val();
                if (!n->interval.lo().is_val())
                    out_c.push_back(s.eq(n->interval.lo(), out_lo));
            }
            else if (n == e0) {
                out_hi = e->interval.hi_val();
                if (!e->interval.hi().is_val())
                    out_c.push_back(s.eq(e->interval.hi(), out_hi));
            }            
            else if (!e->interval.is_full()) {
                auto const& hi = e->interval.hi();
                auto const& next_lo = n->interval.lo();
                auto const& next_hi = n->interval.hi();
                auto lhs = hi - next_lo;
                auto rhs = next_hi - next_lo;
                signed_constraint c = s.m_constraints.ult(lhs, rhs);
                out_c.push_back(c);
            }
            if (e != e0) {
                for (auto sc : e->side_cond)
                    out_c.push_back(sc);
                out_c.push_back(e->src);
            }
            e = n;
        }
        while (e != e0);

        IF_VERBOSE(2, 
                   verbose_stream() << "has-max-forbidden " << e->src << "\n";
                   verbose_stream() << "v" << v << " " << out_lo << " " << out_hi << " " << out_c << "\n";
                   display(verbose_stream(), v) << "\n");
        return true;
    }


    template <query_t mode>
    lbool viable::query(pvar v, typename query_result<mode>::result_t& result) {
        // max number of interval refinements before falling back to the univariate solver
        unsigned const refinement_budget = 1000;
        unsigned refinements = refinement_budget;

        while (refinements--) {
            lbool res = l_undef;

            if constexpr (mode == query_t::find_viable)
                res = query_find(v, result.first, result.second);
            else if constexpr (mode == query_t::min_viable)
                res = query_min(v, result);
            else if constexpr (mode == query_t::max_viable)
                res = query_max(v, result);
            else if constexpr (mode == query_t::has_viable) {
                NOT_IMPLEMENTED_YET();
            }
            else {
                UNREACHABLE();
            }

            if (res != l_undef)
                return res;
        }

        LOG("Refinement budget exhausted! Fall back to univariate solver.");
        return query_fallback<mode>(v, result);
    }

    lbool viable::query_find(pvar v, rational& lo, rational& hi) {
        auto const& max_value = s.var2pdd(v).max_value();
        lbool const refined = l_undef;

        // After a refinement, any of the existing entries may have been replaced
        // (if it is subsumed by the new entry created during refinement).
        // For this reason, we start chasing the intervals from the start again.
        lo = 0;
        hi = max_value;

        auto* e = m_units[v];
        if (!e && !refine_viable(v, lo))
            return refined;
        if (!e && !refine_viable(v, hi))
            return refined;
        if (!e)
            return l_true;
        if (e->interval.is_full()) {
            s.set_conflict_by_viable_interval(v);
            return l_false;
        }

        entry* first = e;
        entry* last = first->prev();

        // quick check: last interval does not wrap around
        // and has space for 2 unassigned values.
        if (last->interval.lo_val() < last->interval.hi_val() &&
            last->interval.hi_val() < max_value) {
            lo = last->interval.hi_val();
            if (!refine_viable(v, lo))
                return refined;
            if (!refine_viable(v, max_value))
                return refined;
            return l_true;
        }

        // find lower bound
        if (last->interval.currently_contains(lo))
            lo = last->interval.hi_val();
        do {
            if (!e->interval.currently_contains(lo))
                break;
            lo = e->interval.hi_val();
            e = e->next();
        }
        while (e != first);

        if (e->interval.currently_contains(lo)) {
            s.set_conflict_by_viable_interval(v);
            return l_false;
        }

        // find upper bound
        hi = max_value;
        e = last;
        do {
            if (!e->interval.currently_contains(hi))
                break;
            hi = e->interval.lo_val() - 1;
            e = e->prev();
        }
        while (e != last);
        if (!refine_viable(v, lo))
            return refined;
        if (!refine_viable(v, hi))
            return refined;
        return l_true;
    }

    lbool viable::query_min(pvar v, rational& lo) {
        // TODO: should be able to deal with UNSAT case; since also min_viable has to deal with it due to fallback solver
        lo = 0;
        entry* e = m_units[v];
        if (!e && !refine_viable(v, lo))
            return l_undef;
        if (!e)
            return l_true;
        entry* first = e;
        entry* last = first->prev();
        if (last->interval.currently_contains(lo))
            lo = last->interval.hi_val();
        do {
            if (!e->interval.currently_contains(lo))
                break;
            lo = e->interval.hi_val();
            e = e->next();
        }
        while (e != first);
        if (!refine_viable(v, lo))
            return l_undef;
        SASSERT(is_viable(v, lo));
        return l_true;
    }

    lbool viable::query_max(pvar v, rational& hi) {
        // TODO: should be able to deal with UNSAT case; since also max_viable has to deal with it due to fallback solver
        hi = s.var2pdd(v).max_value();
        auto* e = m_units[v];
        if (!e && !refine_viable(v, hi))
            return l_undef;
        if (!e)
            return l_true;
        entry* last = e->prev();
        e = last;
        do {
            if (!e->interval.currently_contains(hi))
                break;
            hi = e->interval.lo_val() - 1;
            e = e->prev();
        }
        while (e != last);
        if (!refine_viable(v, hi))
            return l_undef;
        SASSERT(is_viable(v, hi));
        return l_true;
    }

    template <query_t mode>
    lbool viable::query_fallback(pvar v, typename query_result<mode>::result_t& result) {
        unsigned const bit_width = s.size(v);
        univariate_solver* us = s.m_viable_fallback.usolver(bit_width);
        sat::literal_set added;

        // First step: only query the looping constraints and see if they alone are already UNSAT.
        // The constraints which caused the refinement loop will be reached from m_units.
        LOG_H3("Checking looping univariate constraints for v" << v << "...");
        LOG("Assignment: " << assignments_pp(s));
        entry const* first = m_units[v];
        entry const* e = first;
        do {
            entry const* origin = e;
            while (origin->refined)
                origin = origin->refined;
            signed_constraint const c = origin->src;
            sat::literal const lit = c.blit();
            if (!added.contains(lit)) {
                added.insert(lit);
                LOG("Adding " << lit_pp(s, lit));
                c.add_to_univariate_solver(v, s, *us, lit.to_uint());
            }
            e = e->next();
        }
        while (e != first);

        switch (us->check()) {
        case l_false:
            s.set_conflict_by_viable_fallback(v, *us);
            return l_false;
        case l_true:
            // At this point we don't know much because we did not add all relevant constraints
            break;
        default:
            // resource limit
            return l_undef;
        }

        // Second step: looping constraints aren't UNSAT, so add the remaining relevant constraints
        LOG_H3("Checking all univariate constraints for v" << v << "...");
        auto const& cs = s.m_viable_fallback.m_constraints[v];
        for (unsigned i = cs.size(); i-- > 0; ) {
            sat::literal const lit = cs[i].blit();
            if (added.contains(lit))
                continue;
            LOG("Adding " << lit_pp(s, lit));
            added.insert(lit);
            cs[i].add_to_univariate_solver(v, s, *us, lit.to_uint());
        }

        switch (us->check()) {
        case l_false:
            s.set_conflict_by_viable_fallback(v, *us);
            return l_false;
        case l_true:
            // pass solver to mode-specific query
            break;
        default:
            // resource limit
            return l_undef;
        }

        if constexpr (mode == query_t::find_viable)
            return query_find_fallback(v, *us, result.first, result.second);

        if constexpr (mode == query_t::min_viable)
            return query_min_fallback(v, *us, result);

        if constexpr (mode == query_t::max_viable)
            return query_max_fallback(v, *us, result);

        if constexpr (mode == query_t::has_viable) {
            NOT_IMPLEMENTED_YET();
            return l_undef;
        }

        UNREACHABLE();
        return l_undef;
    }

    lbool viable::query_find_fallback(pvar v, univariate_solver& us, rational& lo, rational& hi) {
        return us.find_two(lo, hi) ? l_true : l_undef;
    }

    lbool viable::query_min_fallback(pvar v, univariate_solver& us, rational& lo) {
        return us.find_min(lo) ? l_true : l_undef;
    }

    lbool viable::query_max_fallback(pvar v, univariate_solver& us, rational& hi) {
        return us.find_max(hi) ? l_true : l_undef;
    }

    bool viable::resolve_fallback(pvar v, univariate_solver& us, conflict& core) {
        // The conflict is the unsat core of the univariate solver,
        // and the current assignment (under which the constraints are univariate in v)
        // TODO:
        // - currently we add variables directly, which is sound:
        //      e.g.:   v^2 + w^2 == 0;   w := 1
        // - but we could use side constraints on the coefficients instead (coefficients when viewed as polynomial over v):
        //      e.g.:   v^2 + w^2 == 0;   w^2 == 1
        for (unsigned dep : us.unsat_core()) {
            sat::literal lit = sat::to_literal(dep);
            signed_constraint c = s.lit2cnstr(lit);
            core.insert(c);
            core.insert_vars(c);
        }
        SASSERT(!core.vars().contains(v));
        core.add_lemma("viable unsat core", core.build_lemma());
        verbose_stream() << "unsat core " << core << "\n";
        return true;
    }

    bool viable::resolve_interval(pvar v, conflict& core) {
        DEBUG_CODE( log(v); );
        if (has_viable(v))
            return false;
        entry const* e = m_units[v];
        // TODO: in the forbidden interval paper, they start with the longest interval. We should also try that at some point.
        entry const* first = e;
        SASSERT(e);
        // If there is a full interval, all others would have been removed
        SASSERT(!e->interval.is_full() || e->next() == e);
        SASSERT(e->interval.is_full() || all_of(*e, [](entry const& f) { return !f.interval.is_full(); }));
        clause_builder lemma(s);
        do {
            // Build constraint: upper bound of each interval is not contained in the next interval,
            // using the equivalence:  t \in [l;h[  <=>  t-l < h-l
            entry const* n = e->next();

            // Choose the next interval which furthest extends the covered region.
            // Example:
            //      covered:   [-------]
            //      e:           [-------]      <--- not required for the lemma because all points are also covered by other intervals
            //      n:              [-------]
            //
            // Note that intervals are sorted by their starting points,
            // so the intervals to be considered (i.e., those that
            // contain the current endpoint), form a prefix of the list.
            //
            // Furthermore, because we remove intervals that are subsets
            // of other intervals, also the endpoints must be increasing,
            // so the last interval of this prefix is the best choice.
            //
            // current:  [------[
            // next:       [---[        <--- impossible, would have been removed.
            //
            // current:  [------[
            // next:       [-------[    <--- thus, the next interval is always the better choice.
            //
            // The interval 'first' is always part of the lemma. If we reach first again here, we have covered the complete domain.
            while (n != first) {
                entry const* n1 = n->next();
                // Check if n1 is eligible; if yes, then n1 is better than n.
                //
                // Case 1, n1 overlaps e (unless n1 == e):
                //      e:  [------[
                //      n1:      [----[
                // Case 2, n1 connects to e:
                //      e:  [------[
                //      n1:        [----[
                if (n1 == e)
                    break;
                if (!e->interval.currently_contains(n1->interval.lo_val()))
                    if (e->interval.hi_val() != n1->interval.lo_val())
                        break;
                n = n1;
            }

            // verbose_stream() << e->interval << " " << e->side_cond << " " << e->src << ";\n";

            if (!e->interval.is_full()) {
                auto const& hi = e->interval.hi();
                auto const& next_lo = n->interval.lo();
                auto const& next_hi = n->interval.hi();
                auto lhs = hi - next_lo;
                auto rhs = next_hi - next_lo;
                signed_constraint c = s.m_constraints.ult(lhs, rhs);
                lemma.insert_try_eval(~c);  // "try" because linking constraint may contain unassigned variables, see test_polysat::test_bench23_fi_lemma for an example.
            }
            for (auto sc : e->side_cond)
                lemma.insert_eval(~sc);
            lemma.insert(~e->src);
            core.insert(e->src);
            core.insert_vars(e->src);
            e = n;
        }
        while (e != first);

        // Doesn't hold anymore: we may get new constraints with unassigned variables, see test_polysat::test_bench23_fi_lemma.
        // SASSERT(all_of(lemma, [this](sat::literal lit) { return s.m_bvars.value(lit) == l_false || s.lit2cnstr(lit).is_currently_false(s); }));

        // NSB review: bench23 exposes a scenario where s.m_bvars.value(lit) == l_true. So the viable lemma is mute, but the literal in the premise
        // is a conflict.
        // SASSERT(all_of(lemma, [this](sat::literal lit) { return s.m_bvars.value(lit) != l_true; }));
        core.add_lemma("viable", lemma.build());
        core.logger().log(inf_fi(*this, v));
        return true;
    }

    void viable::log(pvar v) {
        if (!well_formed(m_units[v]))
            LOG("v" << v << " not well formed");
        auto* e = m_units[v];
        if (!e)
            return;
        entry* first = e;
        do {
            LOG("v" << v << ": " << e->interval << " " << e->side_cond << " " << e->src);
            e = e->next();
        }
        while (e != first);
    }

    void viable::log() {
        for (pvar v = 0; v < m_units.size(); ++v)
            log(v);
    }

    std::ostream& viable::display(std::ostream& out, pvar v, entry* e) const {
        if (!e)
            return out;
        entry* first = e;
        do {
            if (e->coeff != 1)
                out << e->coeff << " * v" << v << " ";
            out << e->interval << " " << e->side_cond << " " << e->src << "; ";
            e = e->next();
        }
        while (e != first);
        return out;
    }

    std::ostream& viable::display(std::ostream& out, pvar v) const {
        display(out, v, m_units[v]);
        display(out, v, m_equal_lin[v]);
        display(out, v, m_diseq_lin[v]);
        return out;
    }

    std::ostream& viable::display(std::ostream& out) const {
        for (pvar v = 0; v < m_units.size(); ++v)
            display(out << "v" << v << ": ", v) << "\n";
        return out;
    }

    /*
    * Lower bounds are strictly ascending.
    * intervals don't contain each-other (since lower bounds are ascending,
    * it suffices to check containment in one direction).
    */
    bool viable::well_formed(entry* e) {
        if (!e)
            return true;
        entry* first = e;
        while (true) {
            if (e->interval.is_full())
                return e->next() == e;
            if (e->interval.is_currently_empty())
                return false;

            auto* n = e->next();
            if (n != e && e->interval.currently_contains(n->interval))
                return false;

            if (n == first)
                break;
            if (e->interval.lo_val() >= n->interval.lo_val())
                return false;
            e = n;
        }
        return true;
    }

    //************************************************************************
    // viable_fallback
    //************************************************************************

    viable_fallback::viable_fallback(solver& s):
        s(s) {
        m_usolver_factory = mk_univariate_bitblast_factory();
    }

    void viable_fallback::push_var(unsigned bit_width) {
        m_constraints.push_back({});
    }

    void viable_fallback::pop_var() {
        m_constraints.pop_back();
    }

    void viable_fallback::push_constraint(pvar v, signed_constraint const& c) {
        // v is the only unassigned variable in c.
        SASSERT(c->vars().size() == 1 || !s.is_assigned(v));
        DEBUG_CODE(for (pvar w : c->vars()) { if (v != w) SASSERT(s.is_assigned(w)); });
        m_constraints[v].push_back(c);
        m_constraints_trail.push_back(v);
        s.m_trail.push_back(trail_instr_t::viable_constraint_i);
    }

    void viable_fallback::pop_constraint() {
        pvar v = m_constraints_trail.back();
        m_constraints_trail.pop_back();
        m_constraints[v].pop_back();
    }

    signed_constraint viable_fallback::find_violated_constraint(assignment const& a, pvar v) {
        for (signed_constraint const c : m_constraints[v]) {
            // for this check, all variables need to be assigned
            DEBUG_CODE(for (pvar w : c->vars()) { SASSERT(a.contains(w)); });
            if (c.is_currently_false(a)) {
                LOG(assignment_pp(s, v, a.value(v)) << " violates constraint " << lit_pp(s, c));
                return c;
            }
            SASSERT(c.is_currently_true(a));
        }
        return {};
    }

    univariate_solver* viable_fallback::usolver(unsigned bit_width) {
        univariate_solver* us;

        auto it = m_usolver.find_iterator(bit_width);
        if (it != m_usolver.end()) {
            us = it->m_value.get();
            us->pop(1);
        }
        else {
            auto& mk_solver = *m_usolver_factory;
            m_usolver.insert(bit_width, mk_solver(bit_width));
            us = m_usolver[bit_width].get();
        }
        SASSERT_EQ(us->scope_level(), 0);

        // push once on the empty solver so we can reset it before the next use
        us->push();

        return us;
    }

    find_t viable_fallback::find_viable(pvar v, rational& out_val) {
        unsigned const bit_width = s.m_size[v];
        univariate_solver* us = usolver(bit_width);

        auto const& cs = m_constraints[v];
        for (unsigned i = cs.size(); i-- > 0; ) {
            signed_constraint const c = cs[i];
            LOG("Univariate constraint: " << c);
            c.add_to_univariate_solver(v, s, *us, c.blit().to_uint());
        }

        switch (us->check()) {
        case l_true:
            out_val = us->model();
            // we don't know whether the SMT instance has a unique solution
            return find_t::multiple;
        case l_false:
            s.set_conflict_by_viable_fallback(v, *us);
            return find_t::empty;
        default:
            return find_t::resource_out;
        }
    }

    std::ostream& operator<<(std::ostream& out, find_t x) {
        switch (x) {
        case find_t::empty:
            return out << "empty";
        case find_t::singleton:
            return out << "singleton";
        case find_t::multiple:
            return out << "multiple";
        case find_t::resource_out:
            return out << "resource_out";
        }
        UNREACHABLE();
        return out;
    }

}

