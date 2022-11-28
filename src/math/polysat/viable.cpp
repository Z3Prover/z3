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

--*/


#include "util/debug.h"
#include "math/polysat/viable.h"
#include "math/polysat/solver.h"
#include "math/polysat/univariate/univariate_solver.h"

namespace polysat {

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
            case dd::find_t::singleton:
                propagate(v, val);
                prop = true;
                break;
            case dd::find_t::empty:
                s.set_conflict(v, false);
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
        rational const& max_value = s.var2pdd(v).max_value();
        rational mod_value = max_value + 1;

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
            LOG("refine-equal-lin for src: " << e->src);
            rational coeff_val = mod(e->coeff * val, mod_value);
            if (e->interval.currently_contains(coeff_val)) {

                if (e->interval.lo_val().is_one() && e->interval.hi_val().is_zero() && e->coeff.is_odd()) {
                    rational lo(1);
                    rational hi(0);
                    LOG("refine-equal-lin: " << " [" << lo << ", " << hi << "[");
                    pdd lop = s.var2pdd(v).mk_val(lo);
                    pdd hip = s.var2pdd(v).mk_val(hi);
                    entry* ne = alloc_entry();
                    ne->src = e->src;
                    ne->side_cond = e->side_cond;
                    ne->coeff = 1;
                    ne->interval = eval_interval::proper(lop, lo, hip, hi);
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
                LOG("forbidden interval v" << v << " " << val << " " << e->coeff << " * " << e->interval << " [" << lo << ", " << hi << "[");
                SASSERT(hi <= mod_value);
                bool full = (lo == 0 && hi == mod_value);
                if (hi == mod_value)
                    hi = 0;
                pdd lop = s.var2pdd(v).mk_val(lo);
                pdd hip = s.var2pdd(v).mk_val(hi);
                entry* ne = alloc_entry();
                ne->src = e->src;
                ne->side_cond = e->side_cond;
                ne->coeff = 1;
                if (full)
                    ne->interval = eval_interval::full();
                else
                    ne->interval = eval_interval::proper(lop, lo, hip, hi);
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


    rational viable::min_viable(pvar v) {
        refined:
        rational lo(0);
        auto* e = m_units[v];
        if (!e && !refine_viable(v, lo))
            goto refined;
        if (!e)
            return lo;
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
            goto refined;
        SASSERT(is_viable(v, lo));
        return lo;
    }

    rational viable::max_viable(pvar v) {
        refined:
        rational hi = s.var2pdd(v).max_value();
        auto* e = m_units[v];
        if (!e && !refine_viable(v, hi))
            goto refined;
        if (!e)
            return hi;
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
            goto refined;
        SASSERT(is_viable(v, hi));
        return hi;
    }

    dd::find_t viable::find_viable(pvar v, rational& lo) {
        refined:
        lo = 0;
        auto* e = m_units[v];
        if (!e && !refine_viable(v, lo))
            goto refined;
        if (!e && !refine_viable(v, rational::one()))
            goto refined;
        if (!e)
            return dd::find_t::multiple;
        if (e->interval.is_full())
            return dd::find_t::empty;

        entry* first = e;
        entry* last = first->prev();

        // quick check: last interval does not wrap around
        // and has space for 2 unassigned values.
        auto& max_value = s.var2pdd(v).max_value();
        if (last->interval.lo_val() < last->interval.hi_val() &&
            last->interval.hi_val() < max_value) {
            lo = last->interval.hi_val();
            if (!refine_viable(v, lo))
                goto refined;
            if (!refine_viable(v, max_value))
                goto refined;
            return dd::find_t::multiple;
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

        if (e->interval.currently_contains(lo))
            return dd::find_t::empty;

        // find upper bound
        rational hi = max_value;
        e = last;
        do {
            if (!e->interval.currently_contains(hi))
                break;
            hi = e->interval.lo_val() - 1;
            e = e->prev();
        }
        while (e != last);
        if (!refine_viable(v, lo))
            goto refined;
        if (!refine_viable(v, hi))
            goto refined;
        if (lo == hi)
            return dd::find_t::singleton;
        else
            return dd::find_t::multiple;
    }

    bool viable::resolve(pvar v, conflict& core) {
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

            if (!e->interval.is_full()) {
                auto const& hi = e->interval.hi();
                auto const& next_lo = n->interval.lo();
                auto const& next_hi = n->interval.hi();
                auto lhs = hi - next_lo;
                auto rhs = next_hi - next_lo;
                signed_constraint c = s.m_constraints.ult(lhs, rhs);
                lemma.insert_eval(~c);
            }
            for (auto sc : e->side_cond)
                lemma.insert_eval(~sc);
            lemma.insert(~e->src);
            core.insert(e->src);
            core.insert_vars(e->src);
            e = n;
        }
        while (e != first);

        SASSERT(all_of(lemma, [this](sat::literal lit) { return s.m_bvars.value(lit) == l_false; }));
        core.add_lemma(lemma.build());
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

    bool viable_fallback::check_constraints(pvar v) {
        for (auto const& c : m_constraints[v]) {
            // for this check, all variables need to be assigned
            DEBUG_CODE(for (pvar w : c->vars()) { SASSERT(s.is_assigned(w)); });
            if (c.is_currently_false(s)) {
                LOG(assignment_pp(s, v, s.get_value(v)) << " violates constraint " << lit_pp(s, c));
                return false;
            }
            SASSERT(c.is_currently_true(s));
        }
        return true;
    }

    dd::find_t viable_fallback::find_viable(pvar v, rational& out_val) {
        unsigned bit_width = s.m_size[v];

        univariate_solver* us;
        auto it = m_usolver.find_iterator(bit_width);
        if (it != m_usolver.end()) {
            us = it->m_value.get();
            us->pop(1);
        } else {
            auto& mk_solver = *m_usolver_factory;
            m_usolver.insert(bit_width, mk_solver(bit_width));
            us = m_usolver[bit_width].get();
        }

        // push once on the empty solver so we can reset it before the next use
        us->push();

        auto const& cs = m_constraints[v];
        for (unsigned i = cs.size(); i-- > 0; ) {
            cs[i].add_to_univariate_solver(s, *us, i);
        }

        switch (us->check()) {
        case l_true:
            out_val = us->model();
            // we don't know whether the SMT instance has a unique solution
            return dd::find_t::multiple;
        case l_false:
            return dd::find_t::empty;
        default:
            // TODO: what should we do here? (SMT solver had resource-out ==> polysat should abort too?)
            //       can we pass polysat's resource limit to the univariate solver?
            UNREACHABLE();
            return dd::find_t::empty;
        }
    }

    signed_constraints viable_fallback::unsat_core(pvar v) {
        unsigned bit_width = s.m_size[v];
        SASSERT(m_usolver[bit_width]);
        signed_constraints cs;
        for (unsigned dep : m_usolver[bit_width]->unsat_core()) {
            cs.push_back(m_constraints[v][dep]);
        }
        return cs;
    }

}

