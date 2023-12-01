/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

Notes:

TODO: Investigate in depth a notion of phase caching for variables.
The Linear solver can be used to supply a phase in some cases.
In other cases, the phase of a variable assignment across branches
might be used in a call to is_viable. With phase caching on, it may
just check if the cached phase is viable without detecting that it is a propagation.

TODO: plan to fix the FI "pumping":
    1. simple looping detection and bitblasting fallback.  -- done
    2. intervals at multiple bit widths
        - for equations, this will give us exact solutions for all coefficients
        - for inequalities, a coefficient 2^k*a means that intervals are periodic because the upper k bits of x are irrelevant;
          storing the interval for x[K-k:0] would take care of this.

--*/


#include "util/debug.h"
#include "math/polysat/viable.h"
#include "math/polysat/refine.h"
#include "math/polysat/solver.h"
#include "math/polysat/number.h"

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
        m_units.push_back({});
        m_equal_lin.push_back(nullptr);
        m_diseq_lin.push_back(nullptr);
    }

    void viable::pop_var() {
        m_units.pop_back();
        m_equal_lin.pop_back();
        m_diseq_lin.pop_back();
    }

    viable::entry* viable::alloc_entry(pvar var) {
        if (m_alloc.empty())
            return alloc(entry);
        auto* e = m_alloc.back();
        e->reset();
        e->var = var;
        m_alloc.pop_back();
        return e;
    }

    unsigned viable::size(pvar v) const {
        return s.size(v);
    }

    viable::layer& viable::layers::ensure_layer(unsigned bit_width) {
        for (unsigned i = 0; i < m_layers.size(); ++i) {
            layer& l = m_layers[i];
            if (l.bit_width == bit_width)
                return l;
            else if (l.bit_width < bit_width) {
                m_layers.push_back(layer(0));
                for (unsigned j = m_layers.size(); --j > i; )
                    m_layers[j] = m_layers[j - 1];
                m_layers[i] = layer(bit_width);
                return m_layers[i];
            }
        }
        m_layers.push_back(layer(bit_width));
        return m_layers.back();
    }

    viable::layer* viable::layers::get_layer(unsigned bit_width) {
        return const_cast<layer*>(std::as_const(*this).get_layer(bit_width));
    }

    viable::layer const* viable::layers::get_layer(unsigned bit_width) const {
        for (layer const& l : m_layers)
            if (l.bit_width == bit_width)
                return &l;
        return nullptr;
    }

    void viable::pop_viable() {
        auto const& [v, k, e] = m_trail.back();
        // display_one(verbose_stream() << "Pop entry:  ", v, e) << "\n";
        SASSERT(well_formed(m_units[v]));
        SASSERT(e->active);
        e->active = false;
        switch (k) {
        case entry_kind::unit_e:
            entry::remove_from(m_units[v].get_layer(e)->entries, e);
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
        // display_one(verbose_stream() << "Push entry: ", v, e) << "\n";
        entry*& entries = m_units[v].get_layer(e)->entries;
        SASSERT(e->prev() != e || !entries);
        SASSERT(e->prev() != e || e->next() == e);
        SASSERT(k == entry_kind::unit_e);
        SASSERT(!e->active);
        e->active = true;
        (void)k;
        SASSERT(well_formed(m_units[v]));
        if (e->prev() != e) {
            entry* pos = e->prev();
            e->init(e);
            pos->insert_after(e);
            if (e->interval.lo_val() < entries->interval.lo_val())
                entries = e;
        }
        else
            entries = e;
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
            if (s.is_conflict())
                return true;
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
        s.assign_propagate_by_viable(v, val);
    }

    bool viable::intersect(pvar v, signed_constraint const& c) {
        LOG("intersect v" << v << " in " << lit_pp(s, c));
        if (s.is_assigned(v)) {
            // this can happen e.g. for c = ovfl*(v2,v3); where intersect(pdd,pdd,signed_constraint) will try both variables.
            LOG("abort intersect because v" << v << " is already assigned");
            return false;
        }
        entry* ne = alloc_entry(v);
        if (!m_forbidden_intervals.get_interval(c, v, *ne)) {
            m_alloc.push_back(ne);
            return false;
        }
        if (ne->interval.is_currently_empty()) {
            m_alloc.push_back(ne);
            return false;
        }
        for (signed_constraint sc : ne->side_cond) {
            // side conditions must evaluate to true by definition
            VERIFY(sc.is_currently_true(s));
            switch (sc.bvalue(s)) {
            case l_false:
                // We have a bool/eval conflict with one of the side conditions.
                // This happens if the side condition was already bool-propagated, but appears in the propagation queue after c.
                // UNREACHABLE();  // since propagation now checks bool/eval conflicts before narrowing, this case should be impossible.
                // TODO: why does it still trigger?
                s.set_conflict(~sc);
                return true;
            case l_undef:
                s.assign_eval(sc.blit());
                break;
            case l_true:
                // ok
                break;
            }
            // any bool/eval conflicts should have been discovered before narrowing;
            VERIFY(sc.bvalue(s) != l_false);
            // side conditions should be eval'd
            VERIFY_EQ(sc.bvalue(s), l_true);
        }
        if (ne->coeff == 1) {
            return intersect(v, ne);
        }
        else if (ne->coeff == -1) {
            insert(ne, v, m_diseq_lin, entry_kind::diseq_e);
            return true;
        }
        else {
            unsigned const w = s.size(v);
            unsigned const k = ne->coeff.parity(w);
            // unsigned const lo_parity = ne->interval.lo_val().parity(w);
            // unsigned const hi_parity = ne->interval.hi_val().parity(w);

            // display_one(std::cerr << "try to reduce entry: ", v, ne) << "\n";
            // std::cerr << "coeff_parity " << k << " lo_parity " << lo_parity << " hi_parity " << hi_parity << "\n";

            if (k > 0 && ne->coeff.is_power_of_two()) {
                // reduction of coeff gives us a unit entry
                //
                // 2^k a x \not\in [ lo ; hi [
                //
                // new_lo = lo[w-1:k]      if lo[k-1:0] = 0
                //          lo[w-1:k] + 1  otherwise
                //
                // new_hi = hi[w-1:k]      if hi[k-1:0] = 0
                //          hi[w-1:k] + 1  otherwise
                //
                pdd const& pdd_lo = ne->interval.lo();
                pdd const& pdd_hi = ne->interval.hi();
                rational const& lo = ne->interval.lo_val();
                rational const& hi = ne->interval.hi_val();

                rational new_lo = machine_div2k(lo, k);
                if (mod2k(lo, k).is_zero())
                    ne->side_cond.push_back(  s.eq(pdd_lo * rational::power_of_two(w - k)) );
                else {
                    new_lo += 1;
                    ne->side_cond.push_back( ~s.eq(pdd_lo * rational::power_of_two(w - k)) );
                }

                rational new_hi = machine_div2k(hi, k);
                if (mod2k(hi, k).is_zero())
                    ne->side_cond.push_back(  s.eq(pdd_hi * rational::power_of_two(w - k)) );
                else {
                    new_hi += 1;
                    ne->side_cond.push_back( ~s.eq(pdd_hi * rational::power_of_two(w - k)) );
                }

                // we have to update also the pdd bounds accordingly, but it seems not worth introducing new variables for this eagerly
                //      new_lo = lo[:k]  etc.
                // TODO: for now just disable the FI-lemma if this case occurs

                if (new_lo == new_hi) {
                    // empty or full
                    // if (ne->interval.currently_contains(rational::zero()))
                    NOT_IMPLEMENTED_YET();
                }

                ne->coeff = machine_div2k(ne->coeff, k);
                ne->interval = eval_interval::proper(pdd_lo, new_lo, pdd_hi, new_hi);
                ne->bit_width -= k;
                LOG("reduced entry to unit in width " << ne->bit_width);
                return intersect(v, ne);
            }

            // TODO: later, can reduce according to shared_parity
            // unsigned const shared_parity = std::min(coeff_parity, std::min(lo_parity, hi_parity));

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
        SASSERT(!s.is_assigned(v));
        SASSERT(!ne->src.empty());
        entry*& entries = m_units[v].ensure_layer(ne->bit_width).entries;
        entry* e = entries;
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
            e->remove_from(entries, e);
            e->active = false;
        };

        if (ne->interval.is_full()) {
            while (entries)
                remove_entry(entries);
            entries = create_entry();
            return true;
        }

        if (!e)
            entries = create_entry();
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
                    if (!entries) {
                        entries = create_entry();
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
                        entries = e->prev();
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

    template <bool FORWARD>
    bool viable::refine_viable(pvar v, rational const& val, fixed_bits_info const& fbi) {
        return refine_bits<FORWARD>(v, val, fbi) && refine_equal_lin(v, val) && refine_disequal_lin(v, val);
    }

    bool viable::refine_viable(pvar v, rational const& val) {
        return refine_equal_lin(v, val) && refine_disequal_lin(v, val);
    }

    template <bool FORWARD>
    bool viable::refine_bits(pvar v, rational const& val, fixed_bits_info const& fbi) {
        entry* ne = refine_bits<FORWARD>(v, val, s.size(v), fbi);
        if (!ne)
            return true;
        intersect(v, ne);
        return false;
    }

    template <bool FORWARD>
    viable::entry* viable::refine_bits(pvar const v, rational const& val, unsigned const k, fixed_bits_info const& fbi) {
        SASSERT(k <= s.size(v));
        pdd_manager& m = s.var2pdd(v);

        entry* ne = alloc_entry(v);
        rational hi = extend_by_bits<FORWARD>(k, val, fbi, ne->src, ne->side_cond);

        if (hi == val) {
            m_alloc.push_back(ne);
            return nullptr;
        }

        // TODO: extend backwards as much as we can without introducing new justifications
        rational lo = extend_by_bits<!FORWARD>(k, val, fbi, ne->src, ne->side_cond);

        if (!FORWARD)
            swap(lo, hi);

        ne->refined = true;
        ne->coeff = 1;
        ne->bit_width = k;
        LOG("refine-bits " << (FORWARD ? "FORWARD" : "BACKWARD") << " for v" << v << " = " << val << " to [" << lo << ", " << hi << "[");
        ne->interval = eval_interval::proper(m.mk_val(lo), lo, m.mk_val(hi), hi);
        SASSERT(ne->interval.currently_contains(val));
        return ne;
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
        SASSERT(0 <= val && val <= max_value);

        // Rotate the 'first' entry, to prevent getting stuck in a refinement loop
        // with an early entry when a later entry could give a better interval.
        m_equal_lin[v] = m_equal_lin[v]->next();

        do {
            rational coeff_val = mod(e->coeff * val, mod_value);
            if (e->interval.currently_contains(coeff_val)) {
                // IF_LOGGING(
                //     verbose_stream() << "refine-equal-lin for v" << v << " in src: ";
                //     for (const auto& src : e->src)
                //         verbose_stream() << lit_pp(s, src) << "\n";
                // );
                // LOG("forbidden interval v" << v << " " << num_pp(s, v, val) << "    " << num_pp(s, v, e->coeff, true) << " * " << e->interval);

                if (mod(e->interval.hi_val() + 1, mod_value) == e->interval.lo_val()) {
                    // We have an equation:  a * v == b
                    rational const a = e->coeff;
                    rational const b = e->interval.hi_val();
                    LOG("refine-equal-lin: equation detected: " << dd::val_pp(m, a, true) << " * v" << v << " == " << dd::val_pp(m, b, false));
                    unsigned const parity_a = get_parity(a, N);
                    unsigned const parity_b = get_parity(b, N);
                    if (parity_a > parity_b) {
                        // No solution
                        LOG("refined: no solution due to parity");
                        entry* ne = alloc_entry(v);
                        ne->refined = true;
                        ne->src = e->src;
                        ne->side_cond = e->side_cond;
                        ne->coeff = 1;
                        ne->bit_width = e->bit_width;
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
                        entry* ne = alloc_entry(v);
                        ne->refined = true;
                        ne->src = e->src;
                        ne->side_cond = e->side_cond;
                        ne->coeff = 1;
                        ne->bit_width = e->bit_width;
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
                    entry* ne = alloc_entry(v);
                    ne->refined = true;
                    ne->src = e->src;
                    ne->side_cond = e->side_cond;
                    ne->coeff = 1;
                    ne->bit_width = e->bit_width;
                    ne->interval = eval_interval::proper(m.mk_val(lo), lo, m.mk_val(hi), hi);
                    SASSERT(ne->interval.currently_contains(val));
                    intersect(v, ne);
                    return false;
                }

                // TODO: special handling for the even factors of e->coeff = 2^k * a', a' odd
                //       (create one interval for v[N-k:] instead of 2^k intervals for v)

                // TODO: often, the intervals alternate between short forbidden and short allowed intervals.
                //       we should be able to handle this similarly to compute_y_bounds,
                //       and be able to represent such periodic intervals (inside safe bounds).
                //
                // compute_y_bounds calculates with inclusive upper bound, so we need to adjust argument and result accordingly.
                rational const hi_val_incl = e->interval.hi_val().is_zero() ? max_value : (e->interval.hi_val() - 1);
                auto [lo, hi] = refine_equal::compute_y_bounds(val, e->coeff, e->interval.lo_val(), hi_val_incl, mod_value);
                hi += 1;
                LOG("refined to [" << num_pp(s, v, lo) << ", " << num_pp(s, v, hi) << "[");
                // verbose_stream() << "lo=" << lo << " val=" << val << " hi=" << hi << "\n";
                if (lo <= hi) {
                    SASSERT(0 <= lo && lo <= val && val < hi && hi <= mod_value);
                } else {
                    SASSERT(0 < hi && hi < lo && lo < mod_value && (val < hi || lo <= val));
                }
                bool full = (lo == 0 && hi == mod_value);
                if (hi == mod_value)
                    hi = 0;
                entry* ne = alloc_entry(v);
                ne->refined = true;
                ne->src = e->src;
                ne->side_cond = e->side_cond;
                ne->coeff = 1;
                ne->bit_width = e->bit_width;
                if (full)
                    ne->interval = eval_interval::full();
                else
                    ne->interval = eval_interval::proper(m.mk_val(lo), lo, m.mk_val(hi), hi);
                SASSERT(ne->interval.currently_contains(val));
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
        auto& m = s.var2pdd(v);
        rational const& max_value = m.max_value();
        rational const& mod_value = m.two_to_N();
        SASSERT(0 <= val && val <= max_value);

        // Rotate the 'first' entry, to prevent getting stuck in a refinement loop
        // with an early entry when a later entry could give a better interval.
        m_diseq_lin[v] = m_diseq_lin[v]->next();

        do {
            // IF_LOGGING(
            //         verbose_stream() << "refine-disequal-lin for v" << v << " in src: ";
            //         for (const auto& src : e->src)
            //             verbose_stream() << lit_pp(s, src) << "\n";
            // );

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
            SASSERT(e->src.size() == 1);

            rational const a = mod(p * val + q_, mod_value);
            rational const b = mod(r * val + s_, mod_value);
            rational const np = mod_value - p;
            rational const nr = mod_value - r;
            int const corr = e->src[0].is_negative() ? 1 : 0;

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

            if (a > b || (e->src[0].is_negative() && a == b)) {
                rational lo = val - delta_l(val);
                rational hi = val + delta_u(val) + 1;

                LOG("refine-disequal-lin: " << " [" << lo << ", " << hi << "[");

                SASSERT(0 <= lo && lo <= val);
                SASSERT(val <= hi && hi <= mod_value);
                if (hi == mod_value) hi = 0;
                pdd lop = s.var2pdd(v).mk_val(lo);
                pdd hip = s.var2pdd(v).mk_val(hi);
                entry* ne = alloc_entry(v);
                ne->refined = true;
                ne->src = e->src;
                ne->side_cond = e->side_cond;
                ne->coeff = 1;
                ne->bit_width = e->bit_width;
                ne->interval = eval_interval::proper(lop, lo, hip, hi);
                intersect(v, ne);
                return false;
            }
            e = e->next();
        }
        while (e != first);
        return true;
    }

    // Skips all values that are not feasible w.r.t. fixed bits
    template <bool FORWARD>
    rational viable::extend_by_bits(unsigned k, rational const& bound, fixed_bits_info const& fbi, vector<signed_constraint>& src, vector<signed_constraint>& side_cond) const {
        svector<lbool> const& fixed = fbi.fixed;
        SASSERT(k <= fixed.size());

        sat::literal_set added_src;
        sat::literal_set added_side_cond;

        auto add_justification = [&](unsigned i) {
            SASSERT(!fbi.just_src[i].empty() || !fbi.just_slicing[i].empty());
            for (sat::literal lit : fbi.just_src[i]) {
                if (added_src.contains(lit))
                    continue;
                added_src.insert(lit);
                src.push_back(s.lit2cnstr(lit));
            }
            for (sat::literal lit : fbi.just_side_cond[i]) {
                if (added_side_cond.contains(lit))
                    continue;
                added_side_cond.insert(lit);
                side_cond.push_back(s.lit2cnstr(lit));
            }
            for (slicing::enode* n : fbi.just_slicing[i]) {
                s.m_slicing.explain_fixed(n, [&](sat::literal lit) {
                    if (!added_src.contains(lit)) {
                        added_src.insert(lit);
                        src.push_back(s.lit2cnstr(lit));
                    }
                }, [&](pvar v){
                    sat::literal lit = s.eq(s.var(v), s.get_value(v)).blit();
                    if (!s.m_bvars.is_assigned(lit))
                        s.assign_eval(lit);
                    if (!added_src.contains(lit)) {
                        added_src.insert(lit);
                        src.push_back(s.lit2cnstr(lit));
                    }
                });
            }
        };

        unsigned firstFail;
        for (firstFail = k; firstFail > 0; firstFail--) {
            if (fixed[firstFail - 1] != l_undef) {
                lbool current = to_lbool(bound.get_bit(firstFail - 1));
                if (current != fixed[firstFail - 1])
                    break;
            }
        }
        if (firstFail == 0)
            return bound; // the value is feasible according to fixed bits

        svector<lbool> new_bound(k);

        for (unsigned i = 0; i < firstFail; i++) {
            if (fixed[i] != l_undef) {
                SASSERT(fixed[i] == l_true || fixed[i] == l_false);
                new_bound[i] = fixed[i];
                if (i == firstFail - 1 || FORWARD != (fixed[i] == l_false))
                    add_justification(i); // Minimize number of responsible fixed bits; we only add those justifications we need for sure
            }
            else
                new_bound[i] = FORWARD ? l_false : l_true;
        }

        bool carry = fixed[firstFail - 1] == (FORWARD ? l_false : l_true);

        for (unsigned i = firstFail; i < new_bound.size(); i++) {
            if (fixed[i] == l_undef) {
                lbool current = to_lbool(bound.get_bit(i));
                if (carry) {
                    if (FORWARD) {
                        if (current == l_false) {
                            new_bound[i] = l_true;
                            carry = false;
                        }
                        else
                            new_bound[i] = l_false;
                    }
                    else {
                        if (current == l_true) {
                            new_bound[i] = l_false;
                            carry = false;
                        }
                        else
                            new_bound[i] = l_true;
                    }
                }
                else
                    new_bound[i] = current;
            }
            else {
                new_bound[i] = fixed[i];
                if (carry)
                    add_justification(i); // Again, we need this justification; if carry is false we don't need it
            }
        }
        SASSERT(!src.empty());
        if (carry) {
            // We covered everything
            /*if (FORWARD)
                return rational::power_of_two(k);
            else*/
                return rational::zero();
        }

        // TODO: Directly convert new_bound in rational?
        rational ret = rational::zero();
        for (unsigned i = new_bound.size(); i > 0; i--) {
            ret *= 2;
            SASSERT(new_bound[i - 1] != l_undef);
            ret += new_bound[i - 1] == l_true ? 1 : 0;
        }
        if (!FORWARD)
            return ret + 1;
        return ret;
    }

    // returns true iff no conflict was encountered
    bool viable::collect_bit_information(pvar v, bool add_conflict, fixed_bits_info& out_fbi) {

        pdd p = s.var(v);
        unsigned const v_sz = s.size(v);
        out_fbi.reset(v_sz);
        svector<lbool>& fixed = out_fbi.fixed;
        vector<sat::literal_vector>& just_src = out_fbi.just_src;
        vector<sat::literal_vector>& just_side_cond = out_fbi.just_side_cond;

        slicing::justified_fixed_bits_vector fbs;
        s.m_slicing.collect_fixed(v, fbs);

        for (auto const& fb : fbs) {
            LOG("slicing fixed bits: v" << v << "[" << fb.hi << ":" << fb.lo << "] = " << fb.value);
            for (unsigned i = fb.lo; i <= fb.hi; ++i) {
                SASSERT(out_fbi.just_src[i].empty());  // since we don't get overlapping ranges from collect_fixed.
                SASSERT(out_fbi.just_side_cond[i].empty());
                SASSERT(out_fbi.just_slicing[i].empty());
                out_fbi.fixed[i] = to_lbool(fb.value.get_bit(i - fb.lo));
                out_fbi.just_slicing[i].push_back(fb.just);
            }
        }

        entry* e1 = m_equal_lin[v];
        entry* e2 = m_units[v].get_entries(s.size(v));  // TODO: take other widths into account (will be done automatically by tracking fixed bits in the slicing egraph)
        entry* first = e1;
        if (!e1 && !e2)
            return true;

        clause_builder builder(s, "bit check");
        sat::literal_set added;
        vector<std::pair<entry*, trailing_bits>> postponed;

        auto add_literal = [&builder, &added](sat::literal lit) {
            if (added.contains(lit))
                return;
            added.insert(lit);
            builder.insert_eval(~lit);
        };

        auto add_literals = [&add_literal](sat::literal_vector const& lits) {
            for (sat::literal lit : lits)
                add_literal(lit);
        };

        auto add_entry = [&add_literal](entry* e) {
            for (const auto& sc : e->side_cond)
                add_literal(sc.blit());
            for (const auto& src : e->src)
                add_literal(src.blit());
        };

        auto add_slicing = [this, &add_literal](slicing::enode* n) {
            s.m_slicing.explain_fixed(n, [&](sat::literal lit) {
                add_literal(lit);
            }, [&](pvar v){
                LOG("from slicing: v" << v);
                add_literal(s.eq(s.var(v), s.get_value(v)).blit());
            });
        };

        auto add_bit_justification = [&add_literals, &add_slicing](fixed_bits_info const& fbi, unsigned i) {
            add_literals(fbi.just_src[i]);
            add_literals(fbi.just_side_cond[i]);
            for (slicing::enode* n : fbi.just_slicing[i])
                add_slicing(n);
        };

        if (e1) {
            unsigned largest_lsb = 0;
            do {
                if (e1->src.size() != 1) {
                    // We just consider the ordinary constraints and not already contracted ones
                    e1 = e1->next();
                    continue;
                }
                signed_constraint& src = e1->src[0];
                single_bit bit;
                trailing_bits lsb;
                if (src->is_ule() &&
                    simplify_clause::get_bit(s.subst(src->to_ule().lhs()), s.subst(src->to_ule().rhs()), p, bit, src.is_positive()) && p.is_var()) {
                    lbool prev = fixed[bit.position];
                    fixed[bit.position] = to_lbool(bit.positive);
                    //verbose_stream() << "Setting bit " << bit.position << " to " << bit.positive << " because of " << e->src << "\n";
                    if (prev != l_undef && fixed[bit.position] != prev) {
                        // LOG("Bit conflicting " << e1->src << " with " << just_src[bit.position][0]);  // NOTE: just_src may be empty if the justification is by slicing
                        if (add_conflict) {
                            add_bit_justification(out_fbi, bit.position);
                            add_entry(e1);
                            s.set_conflict(*builder.build());
                        }
                        return false;
                    }
                    // just override; we prefer bit constraints over parity as those are easier for subsumption to remove
                    // do we just introduce a new justification here that subsumption will remove anyway?
                    //      the only way it will not is if all bits are overwritten like this.
                    //      but in that case we basically replace one parity constraint by multiple bit constraints?
                    // verbose_stream() << "Adding bit constraint: " <<  e->src[0] << " (" << bit.position << ")\n";
                    if (prev == l_undef) {
                        out_fbi.set_just(bit.position, e1);
                    }
                }
                else if (src->is_eq() &&
                         simplify_clause::get_lsb(s.subst(src->to_ule().lhs()), s.subst(src->to_ule().rhs()), p, lsb, src.is_positive()) && p.is_var()) {
                    if (src.is_positive()) {
                        for (unsigned i = 0; i < lsb.length; i++) {
                            lbool prev = fixed[i];
                            fixed[i] = to_lbool(lsb.bits.get_bit(i));
                            if (prev == l_undef) {
                                SASSERT(just_src[i].empty());
                                out_fbi.set_just(i, e1);
                                continue;
                            }
                            if (fixed[i] != prev) {
                                // LOG("Positive parity conflicting " << e1->src << " with " << just_src[i][0]);  // NOTE: just_src may be empty if the justification is by slicing
                                if (add_conflict) {
                                    add_bit_justification(out_fbi, i);
                                    add_entry(e1);
                                    s.set_conflict(*builder.build());
                                }
                                return false;
                            }
                            // Prefer justifications from larger masks (less premises)
                            // TODO: Check that we don't override justifications coming from bit constraints
                            if (largest_lsb < lsb.length)
                                out_fbi.set_just(i, e1);
                        }
                        largest_lsb = std::max(largest_lsb, lsb.length);
                    }
                    else
                        postponed.push_back({ e1, lsb });
                }
                e1 = e1->next();
            } while(e1 != first);
        }

        // so far every bit is justified by a single constraint
        SASSERT(all_of(just_src, [](auto const& vec) { return vec.size() <= 1; }));

#if 0 // is the benefit enough?
        if (e2) {
            unsigned largest_msb = 0;
            first = e2;
            do {
                if (e2->src.size() != 1) {
                    e2 = e2->next();
                    continue;
                }
                signed_constraint& src = e2->src[0];
                leading_bits msb;
                if (src->is_ule() &&
                    simplify_clause::get_msb(s.subst(src->to_ule().lhs()), s.subst(src->to_ule().rhs()), p, msb, src.is_positive()) && p.is_var()) {
                    for (unsigned i = fixed.size() - msb.length; i < fixed.size(); i++) {
                        lbool prev = fixed[i];
                        fixed[i] = msb.positive ? l_true : l_false;
                        if (prev != l_undef) {
                            if (fixed[i] != prev) {
                                LOG("msb conflicting " << e2->src << " with " << justifications[i][0]->src);
                                if (add_conflict) {
                                    add_entry_list(justifications[i]);
                                    add_entry(e2);
                                    s.set_conflict(*builder.build());
                                }
                                return false;
                            }
                            else {
                                if (largest_msb < msb.length) {
                                    justifications[i].clear();
                                    justifications[i].push_back(e2);
                                }
                            }
                        }
                        else {
                            SASSERT(justifications[i].empty());
                            justifications[i].push_back(e2);
                        }
                    }
                    largest_msb = std::max(largest_msb, msb.length);
                }
                e2 = e2->next();
            } while(e2 != first);
        }
#endif

        // TODO: Incomplete - e.g., if we know the trailing bits are not 00 not 10 not 01 and not 11 we could also detect a conflict
        // This would require partially clause solving (worth the effort?)
        bool_vector removed(postponed.size(), false);
        bool changed;
        do { // fixed-point required?
            changed = false;
            for (unsigned j = 0; j < postponed.size(); j++) {
                if (removed[j])
                    continue;
                const auto& neg = postponed[j];
                unsigned indet = 0;
                unsigned last_indet = 0;
                unsigned i = 0;
                for (; i < neg.second.length; i++) {
                    if (fixed[i] != l_undef) {
                        if (fixed[i] != to_lbool(neg.second.bits.get_bit(i))) {
                            removed[j] = true;
                            break; // this is already satisfied
                        }
                    }
                    else {
                        indet++;
                        last_indet = i;
                    }
                }
                if (i == neg.second.length) {
                    if (indet == 0) {
                        // Already false
                        LOG("Found conflict with constraint " << neg.first->src);
                        if (add_conflict) {
                            for (unsigned k = 0; k < neg.second.length; k++)
                                add_bit_justification(out_fbi, k);
                            add_entry(neg.first);
                            s.set_conflict(*builder.build());
                        }
                        return false;
                    }
                    else if (indet == 1) {
                        // Simple BCP
                        SASSERT(just_src[last_indet].empty());
                        SASSERT(just_side_cond[last_indet].empty());
                        for (unsigned k = 0; k < neg.second.length; k++) {
                            if (k != last_indet) {
                                SASSERT(fixed[k] != l_undef);
                                out_fbi.push_from_bit(last_indet, k);
                            }
                        }
                        out_fbi.push_just(last_indet, neg.first);
                        fixed[last_indet] = neg.second.bits.get_bit(last_indet) ? l_false : l_true;
                        removed[j] = true;
                        LOG("Applying fast BCP on bit " << last_indet << " from constraint " << neg.first->src);
                        changed = true;
                    }
                }
            }
        } while(changed);

        return true;
    }

    bool viable::has_viable(pvar v) {

        fixed_bits_info fbi;

        if (!collect_bit_information(v, false, fbi))
            return false;

        refined:
        entry* e = m_units[v].get_entries(s.size(v));  // TODO: take other sizes into account

#define CHECK_RETURN(val) { if (refine_viable<true>(v, val, fbi)) return true; else goto refined; }
        // return refine_viable(v, val) ? l_true : l_undef;

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

        fixed_bits_info fbi;

        if (!collect_bit_information(v, false, fbi))
            return false;
        entry* e = m_units[v].get_entries(s.size(v));  // TODO: take other sizes into account
        if (!e)
            return refine_viable<true>(v, val, fbi);
        entry* first = e;
        entry* last = first->prev();
        if (last->interval.currently_contains(val))
            return false;
        for (; e != last; e = e->next()) {
            if (e->interval.currently_contains(val))
                return false;
            if (val < e->interval.lo_val())
                return refine_viable<true>(v, val, fbi);
        }
        return refine_viable<true>(v, val, fbi);
    }

    find_t viable::find_viable(pvar v, rational& lo) {
        rational hi;
        switch (find_viable2(v, lo, hi)) {
        case l_true:
            if (hi < 0) {
                // fallback solver, treat propagations as decisions for now
                // (this is because the propagation justification currently always uses intervals, which is unsound in this case)
                return find_t::multiple;
            }
            return (lo == hi) ? find_t::singleton : find_t::multiple;
        case l_false:
            return find_t::empty;
        default:
            return find_t::resource_out;
        }
    }

    bool viable::has_upper_bound(pvar v, rational& out_hi, vector<signed_constraint>& out_c) {
        entry const* first = m_units[v].get_entries(s.size(v));  // TODO: take other sizes into account
        entry const* e = first;
        bool found = false;
        out_c.reset();
        if (!e)
            return false;
        do {
            found = false;
            do {
                if (!e->refined && e->side_cond.empty()) {
                    auto const& lo = e->interval.lo();
                    auto const& hi = e->interval.hi();
                    if (lo.is_val() && hi.is_val()) {
                        if (out_c.empty() && lo.val() > hi.val()) {
                            for (signed_constraint src : e->src)
                                out_c.push_back(src);
                            out_hi = lo.val() - 1;
                            found = true;
                        }
                        else if (!out_c.empty() && lo.val() <= out_hi && out_hi < hi.val()) {
                            for (signed_constraint src : e->src)
                                out_c.push_back(src);
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
        entry const* first = m_units[v].get_entries(s.size(v));  // TODO: take other sizes into account
        entry const* e = first;
        bool found = false;
        out_c.reset();
        if (!e)
            return false;
        do {
            found = false;
            do {
                if (!e->refined && e->side_cond.empty()) {
                    auto const& lo = e->interval.lo();
                    auto const& hi = e->interval.hi();
                    if (lo.is_val() && hi.is_val()) {
                        if (out_c.empty() && hi.val() != 0 && (lo.val() == 0 || lo.val() > hi.val())) {
                            for (signed_constraint src : e->src)
                                out_c.push_back(src);
                            out_lo = hi.val();
                            found = true;
                        }
                        else if (!out_c.empty() && lo.val() <= out_lo && out_lo < hi.val()) {
                            for (signed_constraint src : e->src)
                                out_c.push_back(src);
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
        // TODO:
        // - skip intervals adjacent to c's interval if they contain side conditions on y?
        //      constraints over y are allowed if level(c) < level(y) (e.g., boolean propagated)

        out_c.reset();
        entry const* first = m_units[v].get_entries(s.size(v));  // TODO: take other sizes into account
        entry const* e = first;
        if (!e)
            return false;

        bool found = false;

        do {
            found = e->src.contains(c);
            if (found)
                break;
            e = e->next();
        }
        while (e != first);

        if (!found)
            return false;
        entry const* e0 = e;

        if (e0->interval.is_full())
            return false;

        entry const* e0_prev = nullptr;
        entry const* e0_next = nullptr;

        do {
            entry const* n = e->next();
            while (n != e0) {
                entry const* n1 = n->next();
                if (n1 == e)
                    break;
                if (!n1->interval.currently_contains(e->interval.hi_val()))
                    break;
                n = n1;
            }
            if (e == n) {
                VERIFY_EQ(e, e0);
                return false;
            }
            if (!n->interval.currently_contains(e->interval.hi_val()))
                return false;  // gap
            if (e == e0) {
                e0_next = n;
                out_lo = n->interval.lo_val();
            }
            else if (n == e0) {
                e0_prev = e;
                out_hi = e->interval.hi_val();
            }
            else if (e->src.contains(c)) {
                // multiple intervals from the same constraint c
                // TODO: adjacent intervals would fine but they should be merged at insertion instead of considering them here.
                return false;
            }
            else {
                VERIFY(!e->interval.is_full());  // if e were full then there would be no e0
                signed_constraint c = s.m_constraints.elem(e->interval.hi(), n->interval.symbolic());
                out_c.push_back(c);
            }
            if (e != e0) {
                for (signed_constraint sc : e->side_cond)
                    out_c.push_back(sc);
                for (signed_constraint src : e->src)
                    out_c.push_back(src);
            }
            e = n;
        }
        while (e != e0);

        // Other intervals fully cover c's interval, e.g.:
        //              [---------[          e0 from c
        //         [---------[               e0_prev
        //                 [-------------[   e0_next
        if (e0_next->interval.currently_contains(e0_prev->interval.hi_val()))
            return false;

        // Conclusion:
        // v \not\in [out_lo; out_hi[, or equivalently
        // v \in [out_hi; out_lo[

        auto& m = s.var2pdd(v);

        // To justify the endpoints, pretend that instead of e0 (coming from constraint c) we have the interval [out_hi; out_lo[.
        out_c.push_back(s.m_constraints.elem(e0_prev->interval.hi(), m.mk_val(out_hi), m.mk_val(out_lo)));
        out_c.push_back(s.m_constraints.elem(m.mk_val(out_lo), e0_next->interval.symbolic()));

        IF_VERBOSE(2,
                   verbose_stream() << "has-max-forbidden " << e->src << "\n";
                   verbose_stream() << "v" << v << " " << out_lo << " " << out_hi << " " << out_c << "\n";
                   display(verbose_stream(), v) << "\n");
        return true;
    }



    // When iterating over intervals:
    // - instead of only intervals of v, go over intervals of each entry of overlaps
    // - need a function to map interval from overlap into an interval over v
    //
    // Maybe combine only the "simple" overlaps in this method, and do the more comprehensive queries on demand, during conflict resolution (saturation.cpp).
    // Here, we should handle at least:
    // - direct equivalences (x = y); could just point one interval set to the other and store them together (may be annoying for bookkeeping)
    // - lower bits extractions (x[h:0]) and equivalent slices;
    //   (this is what Algorithm 3 in "Solving Bitvectors with MCSAT" does, and will also let us better handle even coefficients of inequalities).
    // - intervals with coefficient 2^k*a to be treated as intervals over x[|x|-k:0] with coefficient a (with odd a)
    //
    // Problem:
    // - the conflict clause will involve relations between different bit-widths
    // - can we avoid introducing new extract-terms? (if not, can we at least avoid additional slices?)
    //       e.g., multiply other terms by 2^k instead of introducing extract?
    // - NOTE: currently our clauses survive across backtracking points, but the slicing will be reset.
    //         It is currently unsafe to create extract/concat terms internally.
    //         (to be fixed when we re-internalize conflict clauses after backtracking)
    //
    // Problem:
    // - we want to iterate intervals in order. do we then need to perform the mapping in advance? (monotonic mapping -> only first one needs to be mapped in advance)
    // - should have some "cursor" class which abstracts the prev/next operation.
    //
    // (in addition to slices, some intervals may transfer by other operations. e.g. x = -y. but maybe it's better to handle these cases on demand by saturation.cpp)
    //
    // Refinement:
    // - is done when we find a "feasible" point, so not directly affected by changes to the algorithm.
    // - we don't know which constraint yields the "best" interval, so keep interleaving constraints
    //
    // one could also try starting at the smallest bit-width to detect conflicts faster.
    // question: how to do recursion "upwards" without exponentially many holes to fill?
    //
    // Mapping intervals (by example):
    //
    // A) Removing/appending LSB:
    //
    //      easy enough on numerals (have to be careful with rounding);
    //      using in conflict clause will probably involve new extract-terms...
    //
    //          x[6:0] \not\in [15;30[
    //      ==> x[6:1] \not\in [8;15[
    //      ==> x[6:2] \not\in [4;7[
    //
    //          x[6:2] \not\in [3;7[
    //      ==> x[6:1] \not\in [6;14[
    //      ==> x[6:0] \not\in [12;28[
    //
    // B) Removing/appending MSB:
    //
    //      When appending to the MSB, we get exponentially many copies
    //      of the interval because the upper bits are arbitrary.
    //      This is why the algorithm should support this case directly (i.e., lower-bits extractions of the query variable).
    //
    //          x[4:0] \not\in [3;7[
    //      ==> x[5:0] \not\in [3;7[ + 2^4 {0,1}
    //      ==> x[6:0] \not\in [3;7[ + 2^4 {0,1,2,3}
    //
    //      When shorting from the MSB side, we may not get an interval at all,
    //      because the bit-patterns of the remaining (lower) bits are allowed in another part of the domain.
    //
    //          x[6:0] \not\in [15;30[
    //      ==> x[5:0] \not\in \emptyset
    //
    //
    //
    //
    //
    // start covering on the highest level.
    // - at first, use a low refinement budget: we do not want to get stuck in a refinement loop if lower-bits intervals may already cover everything.
    //
    // - if we can cover everything except a hole of size < 2^{bits of next layer}
    //      - recursively try to cover that hole on lower level
    // - otherwise
    //      - recursively try to cover the whole domain on lower level
    //
    // - if the lower level succeeds, we are done.
    // - if the lower level does not succeed, we can try refinement with a higher budget.
    //
    // - each level may have:
    //   a) intervals (an entry in layers)
    //   b) a fixed top-level bit, i.e., interval that covers half of the area
    //      -- (question: is it useful to consider here already lower-level bits too? or keep it to one bit per layer for simplicity)
    //          maybe we take lower bits into account. but only use bits if we have the highest bit on this level fixed,
    //          i.e., we have a fixed-bit interval that covers half of the area. then extend that interval based on lower bits.
    //          whether this is useful I'm not sure but it could skip some "virtual layers" where we only have a bit but no intervals.
    //
    // - how to integrate fallback solver?
    //   when lowest level fails, we can try more refinement there.
    //   in case of refinement loop, try fallback solver with constraints only from lower level.
    lbool viable::find_viable2_new(pvar v, rational& lo, rational& hi) {
        fixed_bits_info fbi;

        if (!collect_bit_information(v, true, fbi))
            return l_false;  // conflict already added

        pvar_vector overlaps;
        s.m_slicing.collect_simple_overlaps(v, overlaps);
        std::sort(overlaps.begin(), overlaps.end(), [&](pvar x, pvar y) { return s.size(x) > s.size(y); });

        uint_set widths_set;
        // max size should always be present, regardless of whether we have intervals there (to make sure all fixed bits are considered)
        widths_set.insert(s.size(v));

        LOG("Overlaps with v" << v << ":");
        for (pvar x : overlaps) {
            unsigned hi, lo;
            if (s.m_slicing.is_extract(x, v, hi, lo))
                LOG("    v" << x << " = v" << v << "[" << hi << ":" << lo << "]");
            else
                LOG("    v" << x << " not extracted from v" << v << "; size " << s.size(x));
            for (layer const& l : m_units[x].get_layers()) {
                widths_set.insert(l.bit_width);
            }
        }

        unsigned_vector widths;
        for (unsigned w : widths_set) {
            widths.push_back(w);
        }
        LOG("widths: " << widths);

        rational const& max_value = s.var2pdd(v).max_value();

        lbool result_lo = find_on_layers(v, widths, overlaps, fbi, rational::zero(), max_value, lo);
        if (result_lo == l_false)
            return l_false;  // conflict
        if (result_lo == l_undef)
            return find_viable_fallback(v, overlaps, lo, hi);

        if (lo == max_value) {
            hi = lo;
            return l_true;
        }

        lbool result_hi = find_on_layers(v, widths, overlaps, fbi, lo + 1, max_value, hi);
        if (result_hi == l_false)
            hi = lo;  // no other viable value
        if (result_hi == l_undef)
            return find_viable_fallback(v, overlaps, lo, hi);

        return l_true;
    }

    // Find interval that contains 'val', or, if no such interval exists, the first interval after 'val'.
    // The bool component indicates whether the returned interval contains 'val'.
    std::pair<viable::entry*, bool> viable::find_value(rational const& val, entry* entries) {
        SASSERT(entries);
        // display_all(std::cerr << "entries:\n\t", 0, entries, "\n\t");
        entry* const first = entries;
        entry* e = entries;
        do {
            if (e->interval.currently_contains(val))
                return {e, true};
            entry* const n = e->next();
            // there is only one interval, and it does not contain 'val'
            if (e == n)
                return {e, false};
            // check whether 'val' is contained in the gap between e and n
            bool const overlapping = e->interval.currently_contains(n->interval.lo_val());
            if (!overlapping && r_interval::contains(e->interval.hi_val(), n->interval.lo_val(), val))
                return {n, false};
            e = n;
        } while (e != first);
        UNREACHABLE();
        return {nullptr, false};
    }

    // l_true ... found viable value
    // l_false ... no viable value in [to_cover_lo;to_cover_hi[
    // l_undef ... out of resources
    lbool viable::find_on_layers(
        pvar const v,
        unsigned_vector const& widths,
        pvar_vector const& overlaps,
        fixed_bits_info const& fbi,
        rational const& to_cover_lo,
        rational const& to_cover_hi,
        rational& val
    ) {
        ptr_vector<entry> refine_todo;
        ptr_vector<entry> relevant_entries;

        // max number of interval refinements before falling back to the univariate solver
        unsigned const refinement_budget = 100;
        unsigned refinements = refinement_budget;

        while (refinements--) {
            relevant_entries.clear();
            lbool result = find_on_layer(v, widths.size() - 1, widths, overlaps, fbi, to_cover_lo, to_cover_hi, val, refine_todo, relevant_entries);

            // store bit-intervals we have used
            for (entry* e : refine_todo)
                intersect(v, e);
            refine_todo.clear();

            if (result != l_true)
                return l_false;

            // overlaps are sorted by variable size in descending order
            // start refinement on smallest variable
            // however, we probably should rotate to avoid getting stuck in refinement loop on a 'bad' constraint
            bool refined = false;
            for (unsigned i = overlaps.size(); i-- > 0; ) {
                pvar x = overlaps[i];
                rational const& mod_value = s.var2pdd(x).two_to_N();
                rational x_val = mod(val, mod_value);
                if (!refine_viable(x, x_val)) {
                    refined = true;
                    break;
                }
            }

            if (!refined)
                return l_true;
        }

        LOG("Refinement budget exhausted! Fall back to univariate solver.");
        return l_undef;
    }

    // find viable values in half-open interval [to_cover_lo;to_cover_hi[ w.r.t. unit intervals on the given layer
    //
    // Returns:
    // - l_true  ... found value that is viable w.r.t. units and fixed bits
    // - l_false ... found conflict
    // - l_undef ... found no viable value in target interval [to_cover_lo;to_cover_hi[
    lbool viable::find_on_layer(
        pvar const v,
        unsigned const w_idx,
        unsigned_vector const& widths,
        pvar_vector const& overlaps,
        fixed_bits_info const& fbi,
        rational const& to_cover_lo,
        rational const& to_cover_hi,
        rational& val,
        ptr_vector<entry>& refine_todo,
        ptr_vector<entry>& relevant_entries
    ) {
        unsigned const w = widths[w_idx];
        rational const& mod_value = rational::power_of_two(w);

        LOG("layer " << w << " bits, to_cover: [" << to_cover_lo << "; " << to_cover_hi << "[");
        SASSERT(0 <= to_cover_lo);
        SASSERT(0 <= to_cover_hi);
        SASSERT(to_cover_lo < mod_value);
        SASSERT(to_cover_hi <= mod_value);  // full interval if to_cover_hi == mod_value
        SASSERT(to_cover_lo != to_cover_hi);  // non-empty search domain (but it may wrap)

        // TODO: refinement of eq/diseq should happen only on the correct layer: where (one of) the coefficient(s) are odd
        //       for refinement, we have to choose an entry that is violated, but if there are multiple, we can choose the one on smallest domain (lowest bit-width).
        //       (by maintaining descending order by bit-width; and refine first that fails).
        // but fixed-bit-refinement is cheap and could be done during the search.

        // when we arrive at a hole the possibilities are:
        // 1) go to lower bitwidth
        // 2) refinement of some eq/diseq constraint (if one is violated at that point)  -- defer this until point is viable for all layers and fixed bits.
        // 3) refinement by using bit constraints?  -- TODO: do this during search (another interval check after/before the entry_cursors)
        // 4) (point is actually feasible)

        // a complication is that we have to iterate over multiple lists of intervals.
        // might be useful to merge them upfront to simplify the remainder of the algorithm?
        // (non-trivial since prev/next pointers are embedded into entries and lists are updated by refinement)
        struct entry_cursor {
            entry* cur;
            // entry* first;
            // entry* last;
        };

        // find relevant interval lists
        svector<entry_cursor> ecs;
        for (pvar x : overlaps) {
            if (s.size(x) < w)  // note that overlaps are sorted by variable size descending
                break;
            if (entry* e = m_units[x].get_entries(w)) {
                display_all(std::cerr << "units for width " << w << ":\n", 0, e, "\n");
                entry_cursor ec;
                ec.cur = e;
                // ec.first = nullptr;
                // ec.last = nullptr;
                ecs.push_back(ec);
            }
        }

        rational const to_cover_len = r_interval::len(to_cover_lo, to_cover_hi, mod_value);
        val = to_cover_lo;

        rational progress; // = 0
        while (true) {
            while (true) {
                entry* e = nullptr;

                // try to make progress using any of the relevant interval lists
                for (entry_cursor& ec : ecs) {
                    // advance until current value 'val'
                    auto const [n, n_contains_val] = find_value(val, ec.cur);
                    // display_one(std::cerr << "found entry n: ", 0, n) << "\n";
                    // LOG("n_contains_val: " << n_contains_val << "    val = " << val);
                    ec.cur = n;
                    if (n_contains_val) {
                        e = n;
                        break;
                    }
                }

                // when we cannot make progress by existing intervals any more, try interval from fixed bits
                if (!e) {
                    e = refine_bits<true>(v, val, w, fbi);
                    if (e) {
                        refine_todo.push_back(e);
                        display_one(std::cerr << "found entry by bits: ", 0, e) << "\n";
                    }
                }

                // no more progress on current layer
                if (!e)
                    break;

                relevant_entries.push_back(e);

                if (e->interval.is_full())
                    return l_false;

                SASSERT(e->interval.currently_contains(val));
                rational const& new_val = e->interval.hi_val();
                rational const dist = distance(val, new_val, mod_value);
                SASSERT(dist > 0);
                val = new_val;
                progress += dist;
                LOG("val: " << val << " progress: " << progress);

                if (progress >= mod_value) {
                    // covered the whole domain => conflict
                    return l_false;
                }
                if (progress >= to_cover_len) {
                    // we covered the hole left at larger bit-width
                    // TODO: maybe we want to keep trying a bit longer to see if we can cover the whole domain. or maybe only if we enter this layer multiple times.
                    return l_undef;
                }

                // (another way to compute 'progress')
                SASSERT_EQ(progress, distance(to_cover_lo, val, mod_value));
            }

            // no more progress
            // => 'val' is viable w.r.t. unit intervals until current layer

            if (!w_idx) {
                // we are at the lowest layer
                // => found viable value w.r.t. unit intervals and fixed bits
                return l_true;
            }

            // find next covered value
            rational next_val = to_cover_hi;
            for (entry_cursor& ec : ecs) {
                // each ec.cur is now the next interval after 'lo'
                rational const& n = ec.cur->interval.lo_val();
                SASSERT(r_interval::contains(ec.cur->prev()->interval.hi_val(), n, val));
                if (distance(val, n, mod_value) < distance(val, next_val, mod_value))
                    next_val = n;
            }
            if (entry* e = refine_bits<false>(v, next_val, w, fbi)) {
                refine_todo.push_back(e);
                rational const& n = e->interval.lo_val();
                SASSERT(distance(val, n, mod_value) < distance(val, next_val, mod_value));
                next_val = n;
            }
            SASSERT(!refine_bits<true>(v, val, w, fbi));
            SASSERT(val != next_val);

            unsigned const lower_w = widths[w_idx - 1];
            rational const lower_mod_value = rational::power_of_two(lower_w);

            rational lower_cover_lo, lower_cover_hi;
            if (distance(val, next_val, mod_value) >= lower_mod_value) {
                // NOTE: in this case we do not get the first viable value, but the one with smallest value in the lower bits.
                //       this is because we start the search in the recursive case at 0.
                //       if this is a problem, adapt to lower_cover_lo = mod(val, lower_mod_value), lower_cover_hi = ...
                lower_cover_lo = 0;
                lower_cover_hi = lower_mod_value;
                rational a;
                lbool result = find_on_layer(v, w_idx - 1, widths, overlaps, fbi, lower_cover_lo, lower_cover_hi, a, refine_todo, relevant_entries);
                VERIFY(result != l_undef);
                if (result == l_false)
                    return l_false;  // conflict
                SASSERT(result == l_true);
                // replace lower bits of 'val' by 'a'
                rational const val_lower = mod(val, lower_mod_value);
                val = val - val_lower + a;
                if (a < val_lower)
                    a += lower_mod_value;
                LOG("distance(val,      cover_hi) = " << distance(val, to_cover_hi, mod_value));
                LOG("distance(next_val, cover_hi) = " << distance(next_val, to_cover_hi, mod_value));
                SASSERT(distance(val, to_cover_hi, mod_value) >= distance(next_val, to_cover_hi, mod_value));
                return l_true;
            }

            lower_cover_lo = mod(val, lower_mod_value);
            lower_cover_hi = mod(next_val, lower_mod_value);

            rational a;
            lbool result = find_on_layer(v, w_idx - 1, widths, overlaps, fbi, lower_cover_lo, lower_cover_hi, a, refine_todo, relevant_entries);
            if (result == l_false)
                return l_false;  // conflict

            // replace lower bits of 'val' by 'a'
            rational const dist = distance(lower_cover_lo, a, lower_mod_value);
            val += dist;
            progress += dist;
            LOG("distance(val,      cover_hi) = " << distance(val, to_cover_hi, mod_value));
            LOG("distance(next_val, cover_hi) = " << distance(next_val, to_cover_hi, mod_value));
            SASSERT(distance(val, to_cover_hi, mod_value) >= distance(next_val, to_cover_hi, mod_value));

            if (result == l_true)
                return l_true;  // done

            SASSERT(result == l_undef);

            if (progress >= mod_value) {
                // covered the whole domain => conflict
                return l_false;
            }

            if (progress >= to_cover_len) {
                // we covered the hole left at larger bit-width
                return l_undef;
            }
        }
        UNREACHABLE();
        return l_undef;
    }

    lbool viable::find_viable_fallback(pvar v, pvar_vector const& overlaps, rational& lo, rational& hi) {
        unsigned const bit_width = s.size(v);
        univariate_solver* us = s.m_viable_fallback.usolver(bit_width);
        sat::literal_set added;
        svector<std::pair<pvar, sat::literal>> deps;

        // First step: only query the looping constraints and see if they alone are already UNSAT.
        // The constraints which caused the refinement loop can always be reached from m_units.
        LOG_H3("Checking looping univariate constraints for v" << v << "...");
        LOG("Assignment: " << assignments_pp(s));
        for (pvar x : overlaps) {
            for (layer const& l : m_units[x].get_layers()) {
                unsigned const k = l.bit_width;
                entry const* first = l.entries;
                entry const* e = first;
                do {
                    // in the first step we're only interested in entries from refinement
                    if (e->refined) {
                        for (signed_constraint const src : e->src) {
                            sat::literal const lit = src.blit();
                            if (!added.contains(lit)) {
                                added.insert(lit);
                                LOG("Adding " << lit_pp(s, lit));
                                IF_VERBOSE(10, verbose_stream() << ";; " << lit_pp(s, lit) << "\n");
                                unsigned d = deps.size();
                                deps.push_back({x, lit});
                                src.add_to_univariate_solver(x, s, *us, d);
                            }
                        }
                    }
                    e = e->next();
                }
                while (e != first);
            }
        }

        switch (us->check()) {
        case l_false:
            set_conflict_by_fallback(v, *us, deps);
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
        for (pvar x : overlaps) {
            auto const& cs = s.m_viable_fallback.m_constraints[x];
            for (unsigned i = cs.size(); i-- > 0; ) {
                sat::literal const lit = cs[i].blit();
                if (added.contains(lit))
                    continue;
                LOG("Adding " << lit_pp(s, lit));
                IF_VERBOSE(10, verbose_stream() << ";; " << lit_pp(s, lit) << "\n");
                added.insert(lit);
                unsigned d = deps.size();
                deps.push_back({x, lit});
                cs[i].add_to_univariate_solver(x, s, *us, d);
            }
        }

        switch (us->check()) {
        case l_false:
            set_conflict_by_fallback(v, *us, deps);
            return l_false;
        case l_true:
            lo = us->model();
            hi = -1;
            return l_true;
            // TODO: return us.find_two(lo, hi) ? l_true : l_undef;  ???
        default:
            // resource limit
            return l_undef;
        }
    }

    lbool viable::find_viable2(pvar v, rational& lo, rational& hi) {

        fixed_bits_info fbi;

        if (!collect_bit_information(v, true, fbi))
            return l_false; // conflict already added

        // max number of interval refinements before falling back to the univariate solver
        unsigned const refinement_budget = 1000;
        unsigned refinements = refinement_budget;

        while (refinements--) {
            lbool res = query_find(v, lo, hi, fbi);
            IF_VERBOSE(10, {
                if (refinements % 100 == 0)
                    verbose_stream() << "Refinements " << refinements << "\n";
            });
            if (res != l_undef)
                return res;
        }
        IF_VERBOSE(10, verbose_stream() << "Fallback\n";);
        LOG("Refinement budget exhausted! Fall back to univariate solver.");

        pvar_vector overlaps;
        overlaps.push_back(v);
        return find_viable_fallback(v, overlaps, lo, hi);
    }

    lbool viable::query_find(pvar v, rational& lo, rational& hi, fixed_bits_info const& fbi) {
        auto const& max_value = s.var2pdd(v).max_value();
        lbool const refined = l_undef;

        // After a refinement, any of the existing entries may have been replaced
        // (if it is subsumed by the new entry created during refinement).
        // For this reason, we start chasing the intervals from the start again.
        lo = 0;
        hi = max_value;

        entry* e = m_units[v].get_entries(s.size(v));  // TODO: take other sizes into account
        if (!e && !refine_viable<true>(v, lo, fbi))
            return refined;
        if (!e && !refine_viable<false>(v, hi, fbi))
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
            if (!refine_viable<true>(v, lo, fbi))
                return refined;
            if (!refine_viable<false>(v, max_value, fbi))
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

        // TODO: we could also try to continue the search at lo+1, if we get stuck at the upper bound.

        // TODO: we only need (any) 2 viable values. some possibilities:
        // - find lower and upper bound
        // - find lower bound and next lowest value
        // - find upper bound and next highest value
        // - try a random sample and chase value from there

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

        if (!refine_viable<true>(v, lo, fbi))
            return refined;
        if (!refine_viable<false>(v, hi, fbi))
            return refined;
        return l_true;
    }

    bool viable::set_conflict_by_fallback(pvar v, univariate_solver& us, svector<std::pair<pvar, sat::literal>> const& deps) {
        auto& core = s.m_conflict;
        core.init_viable_fallback_begin(v);
        // The conflict is the unsat core of the univariate solver,
        // and the current assignment (under which the constraints are univariate in v)
        // TODO:
        // - currently we add variables directly, which is sound:
        //      e.g.:   v^2 + w^2 == 0;   w := 1
        // - but we could use side constraints on the coefficients instead (coefficients when viewed as polynomial over v):
        //      e.g.:   v^2 + w^2 == 0;   w^2 == 1
        uint_set to_explain;
        for (unsigned d : us.unsat_core()) {
            auto [x, lit] = deps[d];
            if (x != v)
                to_explain.insert(x);
            signed_constraint c = s.lit2cnstr(lit);
            core.insert(c);
            core.insert_vars(c);
        }
        for (pvar x : to_explain) {
            s.m_slicing.explain_simple_overlap(v, x, [this, &core](sat::literal l) {
                core.insert(s.lit2cnstr(l));
            });
        }
        SASSERT(!core.vars().contains(v));
        core.add_lemma("viable unsat core", core.build_lemma());
        IF_VERBOSE(10, verbose_stream() << "unsat core " << core << "\n";);
        core.init_viable_fallback_end(v);
        return true;
    }

    bool viable::resolve_interval(pvar v, conflict& core) {
        DEBUG_CODE( log(v); );
        VERIFY(!has_viable(v));  // does a pass over interval refinement, making sure the intervals actually exist

        entry const* e = m_units[v].get_entries(s.size(v));  // TODO: take other sizes into account
        // TODO: in the forbidden interval paper, they start with the longest interval. We should also try that at some point.
        entry const* first = e;
        SASSERT(e);
        // If there is a full interval, all others would have been removed
        clause_builder lemma(s);
        if (first->interval.is_full()) {
            SASSERT(first->next() == first);
            for (auto sc : first->side_cond)
                lemma.insert_eval(~sc);
            for (const auto& src : first->src) {
                lemma.insert(~src);
                core.insert(src);
                core.insert_vars(src);
            }
            core.add_lemma("viable", lemma.build());
            core.logger().log(inf_fi(*this, v));
            return true;
        }

        SASSERT(all_of(*first, [](entry const& f) { return !f.interval.is_full(); }));

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
                if (!n1->interval.currently_contains(e->interval.hi_val()))
                    break;
                n = n1;
            }

            signed_constraint c = s.m_constraints.elem(e->interval.hi(), n->interval.symbolic());
            // lemma.insert_try_eval(~c);
            VERIFY(c.is_currently_true(s));
            if (c.bvalue(s) == l_false) {
                core.reset();
                core.init(~c);
                return false;
            }
            lemma.insert_eval(~c);

            for (auto sc : e->side_cond)
                lemma.insert_eval(~sc);
            for (const auto& src : e->src) {
                lemma.insert(~src);
                core.insert(src);
                core.insert_vars(src);
            }
            e = n;
        }
        while (e != first);

        // verbose_stream() << "viable lemma:\n";
        // for (auto lit : lemma)
        //     verbose_stream() << "    " << lit_pp(s, lit) << "\n";
        VERIFY(all_of(lemma, [this](sat::literal lit) { return s.m_bvars.value(lit) != l_true; }));

        core.add_lemma("viable", lemma.build());
        core.logger().log(inf_fi(*this, v));
        return true;
    }

    void viable::log(pvar v) {
#if 0
        if (!well_formed(m_units[v]))
            LOG("v" << v << " not well formed");
        auto* e = m_units[v];
        if (!e)
            return;
        entry* first = e;
        do {
            IF_LOGGING(
                    verbose_stream() << "v" << v << ": " << e->interval << " " << e->side_cond << " ";
                    for (const auto& src : e->src)
                        verbose_stream() << src << " ";
                    verbose_stream() << "\n";
            );
            e = e->next();
        }
        while (e != first);
#endif
    }

    void viable::log() {
        for (pvar v = 0; v < m_units.size(); ++v)
            log(v);
    }

    std::ostream& viable::display_one(std::ostream& out, pvar v, entry const* e) const {
        auto& m = s.var2pdd(v);
        if (e->coeff == -1) {
            //      p*val + q >  r*val + s  if e->src.is_positive()
            //      p*val + q >= r*val + s  if e->src.is_negative()
            // Note that e->interval is meaningless in this case,
            // we just use it to transport the values p,q,r,s
            rational const& p = e->interval.lo_val();
            rational const& q_ = e->interval.lo().val();
            rational const& r = e->interval.hi_val();
            rational const& s_ = e->interval.hi().val();
            out << "[ ";
            out << val_pp(m, p, true) << "*v" << v << " + " << val_pp(m, q_);
            out << (e->src[0].is_positive() ? " > " : " >= ");
            out << val_pp(m, r, true) << "*v" << v << " + " << val_pp(m, s_);
            out << " ] ";
        }
        else if (e->coeff != 1)
            out << e->coeff << " * v" << v << " " << e->interval << " ";
        else
            out << e->interval << " ";
        if (e->side_cond.size() <= 5)
            out << e->side_cond << " ";
        else
            out << e->side_cond.size() << " side-conditions ";
        unsigned count = 0;
        for (const auto& src : e->src) {
            ++count;
            out << src << "; ";
            if (count > 10) {
                out << " ...";
                break;
            }
        }
        return out;
    }

    std::ostream& viable::display_all(std::ostream& out, pvar v, entry const* e, char const* delimiter) const {
        if (!e)
            return out;
        entry const* first = e;
        unsigned count = 0;
        do {
            display_one(out, v, e) << delimiter;
            e = e->next();
            ++count;
            if (count > 10) {
                out << " ...";
                break;
            }
        }
        while (e != first);
        return out;
    }

    std::ostream& viable::display_all(std::ostream& out, pvar v, layers const& ls, char const* delimiter) const {
        // TODO
        return out;
    }

    std::ostream& viable::display(std::ostream& out, pvar v, char const* delimiter) const {
        display_all(out, v, m_units[v], delimiter);
        display_all(out, v, m_equal_lin[v], delimiter);
        display_all(out, v, m_diseq_lin[v], delimiter);
        return out;
    }

    std::ostream& viable::display(std::ostream& out, char const* delimiter) const {
        for (pvar v = 0; v < m_units.size(); ++v)
            display(out << "v" << v << ": ", v, delimiter) << "\n";
        return out;
    }

    /*
     * Lower bounds are strictly ascending.
     * Intervals don't contain each-other (since lower bounds are ascending, it suffices to check containment in one direction).
     */
    bool viable::well_formed(entry* e) {
        if (!e)
            return true;
        entry* first = e;
        while (true) {
            if (!e->active)
                return false;

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

    /*
     * Layers are ordered in strictly descending bit-width.
     * Entries in each layer are well-formed.
     */
    bool viable::well_formed(layers const& ls) {
        unsigned prev_width = std::numeric_limits<unsigned>::max();
        for (layer const& l : ls.get_layers()) {
            if (!well_formed(l.entries))
                return false;
            if (!all_of(dll_elements(l.entries), [&l](entry const& e) { return e.bit_width == l.bit_width; }))
                return false;
            if (prev_width <= l.bit_width)
                return false;
            prev_width = l.bit_width;
        }
        return true;
    }

}
