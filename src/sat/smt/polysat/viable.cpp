/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

Notes:


--*/


#include "util/debug.h"
#include "util/log.h"
#include "sat/smt/polysat/viable.h"
#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/number.h"
#include "sat/smt/polysat/refine.h"
#include "sat/smt/polysat/ule_constraint.h"

namespace polysat {

    using dd::val_pp;

    viable::viable(core& c) : c(c), cs(c.cs()), m_forbidden_intervals(c), m_fixed_bits(c) {}

    viable::~viable() {
        for (auto* e : m_alloc)
            dealloc(e);
    }

    std::ostream& operator<<(std::ostream& out, find_t f) {
        switch (f) {
        case find_t::empty: return out << "empty";
        case find_t::singleton: return out << "singleton";
        case find_t::multiple: return out << "multiple";
        case find_t::resource_out: return out << "resource-out";
        default: return out << "<unknown>";
        }
    }

    struct viable::pop_viable_trail : public trail {
        viable& m_s;
        entry* e;
        entry_kind k;
    public:
        pop_viable_trail(viable& s, entry* e, entry_kind k)
            : m_s(s), e(e), k(k) {}
        void undo() override {
            m_s.pop_viable(e, k);
        }
    };

    struct viable::push_viable_trail : public trail {
        viable& m_s;
        entry* e;
    public:
        push_viable_trail(viable& s, entry* e)
            : m_s(s), e(e) {}
        void undo() override {
            m_s.push_viable(e);
        }
    };

    viable::entry* viable::alloc_entry(pvar var, unsigned constraint_index) {
        entry* e = nullptr;
        if (m_alloc.empty())
            e = alloc(entry);
        else {
            e = m_alloc.back();
            m_alloc.pop_back();
        }
        e->reset();
        e->var = var;
        e->constraint_index = constraint_index;
        
        return e;
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

    void viable::init_overlaps(pvar v) {
        m_overlaps.reset();
        c.get_bitvector_suffixes(v, m_overlaps);
        std::sort(m_overlaps.begin(), m_overlaps.end(), [&](auto const& x, auto const& y) { return c.size(x.v) < c.size(y.v); });
        LOG("Overlaps with v" << v << ":" << m_overlaps);
    }

    lbool viable::find_viable(pvar v, rational& val1, rational& val2) {
        m_explain.reset();
        m_var = v;
        m_num_bits = c.size(v);
        m_fixed_bits.reset(v);
        init_overlaps(v);

        rational const& max_value = c.var2pdd(v).max_value();

        val1 = 0;
        lbool r = next_viable(val1);
        if (r != l_true)
            return r;

        if (val1 == max_value) {
            val2 = val1;
            return l_true;
        }
        val2 = val1 + 1;
        
        r = next_viable(val2);

        if (r != l_false)
            return r;
        val2 = val1;
        return l_true;
    }

    //
    // Alternate next viable unit and next fixed until convergence.
    // Check the non-units 
    // Refine?
    // 
    lbool viable::next_viable(rational& val) {
        unsigned rounds = 0;
        do {     
            if (rounds > 10)
                return l_undef;
            ++rounds;
            rational val0 = val;
            auto r = next_viable_unit(val);
            if (r != l_true)
                return r;
            if (!m_fixed_bits.next(val))
                return l_false;
            if (refine_equal_lin(m_var, val))
                continue;
            if (refine_disequal_lin(m_var, val))
                continue;
            if (val0 != val)
                continue;
        } 
        while (false);
        return l_true;
    }

    // 
    // 
    // from smallest size(w) overlap [w] to largest
    //     from smallest bit_width layer [bit_width, entries] to largest
    //         check if val is allowed by entries or advance val to next allowed value
    // 
    lbool viable::next_viable_unit(rational& val) {
        for (auto const& [w, offset] : m_overlaps) {
            auto r = next_viable_overlap(w, val);
            if (r != l_true)
                return r;
        }
        return l_true;
    }

    lbool viable::next_viable_overlap(pvar w, rational& val) {
        for (auto& layer : m_units[w].get_layers()) {
            auto r = next_viable_layer(w, layer, val);
            if (r != l_true)
                return r;
        }
        return l_true;
    }

    /*
    * v in [lo, hi[:
    *  - hi >= v: forward(v) := hi
    *  - hi < v: l_false
    * 2^k v in [lo, hi[:
    *  - hi > 2^k v: forward(v) := hi//2^k + 2^k(v//2^k)
    *  - hi <= 2^k v: forward(v) := hi//2^k + 2^k(v//2^k + 1) unless it overflows.
    * w is a suffix of v of width w.width <= v.width with forbidden 2^l w not in [lo, hi[ and 2^l v[w.width-1:0] in [lo, hi[.
    *   - set k := l + v.width - w.width, lo' := 2^{v.width-w.width} lo, hi' := 2^{v.width-w.width} hi.
    */
    lbool viable::next_viable_layer(pvar w, layer& layer, rational& val) {
        unsigned v_width = m_num_bits;
        unsigned w_width = c.size(w);        
        unsigned l = w_width - layer.bit_width;
        SASSERT(v_width >= w_width);
        SASSERT(layer.bit_width <= w_width);

        bool is_zero = val.is_zero(), wrapped = false;
        rational val1 = val;
        rational const& p2l = rational::power_of_two(l);
        rational const& p2w = rational::power_of_two(w_width);
                
        while (true) {
            if (l > 0)
                val1 *= p2l;
            if (w_width < v_width || l > 0)
                val1 = mod(val1, p2w);
            auto e = find_overlap(val1, layer.entries);
            if (!e) {
                if (l > 0)
                    val1 /= p2l;
                break;
            }
            // TODO check if admitted: layer.entries = e;
            m_explain.push_back(e);
            auto hi = e->interval.hi_val();
            if (hi < val1) {
                if (is_zero)
                    return l_false;
                if (w_width == v_width && l == 0)
                    return l_false;
                // start from 0 and find the next viable value within this layer.
                val1 = 0;
                wrapped = true;
            }
            val1 = hi;
            SASSERT(val1 < p2w);
            // p2l * x = val1 = hi
            if (l > 0)
                val1 = hi / p2l;
            SASSERT(val1.is_int());
        }
        SASSERT(val1 < p2w);
        if (w_width < v_width) {
            if (l > 0)
                NOT_IMPLEMENTED_YET();
            rational val2 = val;
            if (wrapped) {
                val2 = mod(div(val2, p2w) + 1, p2w) * p2w;
                if (val2 == 0)
                    return l_false;
            }
            else
                val2 = clear_lower_bits(val2, w_width);
            val = val1 + val2;
        }
        else if (l > 0) {
            NOT_IMPLEMENTED_YET();
        }
        else
            val = val1;
      
        return l_true;
    }

    // Find interval that contains 'val', or, if no such interval exists, null.
   viable::entry* viable::find_overlap(rational const& val, entry* entries) {
        SASSERT(entries);
        // display_all(std::cerr << "entries:\n\t", 0, entries, "\n\t");
        entry* const first = entries;
        entry* e = entries;
        do {
            auto const& i = e->interval;
            if (i.currently_contains(val))
                return e;
            entry* const n = e->next();
            // there is only one interval, and it does not contain 'val'
            if (e == n)
                return nullptr;
            // check whether 'val' is contained in the gap between e and n
            bool const overlapping = e->interval.currently_contains(n->interval.lo_val());
            if (!overlapping && r_interval::contains(e->interval.hi_val(), n->interval.lo_val(), val))
                return nullptr;
            e = n;
        } 
        while (e != first);
        UNREACHABLE();
        return nullptr;
    }

    bool viable::refine_equal_lin(pvar v, rational const& val) {
        // LOG_H2("refine-equal-lin with v" << v << ", val = " << val);
        entry const* e = m_equal_lin[v];
        if (!e)
            return true;
        entry const* first = e;
        auto& m = c.var2pdd(v);
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
                        entry* ne = alloc_entry(v, e->constraint_index);
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
                        // LOG("refined to [" << num_pp(c, v, lo) << ", " << num_pp(c, v, hi) << "[");
                        SASSERT_EQ(mod(a * hi, mod_value), b);  // hi is the solution
                        entry* ne = alloc_entry(v, e->constraint_index);
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
                    // LOG("refined to [" << num_pp(c, v, lo) << ", " << num_pp(c, v, hi) << "[");
                    SASSERT_EQ(mod(a * (lo - 1), mod_value), b);  // lo-1 is a solution
                    SASSERT_EQ(mod(a * hi, mod_value), b);  // hi is a solution
                    entry* ne = alloc_entry(v, e->constraint_index);
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
                //LOG("refined to [" << num_pp(c, v, lo) << ", " << num_pp(c, v, hi) << "[");
                // verbose_stream() << "lo=" << lo << " val=" << val << " hi=" << hi << "\n";
                if (lo <= hi) {
                    SASSERT(0 <= lo && lo <= val && val < hi && hi <= mod_value);
                }
                else {
                    SASSERT(0 < hi && hi < lo && lo < mod_value && (val < hi || lo <= val));
                }
                bool full = (lo == 0 && hi == mod_value);
                if (hi == mod_value)
                    hi = 0;
                entry* ne = alloc_entry(v, e->constraint_index);
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
        } while (e != first);
        return true;
    }

    bool viable::refine_disequal_lin(pvar v, rational const& val) {
        // LOG_H2("refine-disequal-lin with v" << v << ", val = " << val);
        entry const* e = m_diseq_lin[v];
        if (!e)
            return true;
        entry const* first = e;
        auto& m = c.var2pdd(v);
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
                pdd lop = c.var2pdd(v).mk_val(lo);
                pdd hip = c.var2pdd(v).mk_val(hi);
                entry* ne = alloc_entry(v, e->constraint_index);
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
        } while (e != first);
        return true;
    }

    /*
    * Explain why the current variable is not viable or signleton.
    */
    dependency_vector viable::explain() {
        dependency_vector result;
        for (auto e : m_explain) {
            auto index = e->constraint_index;
            auto const& [sc, d, value] = c.m_constraint_index[index];
            result.push_back(d);
            result.append(c.explain_eval(sc));
        }
        result.append(m_fixed_bits.explain());
        return result;
    }

    /*
    * Register constraint at index 'idx' as unitary in v.
    */
    void viable::add_unitary(pvar v, unsigned idx) {

        if (c.is_assigned(v))
            return;
        auto [sc, d, value] = c.m_constraint_index[idx];
        SASSERT(value != l_undef);
        if (value == l_false)
            sc = ~sc;

        entry* ne = alloc_entry(v, idx);
        if (!m_forbidden_intervals.get_interval(sc, v, *ne)) {
            m_alloc.push_back(ne);
            return;
        }

        if (ne->interval.is_currently_empty()) {
            m_alloc.push_back(ne);
            return;
        }        

        if (ne->coeff == 1) {
            intersect(v, ne);
            return;
        }
        else if (ne->coeff == -1) {
            insert(ne, v, m_diseq_lin, entry_kind::diseq_e);
            return;
        }
        else {
            unsigned const w = c.size(v);
            unsigned const k = ne->coeff.parity(w);
            // unsigned const lo_parity = ne->interval.lo_val().parity(w);
            // unsigned const hi_parity = ne->interval.hi_val().parity(w);

            display_one(std::cerr << "try to reduce entry: ", v, ne) << "\n";

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
                // Reference: Fig. 1 (dtrim) in BitvectorsMCSAT
                //
                pdd const& pdd_lo = ne->interval.lo();
                pdd const& pdd_hi = ne->interval.hi();
                rational const& lo = ne->interval.lo_val();
                rational const& hi = ne->interval.hi_val();

                rational new_lo = machine_div2k(lo, k);
                if (mod2k(lo, k).is_zero())
                    ne->side_cond.push_back(cs.eq(pdd_lo * rational::power_of_two(w - k)));
                else {
                    new_lo += 1;
                    ne->side_cond.push_back(~cs.eq(pdd_lo * rational::power_of_two(w - k)));
                }

                rational new_hi = machine_div2k(hi, k);
                if (mod2k(hi, k).is_zero())
                    ne->side_cond.push_back(cs.eq(pdd_hi * rational::power_of_two(w - k)));
                else {
                    new_hi += 1;
                    ne->side_cond.push_back(~cs.eq(pdd_hi * rational::power_of_two(w - k)));
                }

                // we have to update also the pdd bounds accordingly, but it seems not worth introducing new variables for this eagerly
                //      new_lo = lo[:k]  etc.
                // TODO: for now just disable the FI-lemma if this case occurs
                ne->valid_for_lemma = false;

                if (new_lo == new_hi) {
                    // empty or full
                    // if (ne->interval.currently_contains(rational::zero()))
                    NOT_IMPLEMENTED_YET();
                }

                ne->coeff = machine_div2k(ne->coeff, k);
                ne->interval = eval_interval::proper(pdd_lo, new_lo, pdd_hi, new_hi);
                ne->bit_width -= k;
                display_one(std::cerr << "reduced entry:  ", v, ne) << "\n";
                LOG("reduced entry to unit in bitwidth " << ne->bit_width);
                intersect(v, ne);
            }

            // TODO: later, can reduce according to shared_parity
            // unsigned const shared_parity = std::min(coeff_parity, std::min(lo_parity, hi_parity));

            insert(ne, v, m_equal_lin, entry_kind::equal_e);
            return;
        }
    }

    void viable::ensure_var(pvar v) {
        while (v >= m_units.size()) {
            m_units.push_back(layers());
            m_equal_lin.push_back(nullptr);
            m_diseq_lin.push_back(nullptr);
        }
    }

    bool viable::intersect(pvar v, entry* ne) {
        SASSERT(!c.is_assigned(v));
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
            c.trail().push(pop_viable_trail(*this, ne, entry_kind::unit_e));
            ne->init(ne);
            return ne;
            };

        auto remove_entry = [&](entry* e) {
            c.trail().push(push_viable_trail(*this, e));
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

    viable::layer& viable::layers::ensure_layer(unsigned bit_width) {
        for (unsigned i = 0; i < m_layers.size(); ++i) {
            layer& l = m_layers[i];
            if (l.bit_width == bit_width)
                return l;
            else if (l.bit_width > bit_width) {
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

    void viable::pop_viable(entry* e, entry_kind k) {
        unsigned v = e->var;
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
    }

    void viable::push_viable(entry* e) {
        // display_one(verbose_stream() << "Push entry: ", v, e) << "\n";
        auto v = e->var;
        entry*& entries = m_units[v].get_layer(e)->entries;
        SASSERT(e->prev() != e || !entries);
        SASSERT(e->prev() != e || e->next() == e);
        SASSERT(!e->active);
        e->active = true;

        SASSERT(well_formed(m_units[v]));
        if (e->prev() != e) {
            entry* pos = e->prev();
            e->init(e);
            pos->insert_after(e);
            if (!entries || e->interval.lo_val() < entries->interval.lo_val())
                entries = e;
        }
        else
            entries = e;
        SASSERT(well_formed(m_units[v]));
    }

    void viable::insert(entry* e, pvar v, ptr_vector<entry>& entries, entry_kind k) {
        SASSERT(well_formed(m_units[v]));

        c.trail().push(pop_viable_trail(*this, e, k));

        e->init(e);
        if (!entries[v])
            entries[v] = e;
        else
            e->insert_after(entries[v]);
        SASSERT(entries[v]->invariant());
        SASSERT(well_formed(m_units[v]));
    }


    std::ostream& viable::display_one(std::ostream& out, pvar v, entry const* e) const {
        auto& m = c.var2pdd(v);
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
     * Layers are ordered in strictly ascending bit-width.
     * Entries in each layer are well-formed.
     */
    bool viable::well_formed(layers const& ls) {
        bool first = true;
        unsigned prev_width = 0;
        for (layer const& l : ls.get_layers()) {
            if (!well_formed(l.entries))
                return false;
            if (!all_of(dll_elements(l.entries), [&l](entry const& e) { return e.bit_width == l.bit_width; }))
                return false;
            if (!first && prev_width >= l.bit_width)
                return false;
            first = false;
            prev_width = l.bit_width;
        }
        return true;
    }
}
