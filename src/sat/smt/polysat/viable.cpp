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
#include "sat/smt/polysat/project_interval.h"
#include "sat/smt/polysat/ule_constraint.h"

namespace polysat {

    using dd::val_pp;

    viable::viable(core& c) : c(c), cs(c.cs()), m_forbidden_intervals(c), m_projection(c), m_fixed_bits(c) {}

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

    viable::entry* viable::alloc_entry(pvar var, constraint_id constraint_index) {
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

    bool viable::assign(pvar v, rational const& value, dependency dep) {
        m_var = v;
        m_explain_kind = explain_t::none;
        m_num_bits = c.size(v);
        m_fixed_bits.init(v);
        m_explain.reset();
        m_assign_dep = null_dependency;
        init_suffixes(v);
        bool first = true;
        while (true) {
            for (auto const& [w, offset] : m_suffixes) {
                for (auto& layer : m_units[w].get_layers()) {
                    entry* e = find_overlap(layer, value);
                    if (!e)
                        continue;
                    m_explain.push_back({ e, value });
                    m_explain_kind = explain_t::assignment;
                    m_assign_dep = dep;
                    return false;
                }
            }
            if (!first)
                return true;
            first = false;
            if (!check_fixed_bits(v, value))
                continue;
            if (!check_disequal_lin(v, value))
                continue;
            if (!check_equal_lin(v, value))
                continue;
            break;
        }
            
        return true;
    }

    find_t viable::find_viable(pvar v, rational& lo) {
        m_explain.reset();
        m_var = v;
        m_num_bits = c.size(v);
        m_fixed_bits.init(v);
        init_suffixes(v);
        m_explain_kind = explain_t::none;
        m_assign_dep = null_dependency;

        for (unsigned rounds = 0; rounds < 10; ) {
            entry* n = find_overlap(lo);

            if (m_explain_kind == explain_t::conflict)
                return find_t::empty;

            if (n)
                continue;

            if (!check_fixed_bits(v, lo))
                continue;
            ++rounds;
            if (!check_disequal_lin(v, lo))
                continue;
            if (!check_equal_lin(v, lo))
                continue;
            if (is_propagation(lo)) {
                m_explain_kind = explain_t::propagation;
                return find_t::singleton;
            }
            return find_t::multiple;                        
        }
        TRACE("bv", display(tout << "resource-out v" << v << "\n"));
        return find_t::resource_out;        
    }

    void viable::init_suffixes(pvar v) {
        m_suffixes.reset();
        c.get_bitvector_suffixes(v, m_suffixes);
        std::sort(m_suffixes.begin(), m_suffixes.end(), [&](auto const& x, auto const& y) { return c.size(x.child) < c.size(y.child); });
    }


    //
    // find set of layers across all suffixes, sort by bit-width
    //
    // from smallest bit_width layer [bit_width, entries] to largest
    //     check if val is allowed by entries or advance val to next allowed value
    //

    viable::entry* viable::find_overlap(rational& val) {
        entry* last = nullptr;

#if 0
        {
            verbose_stream() << "\n\n\n\n\nfind_overlap v" << m_var << ", starting val = " << val << "\n";
            for (auto const& [w, offset] : m_suffixes) {
                for (auto& layer : m_units[w].get_layers()) {
                    verbose_stream() << "  layer width = " << layer.bit_width << "\n";
                    entry const* e = layer.entries;
                    if (!e)
                        continue;
                    entry const* first = e;
                    do {
                        display_one(verbose_stream() << "    ", e) << "\n";
                        e = e->next();
                    }
                    while (e != first);
                }
            }
        }
#endif

        ptr_vector<layer const> layers;
        for (auto const& [w, offset] : m_suffixes)
            for (auto const& layer : m_units[w].get_layers())
                layers.push_back(&layer);
        std::sort(layers.begin(), layers.end(), [](layer const* l1, layer const* l2) { return l1->bit_width < l2->bit_width; });

        while (entry* e = find_overlap(layers, val)) {
            last = e;
            if (e->interval.is_proper())
                update_value_to_high(val, e);
            display_explain(verbose_stream() << "found: ", {e,val}) << "\n";
            m_explain.push_back({ e, val });
            if (is_conflict()) {
                verbose_stream() << "find_overlap conflict\n";
                m_explain_kind = explain_t::conflict;
                return nullptr;
            }
        }
        return last;
    }

    viable::entry* viable::find_overlap(ptr_vector<layer const> const& layers, rational const& val) {
        for (layer const* layer : layers)
            if (entry* e = find_overlap(*layer, val))
                return e;
        return nullptr;
    }

    viable::entry* viable::find_overlap(layer const& l, rational const& val) {
        if (!l.entries)
            return nullptr;
        unsigned v_width = m_num_bits;
        unsigned b_width = l.bit_width;
        if (v_width == b_width)
            return find_overlap(val, l.entries);
        rational val1 = mod(val, rational::power_of_two(b_width));
        return find_overlap(val1, l.entries);
    }

    void viable::update_value_to_high(rational& val, entry* e) {
        unsigned v_width = m_num_bits;
        unsigned b_width = e->bit_width;
        SASSERT(b_width <= v_width);

        auto const& hi = e->interval.hi_val();
        auto const& lo = e->interval.lo_val();
        if (b_width == v_width) {
            val = hi;
            SASSERT(0 <= val && val <= c.var2pdd(m_var).max_value());
            return;
        }

        auto p2b = rational::power_of_two(b_width);
        rational val2 = clear_lower_bits(val, b_width);
        if (lo <= mod(val, p2b) && hi < lo) {
            val2 += p2b;            
            if (val2 == rational::power_of_two(v_width)) 
                val2 = 0;            
        }
        val = val2 + hi;  
        SASSERT(0 <= hi && hi < p2b);
        SASSERT(0 <= val && val <= c.var2pdd(m_var).max_value());
    }



    /*
    * In either case we are checking a constraint $v[u-1:0]\not\in[lo, hi[$ 
    * where $u := w'-k-1$ and using it to compute $\forward(v)$.
    * Thus, suppose $v[u-1:0] \in [lo, hi[$.
    * - $lo < hi$: $\forward(v) := \forward(2^u v[w-1:w-u] + hi)$.
    * - $lo > hi$, $v[w-1:w-u]+1 = 2^{w-u}$: $\forward(v) := \bot$
    * - $lo > hi$, $v[w-1:w-u]+1 < 2^{w-u}$: $\forward(v) := \forward(2^u (v[w-1:w-u]+1) + hi)$
    */

    // Find interval that contains 'val', or, if no such interval exists, null.
   viable::entry* viable::find_overlap(rational const& val, entry* entries) {
        SASSERT(entries);
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

    bool viable::check_equal_lin(pvar v, rational const& val) {
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

    bool viable::check_fixed_bits(pvar v, rational const& val) {
        auto e = alloc_entry(v, constraint_id::null());
        if (m_fixed_bits.check(val, *e)) {
            m_alloc.push_back(e);
            return true;
        }
        else {
            TRACE("bv", tout << "fixed " << val << " " << *e << "\n");
            if (!intersect(v, e)) {
                display(verbose_stream());
                display_explain(verbose_stream() << "explain\n");
                UNREACHABLE();
                SASSERT(false);
            }
            
            return false;
        }
    }

    bool viable::check_disequal_lin(pvar v, rational const& val) {
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
    * The current explanation trail is a conflict if the top-most entry
    * is repeated below and there is no entry with higher bit-width between.
    */
    bool viable::is_conflict() {
        auto last = m_explain.back();
        unsigned bw = last.e->bit_width;
        if (last.e->interval.is_full()) {
            m_explain.reset();
            m_explain.push_back(last);
            return true;
        }
        for (unsigned i = m_explain.size() - 1; i-- > 0; ) {
            auto e = m_explain[i];
            if (bw < e.e->bit_width)
                return false;
            if (last.e == e.e)
                return true;
        }
        return false;
    }

    bool viable::is_propagation(rational const& val) {
        // disable for now
        return false;
        if (m_explain.empty())
            return false;
        auto last = m_explain.back();
        auto first = m_explain[0];
        if (first.e->interval.lo_val() == val + 1 &&
            last.e->interval.hi_val() == val &&
            first.e->bit_width == last.e->bit_width &&
            first.e->bit_width == c.size(m_var)) {
            return true;
        }           
        return false;
    }


    std::ostream& operator<<(std::ostream& out, viable::explain_t e) {
        switch(e) {
        case viable::explain_t::conflict: return out << "conflict";
        case viable::explain_t::propagation: return out << "propagation";
        case viable::explain_t::assignment: return out << "assignment";
        case viable::explain_t::none: return out << "none";
        default: UNREACHABLE();
        }
        return out;
    }

    /*
     * Explain why the current variable is not viable or
     * or why it can only have a single value.
     */
    dependency_vector viable::explain() {
        dependency_vector result;      

        // verbose_stream() << "\n\n\n\n\nviable::explain: " << m_explain_kind << " v" << m_var << "\n";
        // display_explain(verbose_stream() << "before subsumption:\n") << "\n";

        // prune redundant intervals
        while (remove_redundant_explanations())
            /* repeat */;

        explanation const last = m_explain.back();

        // if there's more than one interval, we cannot have any full intervals
        SASSERT(m_explain.size() <= 1 || all_of(m_explain, [](auto const& e) { return !e.e->interval.is_full(); }));

        SASSERT(all_of(m_explain, [](auto const& e) { return !e.e->marked; }));
        SASSERT(all_of(m_explain, [](auto const& e) { return !e.mark; }));

        // display_explain(verbose_stream() << "after subsumption:\n") << "\n";

        if (c.inconsistent())
            verbose_stream() << "inconsistent explain\n";
        TRACE("bv", display_explain(tout));

        auto unmark = [&]() {
            for (auto e : m_explain)
                e.e->marked = false;
        };

        auto explain_entry = [&](entry* e) {
            auto index = e->constraint_index;
            if (c.inconsistent())
                return;
            if (e->marked)
                return;
            e->marked = true;
            if (m_var != e->var)
                result.push_back(offset_claim(m_var, { e->var, 0 }));
            for (auto const& sc : e->side_cond) {
                auto d = c.propagate(sc, c.explain_weak_eval(sc), "entry side_cond weak eval");
                if (c.inconsistent()) {
                    verbose_stream() << "inconsistent side_cond " << d << " " << sc << "\n";
                }
                result.push_back(d);
            }
            result.append(e->deps);
            if (!index.is_null()) {
                VERIFY_EQ(e->src.size(), 1);
                VERIFY_EQ(c.get_constraint(index), e->src[0]);
                result.push_back(c.get_dependency(index));
            }
        };

        if (last.e->interval.is_full()) {
            SASSERT(m_explain_kind == explain_t::none);
            explain_entry(last.e);
            SASSERT(m_explain.size() == 1);
            unmark();
            return result;
        }

        SASSERT(m_explain_kind != explain_t::none);

#if 1  // explain_overlap NEW
        if (m_explain.size() >= 2) {
            unsigned i;
            for (i = m_explain.size() - 1; i-- > 0; )
                if (m_explain[i].e == last.e)
                    break;
            explanation* first_it = &m_explain[i];
            explanation* last_it = &m_explain.back();
            SASSERT(first_it->e == last_it->e);
            SASSERT(first_it != last_it);
            verbose_stream() << "Relevant entries:\n";
            for (explanation const* e = first_it; e != last_it+1; ++e) {
                display_explain(verbose_stream() << "  ", *e) << "\n";
            }
            verbose_stream() << "\n";
#if 1
            // the version discussed on whiteboard, no hole treatment needed
            rational prefix(0);
            for (explanation const* e = first_it; e != last_it; ++e) {
                explanation const* after = e + 1;

                explain_entry(e->e);
                explain_overlap_v1(*e, *after, prefix, result);
            }
#else
            explain_overlaps_v2(first_it, last_it, result);
#endif
        }
#else  // explain_overlap OLD
        explanation after = last;
        for (unsigned i = m_explain.size() - 1; i-- > 0; ) {
            explanation const& e = m_explain[i];
            explain_overlap(e, after, result);

            // display_explain(verbose_stream() << "explaining ", e) << "\n";

            // explain_holes(&m_explain[0], &m_explain[i], after)
            SASSERT(e.e->bit_width <= last.e->bit_width);
            if (e.e->bit_width < after.e->bit_width) {
                SASSERT(e.e->bit_width < last.e->bit_width);
                // find all holes that end with 'after'
                unsigned hole_bits = e.e->bit_width;
                // display_explain(verbose_stream() << "finding holes (width " << hole_bits << ") ending at ", after) << "\n";
                for (unsigned j = i; j-- > 0; ) {
                    // display_explain(verbose_stream() << "   potential before: ", m_explain[j]) << "\n";
                    if (m_explain[j].e->bit_width <= hole_bits)
                        continue;
                    explanation const& before = m_explain[j];
                    explain_hole_overlap(before, e, after, result);
                    explain_hole_size(before, after, hole_bits, result);
                    hole_bits = before.e->bit_width;
                    if (hole_bits >= after.e->bit_width)
                        break;
                }
            }

            after = e;
            explain_entry(e.e);
            if (e.e == last.e)
                break;
        }
#endif

        if (m_explain_kind == explain_t::propagation) {
            // assume first and last have same bit-width
            // (true because of is_propagation)
            auto first = m_explain[0];
            SASSERT(first.e->bit_width == last.e->bit_width);
            explain_entry(first.e);
            // add constraint that there is only a single viable value.         
            auto sc = cs.eq(last.e->interval.hi() + 1, first.e->interval.lo());
            auto exp = c.propagate(sc, c.explain_weak_eval(sc), "single viable value weak eval");
            if (c.inconsistent()) {
                verbose_stream() << "inconsistent " << sc << " " << exp << "\n";
            }
            result.push_back(exp);            
        }
        if (m_explain_kind == explain_t::assignment) {
            // there is just one entry
            SASSERT(m_explain.size() == 1);
            SASSERT(!m_assign_dep.is_null());
            entry* e = last.e;

            explain_entry(e);
            // assignment conflict and propagation from containing slice depends on concrete values,
            // so we also need the evaluations of linear terms
            SASSERT(!c.is_assigned(m_var));             // assignment of m_var is justified by m_assign_dep
            auto index = last.e->constraint_index;
            if (!index.is_null())
                result.append(c.explain_weak_eval(c.get_constraint(index)));

            IF_VERBOSE(4, {
                verbose_stream() << "\n\n\n\n\n\nNon-viable assignment for v" << m_var << " size " << c.size(m_var) << "\n";
                display_one(verbose_stream() << "entry: ", e) << "\n";
                verbose_stream() << "value " << last.value << "\n";
                verbose_stream() << "m_suffixes " << m_suffixes << "\n";
                m_fixed_bits.display(verbose_stream() << "fixed: ") << "\n";
            });

            // 'result' so far contains explanation for e and its weak evaluation
            m_projection.init(e->var, e->interval, e->bit_width, result);

            switch (m_projection()) {
            case l_true:
                // propagated interval onto subslice
                result.reset();
                m_projection.explain(result);
                break;
            case l_false:
                // conflict (projected interval is full)
                result.reset();
                m_projection.explain(result);
                break;
            case l_undef:
                // unable to propagate interval to containing slice
                // fallback explanation uses assignment of m_var
                result.push_back(m_assign_dep);
                break;
            };
        }
        unmark();
        if (c.inconsistent())
            verbose_stream() << "inconsistent after explain\n";
        return result;
    }

    // Remove entries at the end of m_explain that are subsumed by the new entry e.
    //
    // Consider the following (partial) example from 1ZjKiWGg7I3v.smt2:
    //
    //      v0[28] := 0 v0 [28*v1 + 28 ; 28*v1[ := [28;0[  src -28*v1 + v0 <= 27;       covers [28;0[
    //      v0[2] := 1 v0[2] [2^26+1 ; 2^26[ := [2;1[  src 2^26*v0 + -2^26 == 0;        covers [-2;1[       REDUNDANT
    //      v0[28] := 4 v0 [0 ; 4[ := [0;4[  src 4 <= v0;                               covers [0;4[
    //      v0[2] := 5 v0[2] [2^26+1 ; 2^26[ := [2;1[  src 2^26*v0 + -2^26 == 0;        covers [2;5[        REDUNDANT
    //      v0[5] := 33 v0[5] [2^24 ; 2^23[ := [2;1[  deps 1 == v0 [5]@0 src            covers [2;33[
    //      v0[28] := 0 v0 [28*v1 + 28 ; 28*v1[ := [28;0[  src -28*v1 + v0 <= 27;       covers [28;0[
    //
    // We can skip the entry v0[2] := 5 because v0[5] := 33 already covers that part.
    //
    // We add lower-width intervals such as v0[2] first, to be able to detect conflicts on lower widths.
    // But it means we sometimes get redundant entries like this.
    bool viable::remove_redundant_explanations() {

/*
TODO: handle case like this properly (from alive/181g9c97IsNV.smt2 when calling remove_redundant_explanations() exactly once)
v0[19] := 0 v0 [-131062 ; 0[ := [-131062;0[  src ~4 <= 43691*v0; 
v0[2] := 1 v0[2] [0 ; 1[ := [0;1[  src ~2^17*v0 == 0; 
v0[2] := 2 v0[2] [2^17 ; 2^17+1[ := [1;2[  src ~2^17*v0 + -2^17 == 0; 
v0[19] := 524280 v0 [0 ; 12*v1[ := [0;-8[  side-conds ~4*v1 == 0 src 12*v1 <= v0; 
v0[2] := 524281 v0[2] [0 ; 1[ := [0;1[  src ~2^17*v0 == 0; 
v0[2] := 524282 v0[2] [2^17 ; 2^17+1[ := [1;2[  src ~2^17*v0 + -2^17 == 0; 
v0[19] := 0 v0 [-131062 ; 0[ := [-131062;0[  src ~4 <= 43691*v0; 
*/

        SASSERT(all_of(m_explain, [](auto const& e) { return !e.mark; }));
        explanation const& last = m_explain.back();

        if (m_explain.size() <= 1)
            return false;
        // In conflicts, 'last' is a repeated entry. So m_explain.size() == 2 does not make sense here.
        SASSERT(m_explain.size() > 2);

        // Find index of first entry
        unsigned k = m_explain.size() - 1;
        while (k-- > 0)
            if (m_explain[k].e == last.e)
                break;
        SASSERT(m_explain[k].e == last.e);

        // For each endpoint, keep only the interval that furthest extends
        for (unsigned i = k; i < m_explain.size() - 1; ++i) {
            explanation const& cur = m_explain[i];

            if (m_explain[i].mark)
                continue;  // already pruned

            // next interval contains current endpoint (because of how it was chosen)
            DEBUG_CODE({
                explanation const& next = m_explain[i + 1];
                SASSERT(get_covered_interval(next).contains(cur.value));
            });

            // if the interval after 'next' still contains 'cur.value', we may skip 'next' (and so on)
            unsigned j = i + 2;
            for (; j < m_explain.size(); ++j) {
                r_interval ivl = get_covered_interval(m_explain[j]);
                if (ivl.contains(cur.value))
                    m_explain[j - 1].mark = true;
                else
                    break;
            }
        }

        IF_VERBOSE(1, {
            for (auto const& e : m_explain)
                if (e.mark)
                    display_explain(verbose_stream() << "redundant: ", e) << "\n";
        });

        // Actually perform the removal
        unsigned erased = m_explain.erase_if([](auto const& e) { return e.mark; });
        return erased > 0;
    }

    /*
     * TODO: update explanation! (see appendix/notes)
     *
     * For two consecutive intervals
     *
     * - 2^k x \not\in [lo, hi[         (entry 'e')
     * - 2^k' y \not\in [lo', hi'[      (entry 'after')
     * - value v such that
     *   - 2^k v \not\in [lo, hi[
     *   - 2^k' v \in [lo', hi'[
     *   - hi \in ] (v - 1) * 2^k ; v * 2^k ]
     *
     * Where:
     *  - bw is the width of x, aw the width of y
     *  - ebw is the bit-width of x, abw the bit-width of y
     *  - k = bw - ebw, k' = aw - abw
     *
     * We have the reduced intervals:
     *  - x[ebw] \not\in [ ceil(lo/2^k), ceil(hi/2^k) [
     *  - y[abw] \not\in [ ceil(lo'/2^k'), ceil(hi'/2^k') [
     *  - ceil(lo/2^k) != ceil(hi/2^k)      ... ensured by side conditions from interval reduction
     *  - ceil(lo'/2^k') != ceil(hi'/2^k')  ... ensured by side conditions from interval reduction
     *  - ceil(lo/2^k) = lo[w-1:k]  or  ceil(lo/2^k) = lo[w-1:k] + 1  ... which case is ensured by side conditions
     *
     * Case ebw = abw:
     *  - Regular intervals that link up
     *  - Encode that ceil(hi/2^k) \in [ ceil(lo'/2^k'), ceil(hi'/2^k') [
     *  - This is equivalent to 2^k' ceil(hi/2^k) \in [ lo', hi' [
     *
     * Case ebw < abw:
     *  - 'e' is last entry of a hole.
     *  - project 'after' onto the hole: [?,ceil(hi/2^k)[ links up with [ceil(lo'/2^k')[ebw],ceil(hi'/2^k')[ebw][
     *  - We want to encode:   ceil(hi/2^k) \in [ceil(lo'/2^k')[ebw],ceil(hi'/2^k')[ebw][
     *  - However, if 'after' is too small the projected interval may be empty and we do not get a useful constraint
     *  - The correct choice is to use the complement of the hole rather than the next interval alone.
     *  - This case is handled in explain_hole_overlap.
     *
     * Case ebw > abw:
     *  - 'after' is first entry of a hole.
     *  - conceptually: project complement of hole onto lower bit-width,
     *    i.e., have interval [?,ceil(hi/2^k)[abw][ link up with [ceil(lo'/2^k'),ceil(hi'/2^k')[
     *  - Encode: ceil(hi/2^k)[abw] \in [ceil(lo'/2^k'),ceil(hi'/2^k')[
     *  - Equivalently: 2^k' ceil(hi/2^k)[abw] \in [lo',hi'[
     *  - Equivalently: 2^k' ceil(hi/2^k) \in [lo',hi'[ because k' = aw - abw
     *
     * In both relevant cases, we want to encode the constraint
     *      2^k' ceil(hi/2^k) \in [lo',hi'[
     *
     * - Note that x in [lo, hi[ <=> x - lo < hi - lo.
     * - If k > 0 (i.e., ebw < bw) then evaluate ceil(hi/2^k) (since we cannot express it as pdd).
     *          TODO: possible exception: if all coefficients of 'hi' are divisible by 2^k
     * - If bw != aw, likewise (since we cannot mix different pdd sizes in one expression).
     *          TODO: possible exception: if lo', hi' are values, just translate them to other pdd manager?
     *
     * Evaluating ceil(hi/2^k) means:
     *  - hi \in ] (v - 1) * 2^{bw - ebw} ; v * 2^{bw - ebw} ]
     *  - hi := v mod aw
     *
     */
    void viable::explain_overlap_v1(explanation const& e, explanation const& after, rational& prefix, dependency_vector& deps) {
#define DEBUG_EXPLAIN_OVERLAP 0
        unsigned const bw = c.size(e.e->var);
        unsigned const ebw = e.e->bit_width;
        unsigned const aw = c.size(after.e->var);
        unsigned const abw = after.e->bit_width;
        pdd t = e.e->interval.hi();
        pdd lo = after.e->interval.lo();
        pdd hi = after.e->interval.hi();

#if DEBUG_EXPLAIN_OVERLAP
        verbose_stream() << "explain_overlap\n";
        display_explain(verbose_stream() << "    e     ", e) << "\n";
        display_explain(verbose_stream() << "    after ", after) << "\n";
        verbose_stream() << "    bw " << bw << " ebw " << ebw << " aw " << aw << " abw " << abw << "\n";
        verbose_stream() << "    t0: " << t << "\n";
        verbose_stream() << "    lo0: " << lo << "\n";
        verbose_stream() << "    hi0: " << hi << "\n";
        verbose_stream() << "    stored prefix: " << prefix << "\n";
#endif

        SASSERT(abw <= aw);
        SASSERT(ebw <= bw);
        SASSERT_EQ(mod2k(e.value, ebw), e.e->interval.hi_val());
        SASSERT(r_interval::proper(after.e->interval.lo_val(), after.e->interval.hi_val()).contains(mod2k(e.value, abw)));

        if (ebw > abw) {
            // effective bit-width reduces => store upper bits of value in prefix
            unsigned const store_sz = ebw - abw;
            rational const store_val = mod2k(machine_div2k(e.value, abw), store_sz);
            prefix = prefix * rational::power_of_two(store_sz) + store_val;
            verbose_stream() << "    store_val = " << store_val << "\n";
            verbose_stream() << "    new stored prefix: " << prefix << "\n";
            // for simplicity, we fix the evaluation of the stored upper bits
            // (alternative would be to track sub-ranges of extracted symbolic bounds)
            auto sc = cs.fixed(t, ebw - 1, abw, store_val);
            verbose_stream() << "    t[" << (ebw - 1) << ":" << abw << "] = " << store_val << "\n";
            verbose_stream() << "    fixed prefix constraint " << sc << "\n";
            verbose_stream() << "        eval " << sc.eval() << "\n";
            verbose_stream() << "        weval " << sc.weak_eval(c.get_assignment()) << "\n";
            verbose_stream() << "        seval " << sc.strong_eval(c.get_assignment()) << "\n";
            VERIFY(!sc.is_always_false());
            if (!sc.is_always_true())
                deps.push_back(c.propagate(sc, c.explain_weak_eval(sc), "explain_overlap prefix evaluation"));
        }

        rational restore_val;
        if (ebw < abw) {
            // restore bits from prefix
            unsigned const restore_sz = abw - ebw;
            /*rational const*/ restore_val = mod2k(prefix, restore_sz);
            prefix = machine_div2k(prefix, restore_sz);
            verbose_stream() << "    restore_val = " << restore_val << "\n";
            verbose_stream() << "    new stored prefix: " << prefix << "\n";

            // restore_val * rational::power_of_two(ebw) + t(?)
            SASSERT(ebw < bw || aw != bw);
        }

        // if there is wrap-around, increment prefix
        if (e.e->interval.lo_val() > e.e->interval.hi_val()) {
            prefix++;
            verbose_stream() << "    incremented stored prefix: " << prefix << "\n";
        }

        if (ebw < bw || aw != bw) {
            auto const& p2b = rational::power_of_two(bw);
            auto const& p2eb = rational::power_of_two(bw - ebw);
            // let coeff = 2^{bw - ebw}
            // let assume coeff * x \not\in [s, t[
            // Then value is chosen, min x . coeff * x >= t.
            // In other words:
            //
            // x >= t div coeff
            // => t <= coeff * x

            // (x - 1) * coeff < t <= x * coeff

            // a < x <= b <=>
            // a + 1 <= x < b + 1
            // x - a - 1 < b - a

            auto vlo = c.value(mod((e.value - 1) * p2eb + 1, p2b), bw);
            auto vhi = c.value(mod(e.value * p2eb + 1, p2b), bw);
            auto sc = cs.ult(t - vlo, vhi - vlo);

#if DEBUG_EXPLAIN_OVERLAP
            verbose_stream() << "    assignment: " << c.get_assignment() << "\n";
            if (c.is_assigned(1))
                verbose_stream() << "    v1 = " << c.get_assignment().value(1) << "\n";
            verbose_stream() << "    value " << e.value << "\n";
            verbose_stream() << "    t " << t << "\n";
            verbose_stream() << "    [" << vlo << " " << vhi << "[\n";
            verbose_stream() << "    before bw " << ebw << " " << bw << " " << *e.e << "\n";
            verbose_stream() << "    after  bw " << abw << " " << aw << " " << *after.e << "\n";
            if (!t.is_val())
                verbose_stream() << "    symbolic t : " << t << "\n";
            verbose_stream() << "    " << t - vlo << " " << vhi - vlo << "\n";
            verbose_stream() << "    sc " << sc << "\n";
#endif

            CTRACE("bv", sc.is_always_false(), c.display(tout));
            VERIFY(!sc.is_always_false());
            if (!sc.is_always_true())
                deps.push_back(c.propagate(sc, c.explain_weak_eval(sc), "explain_overlap value bounds"));
            t.reset(lo.manager());
            t = c.value(mod(e.value, rational::power_of_two(aw)), aw);
#if DEBUG_EXPLAIN_OVERLAP
            verbose_stream() << "    t' " << t << "\n";
#endif
            if (c.inconsistent())
                verbose_stream() << "inconsistent overlap " << sc << " " << "\n";
        }

        if (ebw < abw) {
            t = restore_val * rational::power_of_two(ebw) + t;
            verbose_stream() << "    restored t: " << t << "\n";
        }

        if (abw < aw) {
            t *= rational::power_of_two(aw - abw);
            verbose_stream() << "    shifted t: " << t << "\n";
        }

        auto sc = cs.ult(t - lo, hi - lo);
#if DEBUG_EXPLAIN_OVERLAP
        verbose_stream() << "    t: " << t << "\n";
        verbose_stream() << "    lo: " << lo << "\n";
        verbose_stream() << "    hi: " << hi << "\n";
        verbose_stream() << "    lhs: " << t  << " - (" << lo << ")     ==     " << (t  - lo) << "\n";
        verbose_stream() << "    rhs: " << hi << " - (" << lo << ")     ==     " << (hi - lo) << "\n";
        verbose_stream() << "    ult: " << sc << "\n";
        verbose_stream() << "    eval " << sc.eval() << "\n";
        verbose_stream() << "    weval " << sc.weak_eval(c.get_assignment()) << "\n";
        verbose_stream() << "    seval " << sc.strong_eval(c.get_assignment()) << "\n";
#endif
        VERIFY(!sc.is_always_false());
        if (!sc.is_always_true())
            deps.push_back(c.propagate(sc, c.explain_weak_eval(sc), "explain_overlap linking constraint"));
        if (c.inconsistent()) {
            verbose_stream() << "inconsistent ult " << sc << " " << "\n";
            verbose_stream() << "before bw " << ebw << " " << bw << " " << *e.e << "\nafter  bw " << abw << " " << aw << " " << *after.e << "\n";
            display(verbose_stream());
            // UNREACHABLE();
        }
    }









    void viable::explain_overlaps_v2(explanation const* first, explanation const* last, dependency_vector& deps) {
        // version with "flipped" end condition (i.e., lo \in previous interval instead of hi \in next interval), needs hole size constraint
        NOT_IMPLEMENTED_YET();
    }








    /*
     * For two consecutive intervals
     *
     * - 2^k x \not\in [lo, hi[         (entry 'e')
     * - 2^k' y \not\in [lo', hi'[      (entry 'after')
     * - value v such that
     *   - 2^k v \not\in [lo, hi[
     *   - 2^k' v \in [lo', hi'[
     *   - hi \in ] (v - 1) * 2^k ; v * 2^k ]
     *
     * Where:
     *  - bw is the width of x, aw the width of y
     *  - ebw is the bit-width of x, abw the bit-width of y
     *  - k = bw - ebw, k' = aw - abw
     *
     * We have the reduced intervals:
     *  - x[ebw] \not\in [ ceil(lo/2^k), ceil(hi/2^k) [
     *  - y[abw] \not\in [ ceil(lo'/2^k'), ceil(hi'/2^k') [
     *  - ceil(lo/2^k) != ceil(hi/2^k)      ... ensured by side conditions from interval reduction
     *  - ceil(lo'/2^k') != ceil(hi'/2^k')  ... ensured by side conditions from interval reduction
     *  - ceil(lo/2^k) = lo[w-1:k]  or  ceil(lo/2^k) = lo[w-1:k] + 1  ... which case is ensured by side conditions
     *
     * Case ebw = abw:
     *  - Regular intervals that link up
     *  - Encode that ceil(hi/2^k) \in [ ceil(lo'/2^k'), ceil(hi'/2^k') [
     *  - This is equivalent to 2^k' ceil(hi/2^k) \in [ lo', hi' [
     *
     * Case ebw < abw:
     *  - 'e' is last entry of a hole.
     *  - project 'after' onto the hole: [?,ceil(hi/2^k)[ links up with [ceil(lo'/2^k')[ebw],ceil(hi'/2^k')[ebw][
     *  - We want to encode:   ceil(hi/2^k) \in [ceil(lo'/2^k')[ebw],ceil(hi'/2^k')[ebw][
     *  - However, if 'after' is too small the projected interval may be empty and we do not get a useful constraint
     *  - The correct choice is to use the complement of the hole rather than the next interval alone.
     *  - This case is handled in explain_hole_overlap.
     *
     * Case ebw > abw:
     *  - 'after' is first entry of a hole.
     *  - conceptually: project complement of hole onto lower bit-width,
     *    i.e., have interval [?,ceil(hi/2^k)[abw][ link up with [ceil(lo'/2^k'),ceil(hi'/2^k')[
     *  - Encode: ceil(hi/2^k)[abw] \in [ceil(lo'/2^k'),ceil(hi'/2^k')[
     *  - Equivalently: 2^k' ceil(hi/2^k)[abw] \in [lo',hi'[
     *  - Equivalently: 2^k' ceil(hi/2^k) \in [lo',hi'[ because k' = aw - abw
     *
     * In both relevant cases, we want to encode the constraint
     *      2^k' ceil(hi/2^k) \in [lo',hi'[
     *
     * - Note that x in [lo, hi[ <=> x - lo < hi - lo.
     * - If k > 0 (i.e., ebw < bw) then evaluate ceil(hi/2^k) (since we cannot express it as pdd).
     *          TODO: possible exception: if all coefficients of 'hi' are divisible by 2^k
     * - If bw != aw, likewise (since we cannot mix different pdd sizes in one expression).
     *          TODO: possible exception: if lo', hi' are values, just translate them to other pdd manager?
     *
     * Evaluating ceil(hi/2^k) means:
     *  - hi \in ] (v - 1) * 2^{bw - ebw} ; v * 2^{bw - ebw} ]
     *  - hi := v mod aw
     *
     */
    void viable::explain_overlap(explanation const& e, explanation const& after, dependency_vector& deps) {
#define DEBUG_EXPLAIN_OVERLAP 0
        unsigned const bw = c.size(e.e->var);
        unsigned const ebw = e.e->bit_width;
        unsigned const aw = c.size(after.e->var);
        unsigned const abw = after.e->bit_width;
        pdd t = e.e->interval.hi();
        pdd lo = after.e->interval.lo();
        pdd hi = after.e->interval.hi();

#if DEBUG_EXPLAIN_OVERLAP
        verbose_stream() << "explain_overlap\n";
        display_explain(verbose_stream() << "    e     ", e) << "\n";
        display_explain(verbose_stream() << "    after ", after) << "\n";
        verbose_stream() << "    bw " << bw << " ebw " << ebw << " aw " << aw << " abw " << abw << "\n";
#endif

        SASSERT(abw <= aw);
        SASSERT(ebw <= bw);
        SASSERT_EQ(mod2k(e.value, ebw), e.e->interval.hi_val());
        SASSERT(r_interval::proper(after.e->interval.lo_val(), after.e->interval.hi_val()).contains(mod2k(e.value, abw)));

        if (ebw < abw) {
            // 'e' is the last entry of a hole.
            // This case is handled in explain_hole_overlap.
            // return;  // TODO: disabled for now
        }

        if (ebw < bw || aw != bw) {
            auto const& p2b = rational::power_of_two(bw);
            auto const& p2eb = rational::power_of_two(bw - ebw);
            // let coeff = 2^{bw - ebw}
            // let assume coeff * x \not\in [s, t[
            // Then value is chosen, min x . coeff * x >= t.
            // In other words:
            //
            // x >= t div coeff
            // => t <= coeff * x
            
            // (x - 1) * coeff < t <= x * coeff
            
            // a < x <= b <=>
            // a + 1 <= x < b + 1
            // x - a - 1 < b - a

            auto vlo = c.value(mod((e.value - 1) * p2eb + 1, p2b), bw);
            auto vhi = c.value(mod(e.value * p2eb + 1, p2b), bw);
            auto sc = cs.ult(t - vlo, vhi - vlo);

#if DEBUG_EXPLAIN_OVERLAP
            verbose_stream() << "    assignment: " << c.get_assignment() << "\n";
            if (c.is_assigned(1))
                verbose_stream() << "    v1 = " << c.get_assignment().value(1) << "\n";
            verbose_stream() << "    value " << e.value << "\n";
            verbose_stream() << "    t " << t << "\n";
            verbose_stream() << "    [" << vlo << " " << vhi << "[\n";
            verbose_stream() << "    before bw " << ebw << " " << bw << " " << *e.e << "\n";
            verbose_stream() << "    after  bw " << abw << " " << aw << " " << *after.e << "\n";
            if (!t.is_val())
                verbose_stream() << "    symbolic t : " << t << "\n";
            verbose_stream() << "    " << t - vlo << " " << vhi - vlo << "\n";
            verbose_stream() << "    sc " << sc << "\n";
#endif

            CTRACE("bv", sc.is_always_false(), c.display(tout));
            VERIFY(!sc.is_always_false());
            if (!sc.is_always_true())
                deps.push_back(c.propagate(sc, c.explain_weak_eval(sc), "explain_overlap value bounds"));
            t.reset(lo.manager());
            t = c.value(mod(e.value, rational::power_of_two(aw)), aw);
#if DEBUG_EXPLAIN_OVERLAP
            verbose_stream() << "    t' " << t << "\n";
#endif
            if (c.inconsistent())
                verbose_stream() << "inconsistent overlap " << sc << " " << "\n";
        }

/*
        if (ebw < abw) {
            // NOTE: this doesn't work, because the projected interval may be empty if we just project 'after' instead of the hole's complement
            t *= rational::power_of_two(abw - ebw);
            lo *= rational::power_of_two(abw - ebw);
            hi *= rational::power_of_two(abw - ebw);
        }
*/

        if (abw < aw)
            t *= rational::power_of_two(aw - abw);

        auto sc = cs.ult(t - lo, hi - lo);
#if DEBUG_EXPLAIN_OVERLAP
        // verbose_stream() << "    lhs: " << t  << " - (" << lo << ")     ==     " << (t  - lo) << "\n";
        // verbose_stream() << "    rhs: " << hi << " - (" << lo << ")     ==     " << (hi - lo) << "\n";
        // verbose_stream() << "    ult: " << sc << "\n";
        // verbose_stream() << "    eval " << sc.eval() << "\n";
        // verbose_stream() << "    weval " << sc.weak_eval(c.get_assignment()) << "\n";
        // verbose_stream() << "    seval " << sc.strong_eval(c.get_assignment()) << "\n";
#endif
        SASSERT(!sc.is_always_false());
        if (!sc.is_always_true())
            deps.push_back(c.propagate(sc, c.explain_weak_eval(sc), "explain_overlap linking constraint"));
        if (c.inconsistent()) {
            verbose_stream() << "inconsistent ult " << sc << " " << "\n";
            verbose_stream() << "before bw " << ebw << " " << bw << " " << *e.e << "\nafter  bw " << abw << " " << aw << " " << *after.e << "\n";
            display(verbose_stream());
            // UNREACHABLE();
        }
    }

    void viable::pin(pdd& t, rational const& value, unsigned ebw, dd::pdd_manager& target, dependency_vector& deps) {
        unsigned const bw = t.power_of_2();
        auto const& p2b = t.manager().two_to_N();
        auto const& p2eb = rational::power_of_two(bw - ebw);
        // let coeff = 2^{bw - ebw}
        // let assume coeff * x \not\in [s, t[
        // Then value is chosen, min x . coeff * x >= t.
        // In other words:
        //
        // x >= t div coeff
        // => t <= coeff * x
        
        // (x - 1) * coeff < t <= x * coeff
        
        // a < x <= b <=>
        // a + 1 <= x < b + 1
        // x - a - 1 < b - a

        auto vlo = c.value(mod((value - 1) * p2eb + 1, p2b), bw);
        auto vhi = c.value(mod(value * p2eb + 1, p2b), bw);

        verbose_stream() << "    assignment: " << c.get_assignment() << "\n";
        if (c.is_assigned(1))
            verbose_stream() << "    v1 = " << c.get_assignment().value(1) << "\n";
#if 1
        verbose_stream() << "    value " << value << "\n";
        verbose_stream() << "    t " << t << "\n";
        verbose_stream() << "    [" << vlo << " " << vhi << "[\n";
        // verbose_stream() << "    before bw " << ebw << " " << bw << " " << *e.e << "\n";
        // verbose_stream() << "    after  bw " << abw << " " << aw << " " << *after.e << "\n";
        if (!t.is_val())
            verbose_stream() << "    symbolic t : " << t << "\n";
        verbose_stream() << "    " << t - vlo << " " << vhi - vlo << "\n";
#endif
        auto sc = cs.ult(t - vlo, vhi - vlo);
        verbose_stream() << "    sc " << sc << "\n";
        CTRACE("bv", sc.is_always_false(), c.display(tout));

        VERIFY(!sc.is_always_false());
        if (!sc.is_always_true())
            deps.push_back(c.propagate(sc, c.explain_weak_eval(sc), "explain_overlap value bounds"));
        t.reset(target);
        t = c.value(value, target.power_of_2());
        // verbose_stream() << "    t' " << t << "\n";
        if (c.inconsistent())
            verbose_stream() << "inconsistent pin " << sc << " " << "\n";
    }

    /*
     * We have
     * - before  2^k   x \not\in [?,hi[  effective bit-width bew   pdd-size bw   (k = bw - bew)
     * - after   2^k'  y \not\in [lo,?[  effective bit-width aew   pdd-size aw   (k' = aw - aew)
     * - e       2^k'' z \not\in [?,t[   effective bit-width eew   pdd-size ew   (k'' = ew - eew)
     * - eew < bew, eew < aew
     *
     * where '?' is a placeholder for terms we don't care about.
     *
     *
     * TODO: maybe here: after.lo[eew] \in [e.lo+1, e.hi+1] ????  (+1 on value level, so needs proper 2^k adjustment)
     *
     *  before  x[bew] \not\in [?,ceil(hi/2^k)[
     *  after   y[aew] \not\in [ceil(lo/2^k'),?[
     *  e       z[eew] \not\in [?,ceil(t/2^k'')[
     *
     * Conceptually:
     * - link last interval of the hole ('e') with the complement of the hole projected onto [eew]
     * - Encode: ceil(t/2^k'') \in [ ceil(lo/2^k')[eew], ceil(hi/2^k)[eew] [
     *
     * If bw == aw == ew:
     *  If bew == aew:
     * 
     * Else, normalize to aw always? then we don't have to evaluate lo.
     */
    void viable::explain_hole_overlap(explanation const& before, explanation const& e, explanation const& after, dependency_vector& deps) {
        //  before      hole       after
        // [----------[     [----------[    bit-width k
        //          [--[--[--[              bit-width hole_bits < k
        //
        // e is the last entry of the hole.
        // we need the constraint:
        //      e.hi in [ after.lo[eew] ; before.hi[eew] [
        pdd t = e.e->interval.hi();
        pdd lo = after.e->interval.lo();
        pdd hi = before.e->interval.hi();

        unsigned const bw = c.size(before.e->var);
        unsigned const bew = before.e->bit_width;
        unsigned const ew = c.size(e.e->var);       // e width
        unsigned const eew = e.e->bit_width;        // e effective width
        unsigned const aw = c.size(after.e->var);
        unsigned const aew = after.e->bit_width;

        SASSERT(eew < bew);
        SASSERT(eew < aew);
        return;   // TODO: disabled for now

        verbose_stream() << "explain_hole_overlap:\n";
        display_explain(verbose_stream() << "    before ", before) << "\n";
        display_explain(verbose_stream() << "    e      ", e) << "\n";
        display_explain(verbose_stream() << "    after  ", after) << "\n";
        verbose_stream() << "    bw " << bw << " bew " << bew << "\n";
        verbose_stream() << "    ew " << ew << " eew " << eew << "\n";
        verbose_stream() << "    aw " << aw << " aew " << aew << "\n";
        verbose_stream() << "    t " << t << "\n";
        verbose_stream() << "    lo " << lo << " hi " << hi << "\n";
        verbose_stream() << "    hole size " << r_interval::len(get_covered_interval(before).hi(), get_covered_interval(after).lo(), rational::power_of_two(m_num_bits)) << "\n";

        if (t.is_val() && lo.is_val() && hi.is_val()) {
            return;  // can abort early
        }

        if (bw == aw && aw == ew && bew == aew) {

            static int counter = 0;
            ++counter;
            verbose_stream() << "hole_overlap counter " << counter << "\n";
            if (counter != 3)
                return;

            // encode: ceil(t/2^k'') \in [ ceil(lo/2^k)[eew], ceil(hi/2^k)[eew] [

/*
From ZstJOJYeMR15.smt2

explain_kind conflict
v0:  v4:5@0 value=16  v0:20@0
v0[20] := 1048561 v0 [20*v1 + 21 ; 20*v1 + 1[ := [5;-15[  src -20 <= 20*v1 + -1*v0;
v0[5] := 16 v0[5] [-491520 = (2^15*17) ; 2^15*16[ := [17;16[  deps 16 == v0 [5]@0 src
v0[20] := 1048561 v0 [20*v1 + 21 ; 20*v1 + 1[ := [5;-15[  src -20 <= 20*v1 + -1*v0;
*/

            if (eew < ew || ew != aw) {
                // evaluate t
                pin(t, e.value, eew, lo.manager(), deps);
            }

            t *= rational::power_of_two(aew - eew);
            lo *= rational::power_of_two(aew - eew);
            hi *= rational::power_of_two(aew - eew);
            NOT_IMPLEMENTED_YET();

            // TODO
        }

    }

    r_interval viable::get_covered_interval(explanation const& e) const {
        rational const& lo = e.e->interval.lo_val();
        rational const& hi = e.e->interval.hi_val();
        rational const& mod_value = rational::power_of_two(e.e->bit_width);
        rational const& len = r_interval::len(lo, hi, mod_value);
        rational const& covered_hi = e.value;
        rational const& covered_lo = mod2k(covered_hi - len, m_num_bits);
        return r_interval::proper(covered_lo, covered_hi);
    }

    /*
     * We have:
     * - before  2^k   x \not\in [?,lo[  effective bit-width bew   pdd-size bw   (k = bw - bew)
     * - after   2^k'  y \not\in [hi,?[  effective bit-width aew   pdd-size aw   (k' = aw - aew)
     * - hole [lo,hi[ that is filled by intervals of bit-width 'hole_bits'
     *
     * where '?' is a placeholder for terms we don't care about.
     *
     * before  x[bew] \not\in [?,ceil(lo/2^k)[
     * after   y[aew] \not\in [ceil(hi/2^k'),?[
     * Let ew := min(bew, aew)
     *
     * Conceptually:
     * - the hole, projected onto lower size ew, must be of size < 2^hole_bits
     * - Encode: ceil(hi/2^k')[ew] - ceil(lo/2^k)[ew] < 2^hole_bits
     *
     *
     * (If aw == bw)
     * If bew < aew:
     *    ceil(hi/2^k')[bew] - ceil(lo/2^k)[bew] < 2^hole_bits
     *    2^k*ceil(hi/2^k') - 2^k*ceil(lo/2^k) < 2^(k+hole_bits)
     *          (note hole_bits < bew, thus k + hole_bits < k + bew = bw)
     *
     *
     *
     *
     */
    void viable::explain_hole_size(explanation const& before, explanation const& after, unsigned hole_bits, dependency_vector& deps) {
        //  before      hole       after
        // [----------[     [----------[    bit-width k
        //           [-------[              bit-width hole_bits < k
        //
        // The hole can only be covered by lower intervals if
        //
        //          hole_len < 2^hole_bits
        //
        // i.e., after->lo() - before->hi() < 2^hole_bits.

        unsigned const bw = c.size(before.e->var);
        unsigned const bew = before.e->bit_width;
        unsigned const aw = c.size(after.e->var);
        unsigned const aew = after.e->bit_width;
        SASSERT(bew <= bw);
        SASSERT(aew <= aw);
        SASSERT(hole_bits < aew);
        SASSERT(hole_bits < bew);

        verbose_stream() << "explain_hole: " << hole_bits << " bits\n";
        display_explain(verbose_stream() << "    before: " << bew << " " << bw << "   ", before) << "\n";
        display_explain(verbose_stream() << "    after:  " << aew << " " << aw << "   ", after)  << "\n";
        verbose_stream() << "    before covers: " << get_covered_interval(before) << "\n";
        verbose_stream() << "    after covers:  " << get_covered_interval(after)  << "\n";

        // hole is from t1 to t2
        pdd t1 = before.e->interval.hi();
        pdd t2 = after.e->interval.lo();
        verbose_stream() << "    t1 " << t1 << " t2 " << t2 << "\n";
        verbose_stream() << "    (" << t2 << ") - (" << t1 << ") < " << rational::power_of_two(hole_bits) << "\n";
        rational a;
        verbose_stream() << "    ok? " << c.try_eval(t1, a) << " eval(t1) = " << a << "\n";
        verbose_stream() << "    ok? " << c.try_eval(t2, a) << " eval(t2) = " << a << "\n";

        // rational after_len = r_interval::len(after.e->interval.lo_val(), after.e->interval.hi_val(), rational::power_of_two(aew));
        // rational after_covered_lo = mod2k(after.value - after_len, m_num_bits);
        // auto after_covered_ivl = r_interval::proper(after_covered_lo, after.value);
        // // verbose_stream() << "   after_len " << after_len << "\n";
        // // verbose_stream() << "   after_covered_lo " << after_covered_lo << "\n";
        // // verbose_stream() << "   after_covered_ivl " << after_covered_ivl << "\n";
        // SASSERT_EQ(after_covered_ivl.len(rational::power_of_two(m_num_bits)), after_len);

        if (get_covered_interval(after).contains(before.value)) {
            // this check is still needed as long as we do not prune the 'last' interval
            verbose_stream() << "    not a real hole (subsumption opportunity)\n";
            return;
        }

        SASSERT(!get_covered_interval(after).contains(before.value));

        rational hole_len = r_interval::len(before.value, get_covered_interval(after).lo(), rational::power_of_two(m_num_bits));
        verbose_stream() << "    hole_len " << hole_len << " should be < " << rational::power_of_two(hole_bits) << "\n";
        VERIFY(hole_len < rational::power_of_two(hole_bits));  // otherwise we missed a conflict at lower bit-width

        // no constraint needed for constant bounds
        if (t1.is_val() && t2.is_val())
            return;

        if (aw != bw) {
            // TODO: eval bounds?
            // TODO: eval t1 because it is a "high" value, and project/embed into pdd of t2
            return;
            NOT_IMPLEMENTED_YET();
        }

        if (aew != bew) {
            // TODO: multiply with 2^k appropriately
            SASSERT(aw == bw);
            if (bew < aew)
                t1 *= rational::power_of_two(aew - bew);
            if (aew < bew)
                t2 *= rational::power_of_two(bew - aew);
            return;
            NOT_IMPLEMENTED_YET();
        }
        if (bew != bw || aew != aw) {
            return;
            NOT_IMPLEMENTED_YET();
        }

        auto sc = cs.ult(t2 - t1, rational::power_of_two(hole_bits));
        verbose_stream() << "    constraint " << sc << "\n";
        VERIFY(!sc.is_always_false());
        if (!sc.is_always_true())
            deps.push_back(c.propagate(sc, c.explain_weak_eval(sc), "explain_hole"));
    }

    /*
     * Register constraint at index 'idx' as unitary in v.
     * Returns 'multiple' when either intervals are unchanged or there really are multiple values left.
     */
    find_t viable::add_unitary(pvar v, constraint_id idx, rational& var_value) {

        if (c.is_assigned(v))
            return find_t::multiple;
        auto [sc, d, truth_value] = c.m_constraint_index[idx.id];
        SASSERT(truth_value != l_undef);
        if (truth_value == l_false)
            sc = ~sc;

        if (!sc.is_linear()) 
            return find_t::multiple;        

        entry* ne = alloc_entry(v, idx);
        if (!m_forbidden_intervals.get_interval(sc, v, *ne)) {
            m_alloc.push_back(ne);
            return find_t::multiple;
        }

        // verbose_stream() << "v" << v << " " << sc << " " << ne->interval << "\n";
        TRACE("bv", tout << "v" << v << " " << sc << " " << ne->interval << "\n"; display_one(tout, ne) << "\n");

        if (ne->interval.is_currently_empty()) {
            m_alloc.push_back(ne);
            return find_t::multiple;
        }

        if (ne->coeff == 1) 
            intersect(v, ne);        
        else if (ne->coeff == -1) 
            insert(ne, v, m_diseq_lin, entry_kind::diseq_e);
        else if (!ne->coeff.is_power_of_two())
            insert(ne, v, m_equal_lin, entry_kind::equal_e);
        else if (ne->interval.is_full())
            insert(ne, v, m_equal_lin, entry_kind::equal_e);            
        else {
            unsigned const w = c.size(v);
            unsigned const k = ne->coeff.parity(w);
            SASSERT(k > 0);

            IF_VERBOSE(3, display_one(verbose_stream() << "try to reduce entry: ", ne) << "\n");

            // reduction of coeff gives us a unit entry
            //
            // 2^k x \not\in [ lo ; hi [
            //
            // new_lo = lo[w-1:k]      if lo[k-1:0] = 0
            //          lo[w-1:k] + 1  otherwise
            //        = ceil( lo / 2^k )
            //
            // new_hi = hi[w-1:k]      if hi[k-1:0] = 0
            //          hi[w-1:k] + 1  otherwise
            //        = ceil( hi / 2^k )
            //
            // Reference: Fig. 1 (dtrim) in BitvectorsMCSAT

            TRACE("bv", display_one(tout << "try to reduce entry: ", ne) << "\n");
            pdd const& pdd_lo = ne->interval.lo();
            pdd const& pdd_hi = ne->interval.hi();
            rational const& lo = ne->interval.lo_val();
            rational const& hi = ne->interval.hi_val();
            rational twoK = rational::power_of_two(k);

            rational new_lo = machine_div2k(mod2k(lo + twoK - 1, w), k);
            pdd lo_eq = pdd_lo * rational::power_of_two(w - k);
            if (mod2k(lo, k).is_zero()) {
                if (!lo_eq.is_zero())
                    ne->side_cond.push_back(cs.eq(lo_eq));
            }
            else {
                SASSERT(!lo_eq.is_val() || !lo_eq.is_zero());
                if (!lo_eq.is_val())
                    ne->side_cond.push_back(~cs.eq(lo_eq));
            }

            rational new_hi = machine_div2k(mod2k(hi + twoK - 1, w), k);
            pdd hi_eq = pdd_hi * rational::power_of_two(w - k);
            if (mod2k(hi, k).is_zero()) {
                if (!hi_eq.is_zero())
                    ne->side_cond.push_back(cs.eq(hi_eq));
            }
            else {
                SASSERT(!hi_eq.is_val() || !hi_eq.is_zero());
                if (!hi_eq.is_val())
                    ne->side_cond.push_back(~cs.eq(hi_eq));
            }

            //
            // If new_lo = new_hi it means that
            //   mod(ceil(lo / 2^k), 2^(w-k)) = mod(ceil(hi / 2^k), 2^(w-k))
            // or
            //   div(mod(lo + 2^k - 1, 2^w), 2^k) = div(mod(hi + 2^k - 1, 2^w), 2^k)
            // but we also have lo != hi.
            //
            // Cases:
            //   0 < lo < hi:     empty  (2^k does not divide any of [lo, hi[)
            //   0 == lo < hi:    full
            //   0 < hi < lo:     full
            //   0 == hi < lo:    empty
            //
            if (new_lo == new_hi) {
                bool is_empty = true;
                if (lo.is_zero()) {
                    SASSERT(!hi.is_zero());
                    // 0 == lo < hi
                    ne->side_cond.push_back(cs.eq(pdd_lo));
                    ne->side_cond.push_back(~cs.eq(pdd_hi));
                    is_empty = false;
                }
                else if (!hi.is_zero() && hi < lo) {
                    // 0 < hi < lo
                    ne->side_cond.push_back(~cs.eq(pdd_hi));
                    ne->side_cond.push_back(cs.ult(pdd_hi, pdd_lo));
                    is_empty = false;
                }
                if (is_empty) {
                    m_alloc.push_back(ne);
                    return find_t::multiple;
                }
                else {
                    ne->interval = eval_interval::full();
                    ne->coeff = 1;
                    m_explain.reset();
                    m_explain.push_back({ ne, rational::zero() });
                    m_fixed_bits.reset();
                    m_var = v;
                    return find_t::empty;
                }
            }

            // display_one(verbose_stream() << "original: ", ne) << "\n";
            ne->coeff = 1;
            ne->interval = eval_interval::proper(pdd_lo, new_lo, pdd_hi, new_hi);
            ne->bit_width -= k;

            // display_one(verbose_stream() << "reduced: ", ne) << "\n";
            // verbose_stream() << "to bw " << ne->bit_width << "\n";
            TRACE("bv", display_one(tout << "reduced: ", ne) << "\n");
            intersect(v, ne);
        }
        if (ne->interval.is_full()) {
            m_explain.reset();
            m_explain.push_back({ ne, rational::zero() });
            m_fixed_bits.reset();
            m_var = v;
            return find_t::empty;
        }
        return find_viable(v, var_value);
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
        SASSERT(well_formed(m_units[v]));
        m_alloc.push_back(e);
    }

    void viable::push_viable(entry* e) {
        // display_one(verbose_stream() << "Push entry: ", e) << "\n";
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


    std::ostream& viable::display_one(std::ostream& out, entry const* e) const {
        auto& m = c.var2pdd(e->var);
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
            out << val_pp(m, p, true) << "*v" << e->var << " + " << val_pp(m, q_);
            out << (e->src[0].is_positive() ? " > " : " >= ");
            out << val_pp(m, r, true) << "*v" << e->var << " + " << val_pp(m, s_);
            out << " ] ";
        }
        else {
            if (e->coeff != 1)
                out << e->coeff << " * ";
            out << "v" << e->var;
            if (e->bit_width != c.size(e->var))
                out << "[" << e->bit_width << "]";
            out << " " << e->interval << " ";
        }
        if (!e->deps.empty())
            out << " deps " << e->deps;
        if (e->side_cond.empty())
            ;
        else if (e->side_cond.size() <= 5)
            out << " side-conds " << e->side_cond;
        else
            out << " side-conds " << e->side_cond.size() << " side-conditions";
        out << " src ";
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

    std::ostream& viable::display_all(std::ostream& out, entry const* e, char const* delimiter) const {
        if (!e)
            return out;
        entry const* first = e;
        unsigned count = 0;
        do {
            display_one(out, e) << delimiter;
            e = e->next();
            ++count;
            if (count > 10) {
                out << " ... (total: " << count << " entries)";
                break;
            }
        } 
        while (e != first);
        return out;
    }

    std::ostream& viable::display(std::ostream& out) const {
        for (unsigned v = 0; v < m_units.size(); ++v) {
            for (auto const& layer : m_units[v].get_layers()) {
                if (!layer.entries)
                    continue;
                out << "v" << v << "[" << layer.bit_width << "]: ";
                display_all(out, layer.entries, " ");
                out << "\n";
            }
        }
        return out;
    }

    std::ostream& viable::display_state(std::ostream& out) const {
        out << "v" << m_var << ":";
        for (auto const& slice : m_suffixes) {
            out << "  v" << slice.child << ":" << c.size(slice.child) << "@" << slice.offset;
            if (c.is_assigned(slice.child))
                out << " value=" << c.get_assignment().value(slice.child);
        }
        out << "\n";
        return out;
    }

    std::ostream& viable::display_explain(std::ostream& out) const {
        out << "explain_kind " << m_explain_kind << "\n";
        display_state(out);
        for (auto const& e : m_explain)
            display_explain(out, e) << "\n";
        return out;
    }

    std::ostream& viable::display_explain(std::ostream& out, explanation const& e) const {
        return display_one(out << "v" << e.e->var << "[" << e.e->bit_width << "] := " << e.value << " ", e.e);
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
            CTRACE("bv", !e->active, tout << "inactive entry v" << e->var << " " << e->interval << "\n"; display(tout));
            if (!e->active)
                return false;

            if (e->interval.is_full())
                return e->next() == e;
            if (e->interval.is_currently_empty())
                return false;

            auto* n = e->next();
            if (n != e && e->interval.currently_contains(n->interval)) {
                TRACE("bv", tout << "currently contains\n");
                return false;
            }

            if (n == first)
                break;
            if (e->interval.lo_val() >= n->interval.lo_val()) {
                TRACE("bv", tout << "lo-val >= n->lo_val\n");
                return false;
            }
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
            if (!well_formed(l.entries)) {
                TRACE("bv", tout << "entries are not well-formed\n");
                return false;
            }
            if (!all_of(dll_elements(l.entries), [&l](entry const& e) { return e.bit_width == l.bit_width; })) {
                TRACE("bv", tout << "elements don't have same bit-width\n");
                return false;
            }
            if (!first && prev_width >= l.bit_width) {
                TRACE("bv", tout << "previous width is " << prev_width << " vs " << l.bit_width << "\n");
                return false;
            }
            first = false;
            prev_width = l.bit_width;
        }
        return true;
    }
}
