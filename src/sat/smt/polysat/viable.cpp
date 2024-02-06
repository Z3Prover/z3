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

    bool viable::assign(pvar v, rational const& value) {
        m_var = v;
        m_explain_kind = explain_t::none;
        m_num_bits = c.size(v);
        m_fixed_bits.init(v);
        m_explain.reset();
        init_overlaps(v);
        bool first = true;
        while (true) {
            for (auto const& [w, offset] : m_overlaps) {
                for (auto& layer : m_units[w].get_layers()) {
                    entry* e = find_overlap(w, layer, value);
                    if (!e)
                        continue;
                    
                    m_explain.push_back({ e, value });
                    m_explain_kind = explain_t::assignment;
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
        init_overlaps(v);
        m_explain_kind = explain_t::none;

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

    void viable::init_overlaps(pvar v) {
        m_overlaps.reset();
        c.get_bitvector_suffixes(v, m_overlaps);
        std::sort(m_overlaps.begin(), m_overlaps.end(), [&](auto const& x, auto const& y) { return c.size(x.v) < c.size(y.v); });
    }


    // 
    // 
    // from smallest size(w) overlap [w] to largest
    //     from smallest bit_width layer [bit_width, entries] to largest
    //         check if val is allowed by entries or advance val to next allowed value
    // 

    viable::entry* viable::find_overlap(rational& val) {

        entry* last = nullptr;
        for (auto const& [w, offset] : m_overlaps) {
            for (auto& layer : m_units[w].get_layers()) {
                entry* e = find_overlap(w, layer, val);
                if (!e)
                    continue;
                last = e;
                update_value_to_high(val, e);
                m_explain.push_back({ e, val });
                if (is_conflict()) {
                    m_explain_kind = explain_t::conflict;
                    return nullptr;
                }
            }
        }
        return last;
    }

    viable::entry* viable::find_overlap(pvar w, layer& l, rational const& val) {
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
        auto last = m_explain.back();
        auto after = last;

        verbose_stream() << m_explain_kind << "\n";

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
                auto d = c.propagate(sc, c.explain_weak_eval(sc));
                if (c.inconsistent()) {
                    verbose_stream() << "inconsistent " << d << " " << sc << "\n";
                }
                result.push_back(d);
            }
            result.append(e->deps);
            if (!index.is_null())
                result.push_back(c.get_dependency(index));
        };

        if (last.e->interval.is_full()) {
            explain_entry(last.e);
            SASSERT(m_explain.size() == 1);
            unmark();
            return result;
        }

        SASSERT(m_explain_kind != explain_t::none);

        for (unsigned i = m_explain.size() - 1; i-- > 0; ) {
            auto e = m_explain[i];
            explain_overlap(e, after, result);
            after = e;
            explain_entry(e.e);           
            if (e.e == last.e)
                break;
        }
        if (m_explain_kind == explain_t::propagation) {
            // assume first and last have same bit-width
            auto first = m_explain[0];
            SASSERT(first.e->bit_width == last.e->bit_width);
            explain_entry(first.e);
            // add constraint that there is only a single viable value.         
            auto sc = cs.eq(last.e->interval.hi() + 1, first.e->interval.lo());
            auto exp = c.propagate(sc, c.explain_weak_eval(sc));
            if (c.inconsistent()) {
                verbose_stream() << "inconsistent " << sc << " " << exp << "\n";
            }
            result.push_back(exp);            
        }
        if (m_explain_kind == explain_t::assignment) {
            // there is just one entry
            SASSERT(m_explain.size() == 1);
            explain_entry(last.e);
            auto exp = propagate_from_containing_slice(last.e, last.value, result);
            if (!exp.is_null()) {
                result.clear();
                result.push_back(exp);
            }
        }
        unmark();
        if (c.inconsistent())
            verbose_stream() << "inconsistent after explain\n";
        return result;
    }

    dependency viable::propagate_from_containing_slice(entry* e, rational const& value, dependency_vector const& e_deps) {        
        for (auto const& slice : m_overlaps)
            if (auto d = propagate_from_containing_slice(e, value, e_deps, slice); !d.is_null())
                return d;
        return null_dependency;
    }

    dependency viable::propagate_from_containing_slice(entry* e, rational const& value, dependency_vector const& e_deps, offset_slice const& slice) {
        auto [w, offset] = slice;
        if (w == m_var)
            return null_dependency;
        verbose_stream() << "v" << m_var << " size " << c.size(m_var) << ", v" << w << " size " << c.size(w) << " offset " << offset << "\n";

        // Let:
        // v = m_var[e->bit_width-1:0]
        // v = concat(x, y, z)
        // y = w[y_sz-1:0]

        //                      e->bit_width
        // m_var = ???????vvvvvvvvvvvvvvvvvvvvvvv
        //                      wwwwwwww
        //                xxxxxxyyyyyyyyzzzzzzzzz
        //                        y_sz    offset
        //
        // or:
        // m_var = ???????vvvvvvvvvvvvvvvvvvvvvvv
        //             wwwwwwwwwwwwwwwww
        //                yyyyyyyyyyyyyyzzzzzzzzz
        //
        // or:
        // m_var = ?????????????????vvvvvvvvvvvvv
        //             wwwwwwwww
        unsigned const v_sz = e->bit_width;
        if (offset >= v_sz)
            return null_dependency;

        unsigned const w_sz = c.size(w);
        unsigned const z_sz = offset;
        unsigned const y_sz = std::min(w_sz, v_sz - z_sz);
        unsigned const x_sz = v_sz - y_sz;

        rational const& w_shift = rational::power_of_two(w_sz - y_sz);

        verbose_stream() << "v_sz " << v_sz << " w_sz " << w_sz << " / x_sz " << x_sz << " y_sz " << y_sz << " z_sz " << z_sz << "\n";
        display_one(verbose_stream() << "entry: ", e) << "\n";
        verbose_stream() << "value " << value << "\n";

        SASSERT(!e->interval.is_full());
        rational const& lo = e->interval.lo_val();
        rational const& hi = e->interval.hi_val();

        r_interval const v_ivl  = r_interval::proper(lo, hi);
        verbose_stream() << "propagate interval " << v_ivl << " from v" << m_var << " to v" << w << "[" << y_sz << "]" << "\n";

        // TODO: by the time we call viable::assign, m_fixed_bits only contains a single slice with 'value'.
        //       if we had access to the actually fixed slices (not just fixed because of the latest assignment),
        //       we could chop off fixed and non-fixed parts according to actually fixed slices;
        //       getting rid of the distinction into two separate cases below.

        // more general interval, without taking into account fixed values
        {
            r_interval const yz_ivl = chop_off_upper(v_ivl,  x_sz, y_sz + z_sz);  // chop off x-part
            r_interval const y_ivl  = chop_off_lower(yz_ivl, y_sz,        z_sz);  // chop off z-part

            if (y_ivl.is_full()) {
                // no value for y
                UNREACHABLE();  // without fixed x or z, this is only possible if e->interval was full
            }
            else if (!y_ivl.is_empty()) {
                // proper interval
                verbose_stream() << "=>  v" << w << "[" << y_sz << "] not in " << y_ivl << "\n";
                auto sc = ~cs.ult(w_shift * (c.var(w) - y_ivl.lo()), w_shift * (y_ivl.hi() - y_ivl.lo()));
                dependency_vector deps;
                deps.append(e_deps);  // explains e
                deps.push_back(offset_claim{m_var, slice});  // explains m_var[...] = w
                return c.propagate(sc, deps, "propagate from containing slice (general)");
            }
            else {
                SASSERT(y_ivl.is_empty());
                // y is unconstrained, nothing to do here
            }
        }

        // tighter interval, but depends on fixed values
        {
            rational const var_x_value = x_sz > 0 ? machine_div2k(value, y_sz + z_sz) : rational(0);
            rational const x_value = x_sz > 0 ? mod2k(machine_div2k(value, y_sz + z_sz), x_sz) : rational(0);
            rational const z_value = z_sz > 0 ? mod2k(value, z_sz) : rational(0);
            r_interval const yz_ivl = chop_off_upper(v_ivl,  x_sz, y_sz + z_sz, &x_value);  // chop off x-part
            r_interval const y_ivl  = chop_off_lower(yz_ivl, y_sz,        z_sz, &z_value);  // chop off z-part

            if (y_ivl.is_full()) {
                // no value for y
                // TODO: the signed_constraint to propagate would be 'false'
                NOT_IMPLEMENTED_YET();
            }
            else if (!y_ivl.is_empty()) {
                // proper interval
                verbose_stream() << "=>  v" << w << "[" << y_sz << "] not in " << y_ivl << " using x=" << x_value << " z=" << z_value << "\n";
                auto sc = ~cs.ult(w_shift * (c.var(w) - y_ivl.lo()), w_shift * (y_ivl.hi() - y_ivl.lo()));
                dependency_vector deps;
                deps.append(e_deps);  // explains e
                deps.push_back(offset_claim{m_var, slice});  // explains m_var[...] = w
                if (x_sz > 0) {
                    deps.push_back(fixed_claim{m_var, var_x_value, y_sz + z_sz, x_sz + (c.size(m_var) - v_sz)});  // m_var[upper] = var_x_value
                    // stronger but crashes in bv_plugin::explain_slice, TODO: why?
                    // deps.push_back(fixed_claim{m_var, x_value, y_sz + z_sz, x_sz});  // v[upper] = x_value
                }
                if (z_sz > 0)
                    deps.push_back(fixed_claim{m_var, z_value, 0, z_sz});  // v[lower] = z_value
                return c.propagate(sc, deps, "propagate from containing slice (fixed)");
            }
            else {
                SASSERT(y_ivl.is_empty());
                // y is unconstrained, nothing to do here
            }
        }

        return null_dependency;
    }


    /// Let x = concat(y, z) and x \not\in [lo;hi[.
    /// Returns an interval I such that z \not\in I.
    r_interval viable::chop_off_upper(r_interval const& i, unsigned const Ny, unsigned const Nz, rational const* y_fixed_value) {
        if (i.is_full())
            return r_interval::full();
        if (i.is_empty())
            return r_interval::empty();
        if (Ny == 0)
            return i;
        unsigned const Nx = Ny + Nz;
        rational const& lo = i.lo();
        rational const& hi = i.hi();
        if (y_fixed_value) {
            rational const& n = *y_fixed_value;
            rational const lo_d = machine_div2k(lo, Nz);
            rational const hi_d = machine_div2k(hi, Nz);
            rational z_lo = (lo_d == n) ? mod2k(lo, Nz) : rational(0);
            rational z_hi = (hi_d == n) ? mod2k(hi, Nz) : rational(0);
            if (z_lo != z_hi)
                return r_interval::proper(std::move(z_lo), std::move(z_hi));
            else if (r_interval::contains(lo, hi, n * rational::power_of_two(Nz)))
                return r_interval::full();  // no value for z
            else
                return r_interval::empty();  // z unconstrained
        }
        else {
            rational const Mx = rational::power_of_two(Nx);
            rational const Mz = rational::power_of_two(Nz);
            rational const len = r_interval::len(lo, hi, Mx);
            if (len > Mx - Mz)
                return r_interval::proper(mod2k(lo, Nz), mod2k(hi, Nz));
            else
                return r_interval::empty();  // z unconstrained
        }
        UNREACHABLE();
    }

    /// Let x = concat(y, z) and x \not\in [lo;hi[.
    /// Returns an interval I such that y \not\in I.
    r_interval viable::chop_off_lower(r_interval const& i, unsigned const Ny, unsigned const Nz, rational const* z_fixed_value) {
        if (i.is_full())
            return r_interval::full();
        if (i.is_empty())
            return r_interval::empty();
        if (Nz == 0)
            return i;
        unsigned const Nx = Ny + Nz;
        rational const& lo = i.lo();
        rational const& hi = i.hi();
        if (z_fixed_value) {
            // Note: ceil(a/b) == floor((a-1)/b) + 1 for integers a,b and b > 0
            rational const& n = *z_fixed_value;
            rational y_lo = mod2k(machine_div2k(mod2k(lo - n, Nx) - 1, Nz) + 1, Ny);
            rational y_hi = mod2k(machine_div2k(mod2k(hi - n, Nx) - 1, Nz) + 1, Ny);
            if (y_lo != y_hi)
                return r_interval::proper(std::move(y_lo), std::move(y_hi));
            else if (r_interval::contains(lo, hi, y_hi * rational::power_of_two(Nz) + n))
                return r_interval::full();  // no value for y
            else
                return r_interval::empty();  // y unconstrained
        }
        else {
            rational const Mx = rational::power_of_two(Nx);
            rational const Mz = rational::power_of_two(Nz);
            rational const len = r_interval::len(lo, hi, Mx);
            if (len >= Mz) {
                rational y_lo = mod2k(machine_div2k(lo - 1, Nz) + 1, Ny);
                rational y_hi = machine_div2k(hi, Nz);
                return r_interval::proper(std::move(y_lo), std::move(y_hi));
            }
            else
                return r_interval::empty();  // y unconstrained
        }
        UNREACHABLE();
    }

    /*
     * For two consecutive intervals 
     * 
     * - 2^kx \not\in [lo, hi[, 
     * - 2^k'y \not\in [lo', hi'[
     * - a value v such that 
     *   - 2^kv \not\in [lo, hi[
     *   - 2^k'v \in [lo', hi'[
     *   - hi \in ] (v - 1) * 2^{bw - ebw} ; v * 2^{bw - ebw} ]
     * 
     * Where:
     *  - bw is the width of x, aw the width of y
     *  - ebw is the bit-width of x, abw the bit-width of y
     *  - k = bw - ebw, k' = aw - abw
     * 
     * We want to encode the constraint that (2^k' hi)[w'] in [lo', hi'[
     * 
     * Note that x in [lo, hi[ <=> x - lo < hi - lo
     * If bw = aw, ebw = abw there is nothing else to do.
     *    - hi \in [lo', hi'[ 
     * 
     * If bw != aw or aw < bw:
     *    - hi \in ] (v - 1) * 2^{bw - ebw} ; v * 2^{bw - ebw} ]
     *    - hi := v mod aw
     * 
     * - 2^k'hi \in [lo', hi'[
     * 
     */

    void viable::explain_overlap(explanation const& e, explanation const& after, dependency_vector& deps) {
        auto bw = c.size(e.e->var);
        auto ebw = e.e->bit_width;
        auto aw = c.size(after.e->var);
        auto abw = after.e->bit_width;
        auto t = e.e->interval.hi();
        auto lo = after.e->interval.lo();
        auto hi = after.e->interval.hi();

        SASSERT(abw <= aw);
        SASSERT(ebw <= bw);

        if (ebw < bw || aw != bw) {
            auto const& p2b = rational::power_of_two(bw);
            auto const& p2eb = rational::power_of_two(bw - ebw);
            // let coeff = 2^{bw - ebw}
            // let assume coeff * x \not\in [lo, t[
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

#if 0
            verbose_stream() << "value " << e.value << "\n";
            verbose_stream() << "t " << t << "\n";
            verbose_stream() << "[" << vlo << " " << vhi << "[\n";
            verbose_stream() << "before bw " << ebw << " " << bw << " " << *e.e << "\nafter  bw " << abw << " " << aw << " " << *after.e << "\n";
            if (!t.is_val())
                IF_VERBOSE(0, verbose_stream() << "symbolic t : " << t << "\n");
            verbose_stream() << t - vlo << " " << vhi - vlo << "\n";

#endif
            auto sc = cs.ult(t - vlo, vhi - vlo);
            CTRACE("bv", sc.is_always_false(), c.display(tout));
                
            VERIFY(!sc.is_always_false());
            if (!sc.is_always_true())
                deps.push_back(c.propagate(sc, c.explain_weak_eval(sc)));
            t.reset(lo.manager());
            t = c.value(mod(e.value, rational::power_of_two(aw)), aw);
            // verbose_stream() << "after " << t << "\n";
            if (c.inconsistent())
                verbose_stream() << "inconsistent overlap " << sc << " " << "\n";
        }

        if (abw < aw) 
            t *= rational::power_of_two(aw - abw);            
        
        auto sc = cs.ult(t - lo, hi - lo);
        SASSERT(!sc.is_always_false());
        if (!sc.is_always_true())
            deps.push_back(c.propagate(sc, c.explain_weak_eval(sc)));
        if (c.inconsistent()) {
            verbose_stream() << "inconsistent ult " << sc << " " << "\n";
            verbose_stream() << "before bw " << ebw << " " << bw << " " << *e.e << "\nafter  bw " << abw << " " << aw << " " << *after.e << "\n";
            display(verbose_stream());
            // UNREACHABLE();
        }
    }

    /*
    * Register constraint at index 'idx' as unitary in v.
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
            //
            // new_hi = hi[w-1:k]      if hi[k-1:0] = 0
            //          hi[w-1:k] + 1  otherwise
            //
            // Reference: Fig. 1 (dtrim) in BitvectorsMCSAT
            //
            //
            // Suppose new_lo = new_hi
            // Then since ne is not full, then lo != hi
            // Cases
            // lo < hi, 2^k|lo, new_lo = lo / 2^k != new_hi = hi / 2^k
            // lo < hi, not 2^k|lo, 2^k|hi, new_lo = lo / 2^k + 1, new_hi = hi / 2^k
            //          new_lo = new_hi -> empty
            //          k = 3, lo = 1, hi = 8, new_lo = 1, new_hi = 1
            // lo < hi, not 2^k|lo, not 2^k|hi, new_lo = lo / 2^k + 1, new_hi = hi / 2^k + 1
            //          new_lo = new_hi -> empty
            //          k = 3, lo = 1, hi = 2, new_lo = 1 div 2^3 + 1 = 1, new_hi = 2 div 2^3 + 1 = 1
            // lo > hi

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
            //   mod(ceil (lo / 2^k), 2^w) = mod(ceil (hi / 2^k), 2^w)
            // or
            //   div (mod(lo + 2^k - 1, 2^w), 2^k) = div (mod(hi + 2^k - 1, 2^w), 2^k)
            // but we also have lo != hi.
            // Assume lo < hi
            // - it means 2^k does not divide any of [lo, hi[
            // so x*2^k cannot be in [lo, hi[
            // Assume lo > hi
            // - then the constraint is x*2^k not in [lo, 0[, [0, hi[
            // - it means 2^k does not divide any of [hi, lo[
            // - therefore the interval [lo, hi[ contains all the divisors of 2^k
            //

            if (new_lo == new_hi) {
                if (lo < hi) {
                    m_alloc.push_back(ne);
                    return find_t::multiple;
                }
                else {
                    // IF_VERBOSE(0, display_one(verbose_stream() << "full: ", ne) << "\n");
                    SASSERT(hi < lo);
                    ne->interval = eval_interval::full();
                    ne->coeff = 1;
                    m_explain.reset();
                    m_explain.push_back({ ne, rational::zero() });
                    m_fixed_bits.reset();
                    m_var = v;
                    return find_t::empty;
                }
            }

            ne->coeff = 1;
            ne->interval = eval_interval::proper(pdd_lo, new_lo, pdd_hi, new_hi);
            ne->bit_width -= k;

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
        for (auto const& d : e->deps)
            out << d << " ";
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
                out << " ...";
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
                out << "v" << v << ": ";
                if (layer.bit_width != c.size(v))
                    out << "width[" << layer.bit_width << "] ";
                display_all(out, layer.entries, " ");
                out << "\n";
            }
        }
        return out;
    }

    std::ostream& viable::display_state(std::ostream& out) const {
        out << "v" << m_var << ": ";
        for (auto const& slice : m_overlaps) {
            out << "v" << slice.v << ":" << c.size(slice.v) << "@" << slice.offset << " ";
            if (c.is_assigned(slice.v))
                out << "value(" << c.get_assignment().value(slice.v) << ") ";
        }
        out << "\n";
        return out;
    }

    std::ostream& viable::display_explain(std::ostream& out) const {
        display_state(out);
        for (auto const& e : m_explain)
            display_one(out << "v" << m_var << "[" << e.e->bit_width << "] : = " << e.value << " ", e.e) << "\n";
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
