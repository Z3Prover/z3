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
        init_overlaps(v);
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

    void viable::init_overlaps(pvar v) {
        m_overlaps.reset();
        c.get_bitvector_suffixes(v, m_overlaps);
        std::sort(m_overlaps.begin(), m_overlaps.end(), [&](auto const& x, auto const& y) { return c.size(x.child) < c.size(y.child); });
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
                if (e->interval.is_proper())
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
        explanation const& last = m_explain.back();

        verbose_stream() << "\n\n\n\n\nviable::explain: " << m_explain_kind << " v" << m_var << "\n";
        display_explain(verbose_stream()) << "\n";

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
                    explain_hole(before, after, hole_bits, result);
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
        if (m_explain_kind == explain_t::propagation) {
            // assume first and last have same bit-width
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
                verbose_stream() << "m_overlaps " << m_overlaps << "\n";
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
                deps.push_back(c.propagate(sc, c.explain_weak_eval(sc), "explain_overlap value bounds"));
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
            deps.push_back(c.propagate(sc, c.explain_weak_eval(sc), "explain_overlap linking constraint"));
        if (c.inconsistent()) {
            verbose_stream() << "inconsistent ult " << sc << " " << "\n";
            verbose_stream() << "before bw " << ebw << " " << bw << " " << *e.e << "\nafter  bw " << abw << " " << aw << " " << *after.e << "\n";
            display(verbose_stream());
            // UNREACHABLE();
        }
    }

    void viable::explain_hole(explanation const& before, explanation const& after, unsigned hole_bits, dependency_vector& deps)
    {
        //  before      hole       after
        // [----------[     [----------[    bit-width k
        //           [-------[              bit-width hole_bits < k
        //
        // The hole can only be covered by lower intervals if
        //
        //          hole_size < 2^hole_bits
        //
        // i.e., after->lo() - before->hi() < 2^hole_bits.

        unsigned const bw = c.size(before.e->var);
        unsigned const bew = before.e->bit_width;
        unsigned const aw = c.size(after.e->var);
        unsigned const aew = after.e->bit_width;

        verbose_stream() << "explain_hole: " << hole_bits << " bits\n";
        display_explain(verbose_stream() << "    before: " << bew << " " << bw << "   ", before) << "\n";
        display_explain(verbose_stream() << "    after:  " << aew << " " << aw << "   ", after)  << "\n";

        // hole is from t1 to t2
        pdd t1 = before.e->interval.hi();
        pdd t2 = after.e->interval.lo();

        rational after_len = r_interval::len(after.e->interval.lo_val(), after.e->interval.hi_val(), rational::power_of_two(aew));
        rational after_covered_lo = mod2k(after.value - after_len, m_num_bits);
        auto after_covered_ivl = r_interval::proper(after_covered_lo, after.value);
        // verbose_stream() << "   after_len " << after_len << "\n";
        // verbose_stream() << "   after_covered_lo " << after_covered_lo << "\n";
        // verbose_stream() << "   after_covered_ivl " << after_covered_ivl << "\n";
        SASSERT_EQ(after_covered_ivl.len(rational::power_of_two(m_num_bits)), after_len);
        if (after_covered_ivl.contains(before.value)) {
            verbose_stream() << "    not a real hole (subsumption opportunity)\n";
            return;
        }

        // no constraint needed for constant bounds
        if (t1.is_val() && t2.is_val())
            return;

        if (aw != bw) {
            // TODO: eval bounds?
            return;
            NOT_IMPLEMENTED_YET();
        }

        if (bew != bw || aew != aw) {
            // TODO: multiply with 2^k appropriately
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
            //
            // new_hi = hi[w-1:k]      if hi[k-1:0] = 0
            //          hi[w-1:k] + 1  otherwise
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
                bool is_empty_ivl;
                if (lo < hi) {
                    ne->side_cond.push_back(cs.ult(pdd_lo, pdd_hi));
                    if (lo == 0) {
                        ne->side_cond.push_back(cs.eq(pdd_lo));
                        is_empty_ivl = false;
                    }
                    else {
                        ne->side_cond.push_back(~cs.eq(pdd_lo));
                        is_empty_ivl = true;
                    }
                }
                else {
                    SASSERT(hi < lo);
                    ne->side_cond.push_back(cs.ult(pdd_hi, pdd_lo));
                    if (hi == 0) {
                        ne->side_cond.push_back(cs.eq(pdd_hi));
                        is_empty_ivl = true;
                    }
                    else {
                        ne->side_cond.push_back(~cs.eq(pdd_hi));
                        is_empty_ivl = false;
                    }
                }
                if (is_empty_ivl) {
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
        for (auto const& slice : m_overlaps) {
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
