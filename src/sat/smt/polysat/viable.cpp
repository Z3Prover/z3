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
#include "sat/smt/polysat/ule_constraint.h"

namespace polysat {

    using dd::val_pp;

    viable::viable(core& c) : c(c), cs(c.cs()), m_forbidden_intervals(c) {}

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

    // fixed bits
    // suffixes
    // find one or two values
    // 
    lbool viable::find_viable(pvar v, rational& lo, rational& hi) {
        return l_undef;

        fixed_bits_info fbi;

#if 0
        if (!collect_bit_information(v, true, fbi))
            return l_false;  // conflict already added
#endif

        offset_slices overlaps;
        c.get_bitvector_suffixes(v, overlaps);
        std::sort(overlaps.begin(), overlaps.end(), [&](auto const& x, auto const& y) { return c.size(x.v) > c.size(y.v); });

        uint_set widths_set;
        // max size should always be present, regardless of whether we have intervals there (to make sure all fixed bits are considered)
        widths_set.insert(c.size(v));

        for (auto const& [v, offset] : overlaps) 
            for (layer const& l : m_units[v].get_layers()) 
                widths_set.insert(l.bit_width);
                    
        unsigned_vector widths;
        for (unsigned w : widths_set) 
            widths.push_back(w);       
        LOG("Overlaps with v" << v << ":" << overlaps);
        LOG("widths: " << widths);

        rational const& max_value = c.var2pdd(v).max_value();

        m_explain.reset();
        lbool result_lo = find_on_layers(v, widths, overlaps, fbi, rational::zero(), max_value, lo);
        if (result_lo != l_true)
            return result_lo;

        if (lo == max_value) {
            hi = lo;
            return l_true;
        }
        
        lbool result_hi = find_on_layers(v, widths, overlaps, fbi, lo + 1, max_value, hi);

        if (result_hi != l_false)
            return result_hi;
        hi = lo;
        return l_true;
    }

    // l_true ... found viable value
    // l_false ... no viable value in [to_cover_lo;to_cover_hi[
    // l_undef ... out of resources
    lbool viable::find_on_layers(
        pvar const v,
        unsigned_vector const& widths,
        offset_slices const& overlaps,
        fixed_bits_info const& fbi,
        rational const& to_cover_lo,
        rational const& to_cover_hi,
        rational& val) {
        ptr_vector<entry> refine_todo;        

        // max number of interval refinements before falling back to the univariate solver
        unsigned const refinement_budget = 100;
        unsigned refinements = refinement_budget;
        unsigned explain_size = m_explain.size();

        while (refinements--) {
            m_explain.shrink(explain_size);
            lbool result = find_on_layer(v, widths.size() - 1, widths, overlaps, fbi, to_cover_lo, to_cover_hi, val, refine_todo);

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
                pvar x = overlaps[i].v;
                rational const& mod_value = c.var2pdd(x).two_to_N();
                rational x_val = mod(val, mod_value);
                if (!refine_viable(x, x_val)) {
                    refined = true;
                    break;
                }
            }

            if (!refined)
                return l_true;
        }
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
        offset_slices const& overlaps,
        fixed_bits_info const& fbi,
        rational const& to_cover_lo,
        rational const& to_cover_hi,
        rational& val,
        ptr_vector<entry>& refine_todo) {
        unsigned const w = widths[w_idx];
        rational const& mod_value = rational::power_of_two(w);
        unsigned const first_relevant_for_conflict = m_explain.size();

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
        for (auto const& [x, offset] : overlaps) {
            if (c.size(x) < w)  // note that overlaps are sorted by variable size descending
                break;
            if (entry* e = m_units[x].get_entries(w)) {
                display_all(std::cerr << "units for width " << w << ":\n", 0, e, "\n");
                entry_cursor ec;
                ec.cur = e;  // TODO: e->prev() probably makes it faster when querying 0 (can often save going around the interval list once)
                // ec.first = nullptr;
                // ec.last = nullptr;
                ecs.push_back(ec);
            }
        }

        rational const to_cover_len = r_interval::len(to_cover_lo, to_cover_hi, mod_value);
        val = to_cover_lo;

        rational progress; // = 0
        SASSERT(progress.is_zero());
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

                m_explain.push_back(e);

                if (e->interval.is_full()) {
                    m_explain.reset();
                    m_explain.push_back(e);  // full interval e -> all other intervals are subsumed/irrelevant
                    set_conflict_by_interval(v, w, m_explain, 0);
                    return l_false;
                }

                SASSERT(e->interval.currently_contains(val));
                rational const& new_val = e->interval.hi_val();
                rational const dist = distance(val, new_val, mod_value);
                SASSERT(dist > 0);
                val = new_val;
                progress += dist;
                LOG("val: " << val << " progress: " << progress);

                if (progress >= mod_value) {
                    // covered the whole domain => conflict
                    set_conflict_by_interval(v, w, m_explain, first_relevant_for_conflict);
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
                lbool result = find_on_layer(v, w_idx - 1, widths, overlaps, fbi, lower_cover_lo, lower_cover_hi, a, refine_todo);
                VERIFY(result != l_undef);
                if (result == l_false) {
                    SASSERT(c.inconsistent());
                    return l_false;  // conflict
                }
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
            lbool result = find_on_layer(v, w_idx - 1, widths, overlaps, fbi, lower_cover_lo, lower_cover_hi, a, refine_todo);
            if (result == l_false) {
                SASSERT(c.inconsistent());
                return l_false;  // conflict
            }

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
                set_conflict_by_interval(v, w, m_explain, first_relevant_for_conflict);
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

    void viable::set_conflict_by_interval(pvar v, unsigned w, ptr_vector<entry>& intervals, unsigned first_interval) {
        SASSERT(!intervals.empty());
        SASSERT(first_interval < intervals.size());
    }

    bool viable::set_conflict_by_interval_rec(pvar v, unsigned w, entry** intervals, unsigned num_intervals, bool& create_lemma, uint_set& vars_to_explain) {
        return true;
    }

    // returns true iff no conflict was encountered
    bool viable::collect_bit_information(pvar v, bool add_conflict, fixed_bits_info& out_fbi) {

        pdd p = c.var(v);
        unsigned const v_sz = c.size(v);
        out_fbi.reset(v_sz);
        auto& [fixed, just_src, just_side_cond, just_slice] = out_fbi;

        fixed_bits_vector fbs;        
        c.get_fixed_bits(v, fbs);

        for (auto const& fb : fbs) {
            LOG("slicing fixed bits: v" << v << "[" << fb.hi << ":" << fb.lo << "] = " << fb.value);
            for (unsigned i = fb.lo; i <= fb.hi; ++i) {
                SASSERT(out_fbi.just_src[i].empty());  // since we don't get overlapping ranges from collect_fixed.
                SASSERT(out_fbi.just_side_cond[i].empty());
                SASSERT(out_fbi.just_slicing[i].empty());
                out_fbi.fixed[i] = to_lbool(fb.value.get_bit(i - fb.lo));
                out_fbi.just_slicing[i].push_back(fb);
            }
        }

        entry* e1 = m_equal_lin[v];
        entry* e2 = m_units[v].get_entries(c.size(v));  // TODO: take other widths into account (will be done automatically by tracking fixed bits in the slicing egraph)
        entry* first = e1;
        if (!e1 && !e2)
            return true;

        return true;
    }


    /*
    * Explain why the current variable is not viable or signleton.
    */
    constraint_id_vector viable::explain() { 
        constraint_id_vector result;
        for (auto e : m_explain) {
            auto index = e->constraint_index;
            auto const& [sc, d, value] = c.m_constraint_index[index];
            result.push_back({ index });
            result.append(c.explain_eval(sc));
        }
        // TODO: explaination for fixed bits
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

    void viable::log() {
        for (pvar v = 0; v < m_units.size(); ++v)
            log(v);
    }

    void viable::log(pvar v) {
      // 
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
