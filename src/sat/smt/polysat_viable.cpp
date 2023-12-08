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
#include "sat/smt/polysat_viable.h"
#include "sat/smt/polysat_core.h"

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
        pvar v;
        entry_kind k;
    public:
        pop_viable_trail(viable& s, entry* e, pvar v, entry_kind k)
            : m_s(s), e(e), v(v), k(k) {}
        void undo() override {
            m_s.pop_viable(e, v, k);
        }
    };

    struct viable::push_viable_trail : public trail {
        viable& m_s;
        entry* e;
        pvar v;
        entry_kind k;
    public:
        push_viable_trail(viable& s, entry* e, pvar v, entry_kind k)
            : m_s(s), e(e), v(v), k(k) {}
        void undo() override {
            m_s.push_viable(e, v, k);
        }
    };

    viable::entry* viable::alloc_entry(pvar var) {
        if (m_alloc.empty())
            return alloc(entry);
        auto* e = m_alloc.back();
        e->reset();
        e->var = var;
        m_alloc.pop_back();
        return e;
    }

    find_t viable::find_viable(pvar v, rational& out_val) { 
        ensure_var(v);
        throw default_exception("nyi"); 
    }

    /*
    * Explain why the current variable is not viable or signleton.
    */
    dependency_vector viable::explain() { throw default_exception("nyi"); }

    /*
    * Register constraint at index 'idx' as unitary in v.
    */
    void viable::add_unitary(pvar v, unsigned idx) {

        ensure_var(v);

        if (c.is_assigned(v))
            return;
        auto [sc, d] = c.m_constraint_trail[idx];

        entry* ne = alloc_entry(v);
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
            c.trail().push(pop_viable_trail(*this, ne, v, entry_kind::unit_e));
            ne->init(ne);
            return ne;
            };

        auto remove_entry = [&](entry* e) {
            c.trail().push(push_viable_trail(*this, e, v, entry_kind::unit_e));
            e->remove_from(entries, e);
            e->active = false;
            };

        if (ne->interval.is_full()) {
            // for (auto const& l : m_units[v].get_layers())
            //     while (l.entries)
            //         remove_entry(l.entries);
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
            } while (e != first);
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
        throw default_exception("nyi");
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

    void viable::pop_viable(entry* e, pvar v, entry_kind k) {
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

    void viable::push_viable(entry* e, pvar v, entry_kind k) {
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
    }

    void viable::insert(entry* e, pvar v, ptr_vector<entry>& entries, entry_kind k) {
        SASSERT(well_formed(m_units[v]));

        c.trail().push(pop_viable_trail(*this, e, v, k));

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
