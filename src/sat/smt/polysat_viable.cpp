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

    viable::entry* viable::alloc_entry(pvar var) {
        if (m_alloc.empty())
            return alloc(entry);
        auto* e = m_alloc.back();
        e->reset();
        e->var = var;
        m_alloc.pop_back();
        return e;
    }

    find_t viable::find_viable(pvar v, rational& out_val) { throw default_exception("nyi"); }

    /*
    * Explain why the current variable is not viable or signleton.
    */
    dependency_vector viable::explain() { throw default_exception("nyi"); }

    /*
    * Register constraint at index 'idx' as unitary in v.
    */
    void viable::add_unitary(pvar v, unsigned idx) {
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
                return intersect(v, ne);
            }

            // TODO: later, can reduce according to shared_parity
            // unsigned const shared_parity = std::min(coeff_parity, std::min(lo_parity, hi_parity));

            insert(ne, v, m_equal_lin, entry_kind::equal_e);
            return;
        }

    }

    void viable::intersect(pvar v, entry* e) {

        throw default_exception("nyi");
    }

    void viable::log() {
        for (pvar v = 0; v < m_units.size(); ++v)
            log(v);
    }

    void viable::log(pvar v) {
        throw default_exception("nyi");
    }

    void viable::insert(entry* e, pvar v, ptr_vector<entry>& entries, entry_kind k) {
        throw default_exception("nyi");
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

}
