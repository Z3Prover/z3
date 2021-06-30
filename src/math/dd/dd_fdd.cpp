/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    dd_fdd

Abstract:

    Finite domain abstraction for using BDDs as sets of integers, inspired by BuDDy's fdd module.

Author:

    Nikolaj Bjorner (nbjorner) 2021-04-20
    Jakob Rath 2021-04-20

--*/

#include "math/dd/dd_fdd.h"

namespace dd {

    fdd::fdd(bdd_manager& manager, unsigned_vector&& vars)
        : m_pos2var(std::move(vars))
        , m_var2pos()
        , m(&manager)
        , m_var(manager.mk_var(m_pos2var))
    {
        for (unsigned pos = 0; pos < m_pos2var.size(); ++pos) {
            unsigned const var = m_pos2var[pos];
            while (var >= m_var2pos.size())
                m_var2pos.push_back(UINT_MAX);
            m_var2pos[var] = pos;
        }
    }

    bdd fdd::non_zero() const {
        bdd non_zero = m->mk_false();
        for (unsigned var : m_pos2var) {
            non_zero |= m->mk_var(var);
        }
        return non_zero;
    }

    unsigned fdd::var2pos(unsigned var) const {
        return var < m_var2pos.size() ? m_var2pos[var] : UINT_MAX;
    }

    bool fdd::contains(bdd b, rational const& val) const {
        while (!b.is_const()) {
            unsigned const pos = var2pos(b.var());
            SASSERT(pos != UINT_MAX && "Unexpected BDD variable");
            b = val.get_bit(pos) ? b.hi() : b.lo();
        }
        return b.is_true();
    }

    find_t fdd::find(bdd b, rational& out_val) const {
        return find_hint(b, rational::zero(), out_val);
    }

    find_t fdd::find_hint(bdd b, rational const& hint, rational& out_val) const {
        out_val = 0;
        if (b.is_false())
            return find_t::empty;
        bool is_unique = true;
        bool hint_ok = !hint.is_zero();  // since we choose the 'lo' branch by default, we don't need to check the hint when it is 0.
        unsigned num_vars = 0;
        while (!b.is_true()) {
            ++num_vars;
            unsigned const pos = var2pos(b.var());
            SASSERT(pos != UINT_MAX && "Unexpected BDD variable");

            bool go_hi = false;
            if (b.lo().is_false()) {
                go_hi = true;
                if (hint_ok && !hint.get_bit(pos))
                    hint_ok = false;
            }
            else if (b.hi().is_false()) {
                if (hint_ok && hint.get_bit(pos))
                    hint_ok = false;
            }
            else {
                // This is the only case where we have a choice
                // => follow the hint
                SASSERT(!b.lo().is_false() && !b.hi().is_false());
                is_unique = false;
                if (hint_ok && hint.get_bit(pos))
                    go_hi = true;
            }

            if (go_hi) {
                out_val += rational::power_of_two(pos);
                b = b.hi();
            }
            else
                b = b.lo();
        }
        if (num_vars != num_bits())
            is_unique = false;
        // If a variable corresponding to a 1-bit in hint does not appear in the BDD,
        // out_val is wrong at this point, so we set it explicitly.
        if (hint_ok)
            out_val = hint;
        // TODO: instead of computing out_val incrementally, we could mark the visited 'hi'-positions and only compute out_val from the marks when !hint_ok.
        return is_unique ? find_t::singleton : find_t::multiple;
    }

    std::ostream& operator<<(std::ostream& out, find_t x) {
        switch (x) {
        case find_t::empty:
            return out << "empty";
        case find_t::singleton:
            return out << "singleton";
        case find_t::multiple:
            return out << "multiple";
        }
        UNREACHABLE();
        return out;
    }

  
    bool fdd::sup(bdd const& x, bool_vector& lo) {
        SASSERT(lo.size() == num_bits());
	//
	// Assumption: common case is that high-order bits are before lower-order bits also
	// after re-ordering.
	//

	// this checks that lo is included in x
	bdd b = x;
	while (!b.is_true()) {
	    unsigned const pos = var2pos(b.var());
            SASSERT(pos != UINT_MAX && "Unexpected BDD variable");
	    if (lo[pos] && b.hi().is_false())
		return false;
	    if (!lo[pos] && b.lo().is_false())
		return false;
	    
	    if (lo[pos])
		b = b.hi();
	    else
		b = b.lo();
	}
	return false;
    }
    
    bool fdd::inf(bdd const& b, bool_vector& hi) {
        SASSERT(hi.size() == num_bits());
	return false;
    }


}
