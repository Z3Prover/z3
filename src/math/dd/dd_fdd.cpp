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
        // , m(&manager)
        , m_var(manager.mk_var(m_pos2var))
    {
        for (unsigned pos = 0; pos < m_pos2var.size(); ++pos) {
            unsigned const var = m_pos2var[pos];
            while (var >= m_var2pos.size())
                m_var2pos.push_back(UINT_MAX);
            m_var2pos[var] = pos;
        }
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
        out_val = 0;
        if (b.is_false())
            return find_t::empty;
        bool is_unique = true;
        unsigned num_vars = 0;
        while (!b.is_true()) {
            ++num_vars;
            unsigned const pos = var2pos(b.var());
            SASSERT(pos != UINT_MAX && "Unexpected BDD variable");
            if (b.lo().is_false()) {
                out_val += rational::power_of_two(pos);
                b = b.hi();
            }
            else {
                if (!b.hi().is_false())
                    is_unique = false;
                b = b.lo();
            }
        }
        if (num_vars != num_bits())
            is_unique = false;
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

}
