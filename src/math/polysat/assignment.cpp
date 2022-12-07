/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat substitution and assignment

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/

#include "math/polysat/assignment.h"
#include "math/polysat/solver.h"

namespace polysat {

    substitution::substitution(pdd p)
        : m_subst(std::move(p)) { }

    substitution::substitution(dd::pdd_manager& m)
        : m_subst(m.one()) { }

    substitution substitution::add(pvar var, rational const& value) const {
        return {m_subst.subst_add(var, value)};
    }

    pdd substitution::apply_to(pdd const& p) const {
        return p.subst_val(m_subst);
    }

    bool substitution::contains(pvar var) const {
        rational out_value;
        return value(var, out_value);
    }

    bool substitution::value(pvar var, rational& out_value) const {
        return m_subst.subst_get(var, out_value);
    }

    assignment::assignment(solver& s)
        : m_solver(&s) { }

    assignment assignment::clone() const {
        assignment a(s());
        a.m_pairs = m_pairs;
        a.m_subst.reserve(m_subst.size());
        for (unsigned i = m_subst.size(); i-- > 0; )
            if (m_subst[i])
                a.m_subst.set(i, alloc(substitution, *m_subst[i]));
        a.m_subst_trail = m_subst_trail;
        return a;
    }

    bool assignment::contains(pvar var) const {
        return subst(s().size(var)).contains(var);
    }

    bool assignment::value(pvar var, rational& out_value) const {
        return subst(s().size(var)).value(var, out_value);
    }

    substitution& assignment::subst(unsigned sz) {
        return const_cast<substitution&>(std::as_const(*this).subst(sz));
    }

    substitution const& assignment::subst(unsigned sz) const {
        m_subst.reserve(sz + 1);
        if (!m_subst[sz])
            m_subst.set(sz, alloc(substitution, s().sz2pdd(sz)));
        return *m_subst[sz];
    }

    void assignment::push(pvar var, rational const& value) {
        SASSERT(all_of(m_pairs, [var](assignment_item_t const& item) { return item.first != var; }));
        m_pairs.push_back({var, value});
        unsigned const sz = s().size(var);
        substitution& sub = subst(sz);
        m_subst_trail.push_back(sub);
        sub = sub.add(var, value);
        SASSERT_EQ(sub, *m_subst[sz]);
    }

    void assignment::pop() {
        substitution& sub = m_subst_trail.back();
        unsigned sz = sub.bit_width();
        SASSERT_EQ(sz, s().size(m_pairs.back().first));
        *m_subst[sz] = sub;
        m_subst_trail.pop_back();
        m_pairs.pop_back();
    }

    pdd assignment::apply_to(pdd const& p) const {
        unsigned const sz = p.power_of_2();
        return subst(sz).apply_to(p);
    }

    std::ostream& substitution::display(std::ostream& out) const {
        char const* delim = "";
        pdd p = m_subst;
        while (!p.is_val()) {
            SASSERT(p.lo().is_val());
            out << delim << "v" << p.var() << " := " << p.lo();
            delim = " ";
            p = p.hi();
        }
        return out;
    }

    std::ostream& assignment::display(std::ostream& out) const {
        char const* delim = "";
        for (auto const& [var, value] : m_pairs) {
            out << delim << assignment_pp(s(), var, value);
            delim = " ";
        }
        return out;
    }
}
