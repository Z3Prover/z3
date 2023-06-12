/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    polysat definitions

Author:

    Jakob Rath 2023-06-01

--*/

#include "math/polysat/naming.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    void name_manager::push_var(pdd pv) {
        SASSERT(pv.is_var());
        SASSERT_EQ(pv.var(), m_terms.size());
        pvar const v = pv.var();
        m_terms.push_back(std::move(pv));
        SASSERT(!is_name(v));
    }

    void name_manager::pop_var() {
        pvar const v = m_terms.size() - 1;
        if (is_name(v)) {
            name_key key{m_terms[v]};
            m_names.remove(key);
        }
        m_terms.pop_back();
    }

    void name_manager::set_name(pvar v, pdd const& t) {
        SASSERT(!is_name(v));
        name_key key{t};
        SASSERT(!m_names.contains(key));
        m_names.insert(key, v);
        m_terms[v] = t;
    }

    pvar name_manager::get_name(pdd const& t) const {
        name_key key{t};
        auto it = m_names.find_iterator(key);
        if (it == m_names.end())
            return null_var;
        return it->m_value;
    }

    pvar name_manager::mk_name(pdd const& t) {
        if (t.is_var())
            return t.var();
        pvar v = get_name(t);
        if (v != null_var)
            return v;
        v = s.add_var(t.power_of_2());
        s.add_eq(s.var(v), t);
        set_name(v, t);
        return v;
    }

}
