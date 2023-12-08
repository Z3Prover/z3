/*++
Copyright (c) 2021 Microsoft Corporation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once

#include "math/dd/dd_pdd.h"
#include "util/sat_literal.h"

namespace polysat {

    using pdd = dd::pdd;
    using pvar = unsigned;

    class dependency {
        unsigned m_index;
        unsigned m_level;
    public:
        dependency(sat::literal lit, unsigned level) : m_index(2 * lit.index()), m_level(level) {}
        dependency(unsigned var_idx, unsigned level) : m_index(1 + 2 * var_idx), m_level(level) {} 
        static dependency null_dependency() { return dependency(0, UINT_MAX); }
        bool is_null() const { return m_level == UINT_MAX; }
        bool is_literal() const { return m_index % 2 == 0; }
        sat::literal literal() const { SASSERT(is_literal());  return sat::to_literal(m_index / 2); }
        unsigned index() const { SASSERT(!is_literal()); return (m_index - 1) / 2; }
        unsigned level() const { return m_level; }
    };

    inline std::ostream& operator<<(std::ostream& out, dependency d) {
        if (d.is_literal())
            return out << d.literal() << "@" << d.level();
        else
            return out << "v" << d.index() << "@" << d.level();
    }

    using dependency_vector = vector<dependency>;

}
