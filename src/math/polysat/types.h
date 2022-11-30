/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat types

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/
#pragma once
#include "util/trail.h"
#include "util/lbool.h"
#include "util/map.h"
#include "util/rlimit.h"
#include "util/scoped_ptr_vector.h"
#include "util/var_queue.h"
#include "util/ref_vector.h"
#include "util/sat_literal.h"
#include "math/dd/dd_pdd.h"
#include "math/dd/dd_bdd.h"
#include "math/dd/dd_fdd.h"

namespace polysat {

    class solver;
    class clause;

    using clause_ref = ref<clause>;
    using clause_ref_vector = sref_vector<clause>;

    typedef dd::pdd pdd;
    typedef dd::bdd bdd;
    typedef dd::bddv bddv;

    typedef unsigned pvar;
    inline const pvar null_var = UINT_MAX;

    class dependency {
        unsigned m_val;
    public:
        explicit dependency(unsigned val): m_val(val) {}
        unsigned val() const { return m_val; }
        bool is_null() const { return m_val == UINT_MAX; }
        unsigned hash() const { return val(); }
    };

    inline const dependency null_dependency = dependency(UINT_MAX);
    typedef svector<dependency> dependency_vector;

    inline bool operator<(dependency const& d1, dependency const& d2) { return d1.val() < d2.val();  }
    inline bool operator==(dependency const& d1, dependency const& d2) { return d1.val() == d2.val(); }
    inline bool operator!=(dependency const& d1, dependency const& d2) { return d1.val() != d2.val(); }

    inline std::ostream& operator<<(std::ostream& out, dependency const& d) {
        out << "dep(" << d.val() << ")";
        return out;
    }

}
