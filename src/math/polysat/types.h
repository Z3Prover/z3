/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat types

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/
#pragma once
#include "util/dependency.h"
#include "util/trail.h"
#include "util/lbool.h"
#include "util/rlimit.h"
#include "util/scoped_ptr_vector.h"
#include "util/var_queue.h"
#include "util/ref_vector.h"
#include "math/dd/dd_pdd.h"
#include "math/dd/dd_bdd.h"
#include "math/dd/dd_fdd.h"

namespace polysat {

    class solver;
    typedef dd::pdd pdd;
    typedef dd::bdd bdd;
    typedef dd::bddv bddv;
    typedef unsigned pvar;

    const unsigned null_dependency = UINT_MAX;
    const pvar null_var = UINT_MAX;

    struct dep_value_manager {
        void inc_ref(unsigned) {}
        void dec_ref(unsigned) {}
    };

    struct dep_config {
        typedef dep_value_manager value_manager;
        typedef unsigned value;
        typedef small_object_allocator allocator;
        static const bool ref_count = false;
    };

    typedef dependency_manager<dep_config> poly_dep_manager;
    typedef poly_dep_manager::dependency p_dependency;

    typedef obj_ref<p_dependency, poly_dep_manager> p_dependency_ref; 
    typedef ref_vector<p_dependency, poly_dep_manager> p_dependency_refv;

    typedef unsigned bool_var;
    typedef svector<bool_var> bool_var_vector;

    // 0 ...  x
    // 1 ... ~x
    // 2 ...  y
    // 3 ... ~y
    // :
    // :
    // UINT_MAX-1 ... (invalid)
    // UINT_MAX   ... (invalid; used to represent invalid/missing literals)
    class bool_lit {
        unsigned m_index;

        bool_lit(): m_index(UINT_MAX) {}
        explicit bool_lit(unsigned idx): m_index(idx) { SASSERT(is_valid()); }

    public:
        bool_lit(bool_var var, bool is_positive): bool_lit(2*var + is_positive) {}

        static bool_lit positive(bool_var var) { return bool_lit(var, true); }
        static bool_lit negative(bool_var var) { return bool_lit(var, false); }
        static bool_lit invalid() { return bool_lit(); }

        bool is_valid() const { return m_index < (UINT_MAX & ~0x1); }

        unsigned index() const { SASSERT(is_valid()); return m_index; }
        bool_var var() const { SASSERT(is_valid()); return m_index / 2; }

        bool is_positive() const { return (m_index & 0x1) == 0; }
        bool is_negative() const { return !is_positive(); }

        bool_lit operator~() const { return bool_lit(m_index ^ 0x1); }

        // operator unsigned() const { return index(); }
    };


}
