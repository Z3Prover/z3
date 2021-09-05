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
#include "util/map.h"
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

}
