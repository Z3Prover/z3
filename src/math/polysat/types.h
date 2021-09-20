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

}
