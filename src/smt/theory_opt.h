/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_opt.h

Abstract:

    Interface utilities used by optimization providing 
    theory solvers.

Author:

    Nikolaj Bjorner (nbjorner) 2013-10-18

Notes:

--*/

#include "inf_rational.h"
#include "inf_eps_rational.h"

#ifndef _THEORY_OPT_H_
#define _THEORY_OPT_H_

namespace smt {
    class theory_opt {
    public:
        typedef inf_eps_rational<inf_rational> inf_eps;
        virtual inf_eps_rational<inf_rational> maximize(theory_var v) { UNREACHABLE(); return inf_eps::infinity(); }
        virtual theory_var add_objective(app* term) { UNREACHABLE(); return null_theory_var; }
        virtual expr* block_lower_bound(theory_var v, inf_rational const& val) { return 0; }
    };
}

#endif
