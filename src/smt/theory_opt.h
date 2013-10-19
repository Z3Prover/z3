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

#include "inf_eps_rational.h"

#ifndef _THEORY_OPT_H_
#define _THEORY_OPT_H_

namespace smt {
    class theory_opt {
    public:
        virtual bool maximize(theory_var v) { UNREACHABLE(); return false; };
        virtual theory_var add_objective(app* term) { UNREACHABLE(); return null_theory_var; }
		virtual inf_eps_rational<rational> get_objective_value(theory_var v) { 
            UNREACHABLE(); 
            inf_eps_rational<rational> r(rational(1), rational(0)); 
            return r; 
		}
    };
}

#endif
