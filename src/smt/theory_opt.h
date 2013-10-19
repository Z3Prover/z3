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

#ifndef _THEORY_OPT_H_
#define _THEORY_OPT_H_

namespace smt {
    class theory_opt {
    public:
        virtual bool max(theory_var v) { UNREACHABLE(); return false; };
        virtual theory_var add_objective(app* term) { UNREACHABLE(); return null_theory_var; }
        virtual optional<rational> get_objective_value(theory_var v) { UNREACHABLE(); optional<rational> r; return r;}
    };
}

#endif
