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
        virtual bool max_min(theory_var v, bool max) { UNREACHABLE(); return false; };
        virtual theory_var add_objective(app* term) { UNREACHABLE(); return null_theory_var; }
    };
}

#endif
