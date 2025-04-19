/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    diophantine equations

Abstract:

    Following "A Practical Approach to Satisfiability  Modulo Linear Integer Arithmetic"
    by Alberto Griggio(griggio@fbk.eu)

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)
    
Revision History:
--*/
#pragma once
#include "math/lp/lia_move.h"
#include "math/lp/explanation.h"

namespace lp {
    
    class int_solver;
    class dioph_eq {
        class imp;
        imp*        m_imp;
    public:
        dioph_eq(int_solver& lia);
        ~dioph_eq();
        lia_move check();
        void explain(lp::explanation&);
        bool some_terms_are_ignored() const;
    };
}
