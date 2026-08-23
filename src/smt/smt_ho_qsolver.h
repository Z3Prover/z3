/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    smt_ho_qsolver.h

Abstract:

    Higher-order matching and term-enumeration quantifier solver.

--*/
#pragma once

#include "util/statistics.h"

namespace smt {
    class context;
    class quantifier_manager;

    class ho_qsolver {
        struct imp;
        imp* m_imp;

    public:
        ho_qsolver(context& ctx, quantifier_manager& qm);
        ~ho_qsolver();

        bool final_check();
        void collect_statistics(::statistics& st) const;
    };
}
