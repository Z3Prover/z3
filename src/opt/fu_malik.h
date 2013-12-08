/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    fu_malik.h

Abstract:

    Fu&Malik built-in optimization method.
    Adapted from sample code in C.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-15

Notes:

    Takes solver with hard constraints added.
    Returns a maximal satisfying subset of soft_constraints
    that are still consistent with the solver state.

--*/
#ifndef _OPT_FU_MALIK_H_
#define _OPT_FU_MALIK_H_

#include "solver.h"
#include "maxsmt.h"

namespace opt {

    class fu_malik : public maxsmt_solver {
        struct imp;
        imp* m_imp;
    public:
        fu_malik(ast_manager& m, solver& s, expr_ref_vector& soft_constraints);
        virtual ~fu_malik();
        virtual lbool operator()();
        virtual rational get_lower() const;
        virtual rational get_upper() const;
        virtual rational get_value() const;
        virtual expr_ref_vector get_assignment() const;
        virtual void set_cancel(bool f);
        virtual void collect_statistics(statistics& st) const;
    };
    
};

#endif
