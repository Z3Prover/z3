/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    weighted_maxsat.h

Abstract:

    Weighted MAXSAT module

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

    Takes solver with hard constraints added.
    Returns a maximal satisfying subset of weighted soft_constraints
    that are still consistent with the solver state.

--*/
#ifndef _OPT_WEIGHTED_MAX_SAT_H_
#define _OPT_WEIGHTED_MAX_SAT_H_

#include "opt_solver.h"
#include "maxsmt.h"

namespace opt {
    class wmaxsmt : public maxsmt_solver {
        struct imp;
        imp* m_imp;
    public:
        wmaxsmt(ast_manager& m, opt_solver& s, expr_ref_vector& soft_constraints, vector<rational> const& weights);
        ~wmaxsmt();
        virtual lbool operator()();
        virtual rational get_lower() const;
        virtual rational get_upper() const;
        virtual bool get_assignment(unsigned idx) const;
        virtual void set_cancel(bool f);
        virtual void collect_statistics(statistics& st) const;
        virtual void get_model(model_ref& mdl);
        virtual void updt_params(params_ref& p);
    };
};

#endif
