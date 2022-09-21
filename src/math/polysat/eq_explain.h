#if 0
/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/explain.h"

namespace polysat {

    class solver;

    class eq_explain : public explainer {
    private:
        bool try_explain1(pvar v, signed_constraint c, conflict& core);
        bool explain_zero(pvar v, pdd& a, pdd& b, signed_constraint c, conflict& core);
    public:
        eq_explain(solver& s) : explainer(s) {}
        bool try_explain(pvar v, conflict& core) override;
    };

}
#endif
