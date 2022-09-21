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
#include "math/polysat/conflict.h"
#include "math/polysat/constraint.h"
#include "math/polysat/clause_builder.h"
#include "math/polysat/interval.h"

namespace polysat {

    class solver;

    class explainer {
        friend class conflict;
    protected:
        solver& s;
    public:
        explainer(solver& s) :s(s) {}
        virtual ~explainer() {}
        virtual bool try_explain(pvar v, conflict& core) = 0;
    };

    class ex_polynomial_superposition : public explainer {
    private:
        signed_constraint resolve1(pvar v, signed_constraint c1, signed_constraint c2);
        lbool find_replacement(signed_constraint c2, pvar v, conflict& core);
        void reduce_by(pvar v, conflict& core);
        bool reduce_by(pvar, signed_constraint c, conflict& core);
        lbool try_explain1(pvar v, conflict& core);
    public:
        ex_polynomial_superposition(solver& s) : explainer(s) {}
        bool try_explain(pvar v, conflict& core) override;
    };

}
#endif
