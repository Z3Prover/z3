/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/conflict_core.h"
#include "math/polysat/constraint.h"
#include "math/polysat/clause_builder.h"
#include "math/polysat/interval.h"

namespace polysat {

    class solver;
    class constraint_manager;

    class explainer {
        friend class conflict_core;
        solver* m_solver = nullptr;
        void set_solver(solver& s) { m_solver = &s; }
    protected:
        solver& s() { return *m_solver; }
        constraint_manager& cm();
    public:
        virtual ~explainer() {}
        virtual bool try_explain(pvar v, /* vector<signed_constraint> const& cjust_v, */ conflict_core& core) = 0;
    };

    class ex_polynomial_superposition : public explainer {
    private:
        bool is_positive_equality_over(pvar v, signed_constraint const& c);
        signed_constraint resolve1(pvar v, signed_constraint c1, signed_constraint c2);
        lbool try_explain1(pvar v, conflict_core& core);
    public:
        bool try_explain(pvar v, conflict_core& core) override;
    };







#if 0
    class conflict_explainer {
        solver& m_solver;

        // conflict_core m_conflict;
        vector<constraint> m_new_assertions;  // to be inserted into Gamma (conclusions from saturation)

        scoped_ptr_vector<inference_engine> inference_engines;

        bool push_omega_mul(clause_builder& clause, unsigned level, unsigned p, pdd const& x, pdd const& y);

        // Gamma
        // search_state& search() { return m_solver.m_search; }
        // Core
        // conflict_core& conflict() { return m_solver.m_conflict; }
    public:
        /** Create empty conflict */
        conflict_explainer(solver& s);

        /** Perform one step of core saturation, if possible.
         *  Core saturation derives new constraints according applicable inference rules.
         */
        bool saturate();

        /** resolve conflict state against assignment to v */
        void resolve(pvar v, ptr_vector<constraint> const& cjust_v);
        void resolve(sat::literal lit);

        // TODO: move conflict resolution from solver into this class.
        //       we have a single public method as entry point to conflict resolution.
        //       what do we need to return?

        /** conflict resolution until first (relevant) decision */
        void resolve();
    };
#endif
}
