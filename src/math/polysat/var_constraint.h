/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat var_constraint

Abstract:

    Var constraints restrict viable values.

    The main way var-constraints interact with the solver is to 
    narrow m_viable during initialization. 

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/dd/dd_bdd.h"
#include "math/polysat/constraint.h"


namespace polysat {

    class var_constraint : public constraint {
        pvar        m_var;
        bdd         m_viable;
    public:
        var_constraint(constraint_manager& m, unsigned lvl, csign_t sign, pvar v, bdd const & b, p_dependency_ref const& dep):
            constraint(m, lvl, sign, dep, ckind_t::bit_t), m_var(v), m_viable(b) {}
        ~var_constraint() override {}
        std::ostream& display(std::ostream& out) const override;
        constraint* resolve(solver& s, pvar v) override;
        void narrow(solver& s) override;
        bool is_always_false() override;
        bool is_currently_false(solver& s) override;
        bool is_currently_true(solver& s) override;
    };
}
