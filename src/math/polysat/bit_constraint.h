/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat bit_constraint

Abstract:

    Bit constraints fix a subrange of bits
    
    The first version assumes the requirement is to fix bit positions 
    to specific values. This is insufficient to encode that x != 0.
    A more general approach is required since bit constraints should
    be able to also let us reduce inequality reasoning to having slack
    variables.

    The main way bit-constraints interact with the solver is to 
    narrow m_viable during initialization. 

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/constraint.h"


namespace polysat {

    class bit_constraint : public constraint {
        pvar        m_var;
        unsigned    m_index;
        bool        m_value;
    public:
        bit_constraint(unsigned lvl, pvar v, unsigned i, bool val, p_dependency_ref& dep):
            constraint(lvl, dep, ckind_t::bit_t), m_var(v), m_index(i), m_value(val) {
        }
        ~bit_constraint() override {}
        std::ostream& display(std::ostream& out) const override;
        bool propagate(solver& s, pvar v) override;
        constraint* resolve(solver& s, pvar v) override;
        void narrow(solver& s) override;
        bool is_always_false() override;
        bool is_currently_false(solver& s) override;
    };
}
