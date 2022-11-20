/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat variable elimination

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once

#include "math/polysat/types.h"
#include "math/polysat/constraint.h"

namespace polysat {

    class conflict;

    class free_variable_elimination {
        
        solver& s;
        unsigned_vector m_has_validation_of_range; // TODO: Find a better name
        unsigned_vector m_pv_constants;
        unsigned_vector m_pv_power_constants;
        unsigned_vector m_inverse_constants;
        unsigned_vector m_rest_constants;
        
        pdd get_hamming_distance(pdd p);
        pdd get_odd(pdd p); // add lemma "2^pv(v) * v' = v"
        optional<pdd> get_inverse(pdd v); // add lemma "v' * v'^-1 = 1 (where v' is the odd part of v)"
        void add_dyadic_valuation(pvar v, unsigned k); // add lemma "pv(v) = k" ==> "pv_v = k"
        std::pair<pdd, pdd> get_dyadic_valuation(pdd p, unsigned short lower, unsigned short upper); // lower bound inclusive; upper exclusive
        std::pair<pdd, pdd> get_dyadic_valuation(pdd p);
        void find_lemma(pvar v, conflict& core);
        void find_lemma(pvar v, signed_constraint c, conflict& core);
        pdd eval(pdd const& p, conflict& core, assignment_t& out_assignment);
        bool inv(pdd const& p, pdd& out_p_inv);
    public:
        free_variable_elimination(solver& s): s(s) {}
        void find_lemma(conflict& core);
    };

}
