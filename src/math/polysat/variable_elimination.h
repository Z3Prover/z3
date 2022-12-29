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
#include "math/polysat/clause_builder.h"

namespace polysat {

    class conflict;

    class free_variable_elimination {

        enum get_multiple_result {
          is_multiple, can_multiple, cannot_multiple
        };

        solver& s;
        unsigned_vector m_has_validation_of_range; // TODO: Find a better name
        unsigned_vector m_pv_constants;
        unsigned_vector m_pv_power_constants;
        unsigned_vector m_inverse_constants;
        unsigned_vector m_rest_constants;
        
        unsigned_vector m_occ;
        unsigned_vector m_occ_cnt;
        
        pdd get_hamming_distance(pdd p);
        pdd get_odd(pdd p); // add lemma "2^pv(v) * v' = v"
        optional<pdd> get_inverse(pdd v); // add lemma "v' * v'^-1 = 1 (where v' is the odd part of v)"
        void add_dyadic_valuation(pvar v, unsigned k); // add lemma "pv(v) = k" ==> "pv_v = k"
        std::pair<pdd, pdd> get_dyadic_valuation(pdd p, unsigned short lower, unsigned short upper); // lower bound inclusive; upper exclusive
        std::pair<pdd, pdd> get_dyadic_valuation(pdd p);
        void find_lemma(pvar v, conflict& core);
        void find_lemma(pvar v, signed_constraint c, conflict& core);
        pdd eval(pdd const& p, conflict& core, substitution& out_sub);
        bool inv(pdd const& p, pdd& out_p_inv);
        get_multiple_result get_multiple(const pdd& p1, const pdd& p2, pdd &out);
    public:
        free_variable_elimination(solver& s): s(s) {}
        void find_lemma(conflict& core);
    };
    
    class saturation;
    
    class parity_tracker {
        
        solver& s;
        clause_builder m_builder;
        
        vector<optional<std::pair<pvar, bool_vector>>> m_odd;
        unsigned_vector m_inverse;
        
        struct optional_pdd_hash {
            unsigned operator()(optional<pdd> const& args) const {
                return args->hash();
            }
        };
        using pdd_to_id = map<optional<pdd>, unsigned, optional_pdd_hash, default_eq<optional<pdd>>>;
        
        pdd_to_id m_pdd_to_id; // if we want to use arbitrary pdds instead of pvars
        
        unsigned get_id(const pdd& p);
        
    public:
        
        parity_tracker(solver& s) : s(s), m_builder(s) {}
        
        pdd get_inverse(const pdd& p);
        pdd get_odd(const pdd& p, unsigned parity, svector<signed_constraint>& pat);
        
        std::tuple<pdd, bool, svector<signed_constraint>> eliminate_variable(saturation& saturation, pvar x, const pdd& a, const pdd& b, const pdd& p);
    };
}
