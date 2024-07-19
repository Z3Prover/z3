/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_sls.h

Abstract:

    Base types for SLS.
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-06027
    
--*/
#pragma once

#include "util/sat_literal.h"

namespace sat {

    struct clause_info {
        clause_info(unsigned n, literal const* lits, double init_weight): m_weight(init_weight), m_clause(n, lits) {}
        double   m_weight;           // weight of clause
        unsigned m_trues = 0;        // set of literals that are true
        unsigned m_num_trues = 0;    // size of true set
        literal_vector m_clause;
        literal const* begin() const { return m_clause.begin(); }
        literal const* end() const { return m_clause.end(); }
        bool is_true() const { return m_num_trues > 0; }
        void add(literal lit) { ++m_num_trues; m_trues += lit.index(); }
        void del(literal lit) { SASSERT(m_num_trues > 0); --m_num_trues; m_trues -= lit.index(); }
    };

    inline std::ostream& operator<<(std::ostream& out, clause_info const& ci) {
        return out << ci.m_clause << " w: " << ci.m_weight << " nt: " << ci.m_num_trues;
    }
};


