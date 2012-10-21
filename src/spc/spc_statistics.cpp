/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_statistics.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-17.

Revision History:

--*/
#include"spc_statistics.h"

namespace spc {
    
    void statistics::reset() {
        m_num_mk_clause = 0;
        m_num_del_clause = 0;
        m_num_processed = 0;
        m_num_superposition = 0;
        m_num_resolution = 0;
        m_num_eq_factoring = 0;
        m_num_factoring = 0;
        m_num_eq_resolution = 0;
        m_num_trivial = 0;
        m_num_simplified = 0;
        m_num_subsumed = 0;
        m_num_redundant = 0;
    }
    
    void statistics::display(std::ostream & out) const {
        out << "num. mk. clause:    " << m_num_mk_clause << "\n";
        out << "num. del. clause:   " << m_num_del_clause << "\n";
        out << "num. processed:     " << m_num_processed << "\n";
        out << "num. superposition: " << m_num_superposition << "\n";
        out << "num. resolution:    " << m_num_resolution << "\n";
        out << "num. eq. factoring: " << m_num_eq_factoring << "\n";
        out << "num. factoring:     " << m_num_factoring << "\n";
        out << "num. eq. resol.:    " << m_num_eq_resolution << "\n";
        out << "num. simplified:    " << m_num_simplified << "\n";
        out << "num. redundant:     " << m_num_redundant << "\n";
        out << "  num. trivial:     " << m_num_trivial << "\n";
        out << "  num. subsumed:    " << m_num_subsumed << "\n";
    }

};

