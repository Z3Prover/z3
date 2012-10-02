/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_statistics.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-17.

Revision History:

--*/
#ifndef _SPC_STATISTICS_H_
#define _SPC_STATISTICS_H_

#include<iostream>

namespace spc {

    struct statistics {
        unsigned m_num_mk_clause;
        unsigned m_num_del_clause;
        unsigned m_num_processed;
        unsigned m_num_superposition;
        unsigned m_num_resolution;
        unsigned m_num_eq_factoring;
        unsigned m_num_factoring;
        unsigned m_num_eq_resolution;
        unsigned m_num_trivial;
        unsigned m_num_simplified;
        unsigned m_num_subsumed;
        unsigned m_num_redundant;
        statistics() {
            reset();
        }
        
        void reset();
        void display(std::ostream & out) const;
    };
};

#endif /* _SPC_STATISTICS_H_ */

