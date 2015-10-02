/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_statistics.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-21.

Revision History:

--*/
#ifndef SMT_STATISTICS_H_
#define SMT_STATISTICS_H_

#include<iostream>

namespace smt {

    struct statistics {
        unsigned m_num_propagations;
        unsigned m_num_bin_propagations;
        unsigned m_num_conflicts;
        unsigned m_num_sat_conflicts;
        unsigned m_num_decisions;
        unsigned m_num_add_eq;
        unsigned m_num_restarts;
        unsigned m_num_final_checks;
        unsigned m_num_mk_bool_var;
        unsigned m_num_del_bool_var;
        unsigned m_num_mk_enode;
        unsigned m_num_del_enode;
        unsigned m_num_mk_clause;
        unsigned m_num_del_clause;
        unsigned m_num_mk_bin_clause;
        unsigned m_num_mk_lits;
        unsigned m_num_dyn_ack;
        unsigned m_num_del_dyn_ack;
        unsigned m_num_interface_eqs;
        unsigned m_max_generation;
        unsigned m_num_minimized_lits;
        unsigned m_num_checks;
        statistics() {
            reset();
        }
        
        void reset();
    };
};



#endif /* SMT_STATISTICS_H_ */

