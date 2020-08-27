/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_th.cpp

Abstract:

    Theory plugins

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#include "sat/smt/sat_th.h"
#include "util/top_sort.h"

namespace sat {
    
    /*
     * \brief add dependency: dst depends on src.
     */
    void th_dependencies::add(euf::enode* src, euf::enode* dst) {
        
    }
    
    /*
     * \brief sort dependencies.
     */
    void th_dependencies::sort() {
        top_sort<euf::enode> top;
        
    }

}
