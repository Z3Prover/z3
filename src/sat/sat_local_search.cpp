/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_local_search.cpp

Abstract:
   
    Local search module for cardinality clauses.

Author:

    Sixue Liu 2017-2-21

Notes:

--*/

#include "sat_local_search.h"

namespace sat {

    void local_search::init() {

    }

    bool_var local_search::pick_var() {

        return null_bool_var;
    }

    void local_search::flip(bool_var v) {

       
    }

    bool local_search::tie_breaker_sat(int, int) {

        return false;
    }

    bool local_search::tie_breaker_ccd(int, int) {

        return false;
    }

    void local_search::calculate_and_update_ob() {

    }
    
    void local_search::verify_solution() {

    }
    
    void local_search::display(std::ostream& out) {

    }

    local_search::local_search(solver& s) {

    }
    
    local_search::~local_search() {

    }
    
    void local_search::add_soft(literal l, double weight) {

    }
    
    lbool local_search::operator()() {
        return l_undef;
    }
    

}
