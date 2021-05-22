/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_types.h

Abstract:

    Basic types for the SMT engine

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#pragma once

#include "util/list.h"
#include "util/vector.h"
#include "util/hashtable.h"
#include "util/lbool.h"
#include "util/sat_literal.h"

class model;

namespace smt {
    /**
       \brief A boolean variable is just an integer.
    */
    typedef sat::bool_var bool_var;
    
    const bool_var null_bool_var  = sat::null_bool_var;
    const bool_var true_bool_var  = 0;
    const bool_var first_bool_var = 1;
    
    typedef svector<bool_var> bool_var_vector;

    typedef family_id theory_id;
    const theory_id null_theory_id = null_family_id;
    typedef int theory_var;
    const theory_var null_theory_var = -1;

    class enode;
    typedef ptr_vector<enode> enode_vector;
    typedef std::pair<enode *, enode *> enode_pair;
    typedef svector<enode_pair> enode_pair_vector;

    class theory;

    class justification;

    class model_generator;

    enum final_check_status {
        FC_DONE,
        FC_CONTINUE,
        FC_GIVEUP
    };

    inline std::ostream & operator<<(std::ostream & out, final_check_status st) {
        switch (st) {
        case FC_DONE:     out << "done"; break;
        case FC_CONTINUE: out << "continue"; break;
        case FC_GIVEUP:   out << "giveup"; break;
        }
        return out;
    }

// if defined, then clauses have an extra mask field used to optimize backward subsumption, and backward/forward subsumption resolution.
#define APPROX_LIT_SET

};


