/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    theory_array_bapa.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner 2019-04-13

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_array_full;

    class theory_array_bapa {
        class imp;
        imp* m_imp;
    public:
        theory_array_bapa(theory_array_full& th);
        ~theory_array_bapa();
        void internalize_term(app* term);
        final_check_status final_check();
        void init_model();
        bool should_research(expr_ref_vector & unsat_core);
        void add_theory_assumptions(expr_ref_vector & assumptions);
    };

};


