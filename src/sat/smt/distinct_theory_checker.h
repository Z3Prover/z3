/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    distinct_proof_checker.h

Abstract:

    Plugin for checking distinct internalization

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-07

Note:
 
  First version just trusts that distinct is internalized correctly.


--*/
#pragma once

#include "sat/smt/euf_proof_checker.h"
#include <iostream>

namespace distinct {

    class theory_checker : public euf::theory_checker_plugin {
        ast_manager& m;
    public:
        theory_checker(ast_manager& m): 
            m(m) {
        }

        expr_ref_vector clause(app* jst) override { 
            expr_ref_vector result(m); 
            result.append(jst->get_num_args(), jst->get_args()); 
            return result; 
        }
        
        bool check(app* jst) override { return true; }

        void register_plugins(euf::theory_checker& pc) override {
            pc.register_plugin(symbol("alldiff"), this);
        }
        
    };

}
