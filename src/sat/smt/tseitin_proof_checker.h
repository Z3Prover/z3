/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    tseitin_proof_checker.h

Abstract:

    Plugin for checking quantifier instantiations

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-07


--*/
#pragma once

#include "util/obj_pair_set.h"
#include "ast/ast_trail.h"
#include "ast/ast_util.h"
#include "sat/smt/euf_proof_checker.h"
#include <iostream>

namespace tseitin {

    class proof_checker : public euf::proof_checker_plugin {
        ast_manager& m;

        bool equiv(expr* a, expr* b);
        
    public:
        proof_checker(ast_manager& m): 
            m(m) {
        }

        ~proof_checker() override {}
        
        expr_ref_vector clause(app* jst) override;
        
        bool check(app* jst) override;

        void register_plugins(euf::proof_checker& pc) override {
            pc.register_plugin(symbol("tseitin"), this);
        }
        
    };

}
