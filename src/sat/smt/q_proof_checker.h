/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    q_proof_checker.h

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

namespace q {

    class proof_checker : public euf::proof_checker_plugin {
        ast_manager& m;
        symbol       m_inst;
        symbol       m_bind;

        expr_ref_vector binding(app* jst);

        bool is_inst(expr* jst);

        bool is_bind(expr* e);
        
    public:
        proof_checker(ast_manager& m): 
            m(m),
            m_inst("inst"),
            m_bind("bind") {
            }

        ~proof_checker() override {}
        
        expr_ref_vector clause(app* jst) override;

        bool check(app* jst) override { return false; }

        void register_plugins(euf::proof_checker& pc) override {
            pc.register_plugin(symbol("inst"), this);
        }

        void vc(app* jst, expr_ref_vector& clause) override;
        
    };

}
