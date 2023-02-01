/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    q_theory_checker.h

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

    class theory_checker : public euf::theory_checker_plugin {
        ast_manager& m;
        symbol       m_inst;
        symbol       m_bind;

        expr_ref_vector binding(app* jst);

        bool is_inst(expr* jst);

        bool is_bind(expr* e);
        
    public:
        theory_checker(ast_manager& m): 
            m(m),
            m_inst("inst"),
            m_bind("bind") {
            }
        
        expr_ref_vector clause(app* jst) override;

        bool check(app* jst) override { return false; }

        void register_plugins(euf::theory_checker& pc) override {
            pc.register_plugin(symbol("inst"), this);
        }

        bool vc(app* jst, expr_ref_vector const& clause, expr_ref_vector& v) override;
        
    };

}
