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

        expr_fast_mark1 m_mark;
        bool equiv(expr* a, expr* b);
        
        void mark(expr* a) { m_mark.mark(a); }
        bool is_marked(expr* a) { return m_mark.is_marked(a); }
        struct scoped_mark {
            proof_checker& pc;
            scoped_mark(proof_checker& pc): pc(pc) {}
            ~scoped_mark() { pc.m_mark.reset(); }
        };
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
