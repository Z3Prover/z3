/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bv_theory_checker.h

Abstract:

    Plugin for bitvector lemmas

Author:

    Nikolaj Bjorner (nbjorner) 2022-08-28

Notes:


--*/
#pragma once

#include "util/obj_pair_set.h"
#include "ast/ast_trail.h"
#include "ast/ast_util.h"
#include "ast/bv_decl_plugin.h"
#include "sat/smt/euf_proof_checker.h"
#include <iostream>


namespace bv {

    class theory_checker : public euf::theory_checker_plugin {
        ast_manager& m;
        bv_util      bv;

        symbol m_eq2bit = symbol("eq2bit");
        symbol m_ne2bit = symbol("ne2bit");
        symbol m_bit2eq = symbol("bit2eq");
        symbol m_bit2ne = symbol("bit2ne");
        symbol m_bv2int = symbol("bv2int");
        symbol m_bv     = symbol("bv");

        bool check_bv(app* jst);
        bool check_bit2eq(app* jst);
        bool check_bit2ne(app* jst);
        bool check_eq2bit(app* jst);
        bool check_ne2bit(app* jst);
        bool check_bv2int(app* jst);

    public:
        theory_checker(ast_manager& m): 
            m(m),
            bv(m) {}

        bool check(app* jst) override {
            if (jst->get_name() == m_bv)
                return check_bv(jst);
            if (jst->get_name() == m_eq2bit)
                return check_eq2bit(jst);
            if (jst->get_name() == m_ne2bit)
                return check_ne2bit(jst);
            if (jst->get_name() == m_bit2eq)
                return check_bit2eq(jst);
            if (jst->get_name() == m_bit2ne)
                return check_bit2ne(jst);
            if (jst->get_name() == m_bv2int)
                return check_bv2int(jst);            
            return false;
        }

        expr_ref_vector clause(app* jst) override {
            expr_ref_vector result(m);
            if (jst->get_name() == m_bv) {
                for (expr* arg : *jst) 
                    result.push_back(mk_not(m, arg));
            }
            else {
                for (expr* arg : *jst) 
                    result.push_back(arg);
            }
            return result;
        }

        void register_plugins(euf::theory_checker& pc) override {
            pc.register_plugin(m_bv, this);
            pc.register_plugin(m_bit2eq, this);
            pc.register_plugin(m_bit2ne, this);
            pc.register_plugin(m_eq2bit, this);
            pc.register_plugin(m_ne2bit, this);
            pc.register_plugin(m_bv2int, this);
        }
        
    };

}
