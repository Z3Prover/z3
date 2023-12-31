/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    polysat_proof_checker.h

Abstract:

    Plugin for checking polysat bit-vector lemmas

Author:

    Nikolaj Bjorner (nbjorner) 2022-08-28


--*/
#pragma once

#include "ast/ast_util.h"
#include "sat/smt/euf_proof_checker.h"
#include <iostream>


namespace polysat {

    class theory_checker : public euf::theory_checker_plugin {
        ast_manager& m;
        
    public:
        theory_checker(ast_manager& m): 
            m(m) {}        

        expr_ref_vector clause(app* jst) override {
            expr_ref_vector result(m);
            for (expr* arg : *jst) 
                if (m.is_bool(arg))
                    result.push_back(mk_not(m, arg));
            return result;
        }

        bool check(app* jst) override {
            params_ref params;
            params.set_uint("smt.bv.solver",2); // use int-blast solver to check lemmas
            scoped_ptr<solver> s = mk_smt_solver(m, params, symbol());
            auto cl = clause(jst);
            for (auto arg : cl)
                s->assert_expr(mk_not(m, arg));
            lbool r = s->check_sat();
            if (r == l_true) {
                model_ref mdl;
                s->get_model(mdl);
                IF_VERBOSE(0, verbose_stream() << "checking failed for\n" << mk_pp(jst, m) << "\n" << * mdl << "\n");
            }                
            return r == l_false;
        }

        void register_plugins(euf::theory_checker& pc) override {
            pc.register_plugin(symbol("polysat"), this);
        }
        
    };

}
