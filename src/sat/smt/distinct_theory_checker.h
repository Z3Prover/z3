/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    distinct_theory_checker.h

Abstract:

    Plugin for checking distinct internalization

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-07

--*/
#pragma once

#include "util/obj_pair_set.h"
#include "util/obj_hashtable.h"
#include "sat/smt/euf_proof_checker.h"
#include <iostream>

namespace distinct {

    class theory_checker : public euf::theory_checker_plugin {
        ast_manager& m;

        bool gate_holds(app* d, expr* some_eq, bool negated);
    public:
        theory_checker(ast_manager& m):
            m(m) {
        }

        expr_ref_vector clause(app* jst) override;

        bool check(app* jst) override;

        void register_plugins(euf::theory_checker& pc) override {
            pc.register_plugin(symbol("alldiff"), this);
        }

    };

}
