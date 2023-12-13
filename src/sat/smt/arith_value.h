
/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    arith_value.h

Abstract:

    Utility to extract arithmetic values from context.

Author:

    Nikolaj Bjorner (nbjorner) 2018-12-08.

Revision History:

--*/
#pragma once

#include "ast/arith_decl_plugin.h"

namespace euf {
    class solver;
}
namespace arith {

    class solver;

    class arith_value {
        euf::solver& s;
        ast_manager& m;
        arith_util a;
        solver* as = nullptr;
        void init();
    public:
        arith_value(euf::solver& s);
        bool get_value(expr* e, rational& value);

#if 0
        bool get_lo_equiv(expr* e, rational& lo, bool& strict);
        bool get_up_equiv(expr* e, rational& up, bool& strict);
        bool get_lo(expr* e, rational& lo, bool& strict);
        bool get_up(expr* e, rational& up, bool& strict);
        bool get_value_equiv(expr* e, rational& value);
        expr_ref get_lo(expr* e);
        expr_ref get_up(expr* e);
        expr_ref get_fixed(expr* e);
#endif
    };
};
