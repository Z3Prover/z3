
/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    smt_arith_value.h

Abstract:

    Utility to extract arithmetic values from context.

Author:

    Nikolaj Bjorner (nbjorner) 2018-12-08.

Revision History:

--*/
#pragma once

#include "ast/arith_decl_plugin.h"
#include "smt/smt_context.h"


namespace smt {
    class arith_value {
        context& m_ctx;        
        ast_manager& m;
        arith_util a;
    public:
        arith_value(context& ctx);
        bool get_lo(expr* e, rational& lo, bool& strict);
        bool get_up(expr* e, rational& up, bool& strict);
        bool get_value(expr* e, rational& value);
        final_check_status final_check();
    };
};
