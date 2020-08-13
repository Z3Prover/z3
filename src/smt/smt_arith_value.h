
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
#include "smt/theory_lra.h"
#include "smt/theory_arith.h"
#include "smt/theory_bv.h"

namespace smt {
    class arith_value {
        context* m_ctx;        
        ast_manager& m;
        arith_util a;
        bv_util    b;
        theory_mi_arith* m_tha;
        theory_i_arith*  m_thi;
        theory_lra*      m_thr;
        theory_bv*       m_thb;
    public:
        arith_value(ast_manager& m);
        void init(context* ctx);
        bool get_lo_equiv(expr* e, rational& lo, bool& strict);
        bool get_up_equiv(expr* e, rational& up, bool& strict);
        bool get_value_equiv(expr* e, rational& value) const;
        bool get_lo(expr* e, rational& lo, bool& strict) const;
        bool get_up(expr* e, rational& up, bool& strict) const;
        bool get_value(expr* e, rational& value) const;
        expr_ref get_lo(expr* e) const;
        expr_ref get_up(expr* e) const;
        expr_ref get_fixed(expr* e) const;
        final_check_status final_check();
    };
};
