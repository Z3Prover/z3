/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    clp_context.h

Abstract:

    Bounded CLP (symbolic simulation using Z3) context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-04-26

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "util/lbool.h"
#include "util/statistics.h"
#include "muz/base/dl_engine_base.h"

namespace datalog {
    class context;

    class clp : public datalog::engine_base {
        class imp;
        imp* m_imp;
    public:
        clp(context& ctx);
        ~clp() override;
        lbool query(expr* query) override;
        void reset_statistics() override;
        void collect_statistics(statistics& st) const override;
        void display_certificate(std::ostream& out) const override;
        expr_ref get_answer() override;
    };
};

