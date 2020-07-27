/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    tab_context.h

Abstract:

    Tabulation/subsumption/cyclic proof context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-01-15

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "util/lbool.h"
#include "util/statistics.h"
#include "muz/base/dl_engine_base.h"

namespace datalog {
    class context;

    class tab : public engine_base {
        class imp;
        imp* m_imp;
    public:
        tab(context& ctx);
        ~tab() override;
        lbool query(expr* query) override;
        void cleanup() override;
        void reset_statistics() override;
        void collect_statistics(statistics& st) const override;
        void display_certificate(std::ostream& out) const override;
        expr_ref get_answer() override;
    };
};

