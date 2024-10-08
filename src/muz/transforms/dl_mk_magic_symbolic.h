/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_magic_symbolic.h

Abstract:

    Create Horn clauses for magic symbolic transformation.

Author:

    Nikolaj Bjorner (nbjorner) 2013-06-19

Revision History:

--*/
#pragma once

#include "muz/base/dl_rule_transformer.h"

namespace datalog {

    class mk_magic_symbolic : public rule_transformer::plugin {
        ast_manager& m;
        context&     m_ctx;
        app_ref      mk_ans(app* q);
        app_ref      mk_query(app* q);
    public:
        mk_magic_symbolic(context & ctx, unsigned priority = 33037);
        rule_set * operator()(rule_set const & source) override;
    };

};


