/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_different_symbolic.h

Abstract:

    Create Horn clauses for different symbolic transformation.

Author:

    Nikolaj Bjorner (nbjorner) 2013-06-19

Revision History:

--*/
#pragma once

#include "muz/base/dl_rule_transformer.h"

namespace datalog {

    class mk_different_symbolic : public rule_transformer::plugin {
        ast_manager& m;
        context&     m_ctx;
    public:
        mk_different_symbolic(context & ctx, unsigned priority = 33037);
        ~mk_different_symbolic();        
        rule_set * operator()(rule_set const & source);
    };

};


