/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    goal_num_occurs.h

Abstract:


Author:

    Leonardo de Moura (leonardo) 2012-10-20.

Revision History:

--*/
#pragma once

#include "ast/num_occurs.h"

class goal;

class goal_num_occurs : public num_occurs { 
    expr_ref_vector m_pinned;
public:
    goal_num_occurs(ast_manager& m, bool ignore_ref_count1 = false, bool ignore_quantifiers = false):
        num_occurs(ignore_ref_count1, ignore_quantifiers), 
        m_pinned(m) {
    }

    void reset() override { num_occurs::reset(); m_pinned.reset(); }
    void operator()(goal const & s);
};


