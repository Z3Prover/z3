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
#ifndef _TAB_CONTEXT_H_
#define _TAB_CONTEXT_H_

#include "ast.h"
#include "lbool.h"
#include "statistics.h"

namespace datalog {
    class context;

    class tab {
        class imp;
        imp* m_imp;
    public:
        tab(context& ctx);
        ~tab();
        lbool query(expr* query);
        void cancel();
        void cleanup();
        void reset_statistics();
        void collect_statistics(statistics& st) const;
        void display_certificate(std::ostream& out) const;        
        expr_ref get_answer();
    };
};

#endif
