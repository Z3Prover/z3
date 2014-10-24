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
#include "dl_engine_base.h"

namespace datalog {
    class context;

    class tab : public engine_base {
        class imp;
        imp* m_imp;
    public:
        tab(context& ctx);
        ~tab();
        virtual lbool query(expr* query);
        virtual void cancel();
        virtual void cleanup();
        virtual void reset_statistics();
        virtual void collect_statistics(statistics& st) const;
        virtual void display_certificate(std::ostream& out) const;        
        virtual expr_ref get_answer();
    };
};

#endif
