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
#ifndef _CLP_CONTEXT_H_
#define _CLP_CONTEXT_H_

#include "ast.h"
#include "lbool.h"
#include "statistics.h"

namespace datalog {
    class context;

    class clp {
        class imp;
        imp* m_imp;
    public:
        clp(context& ctx);
        ~clp();
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
