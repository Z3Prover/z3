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
#ifndef CLP_CONTEXT_H_
#define CLP_CONTEXT_H_

#include "ast.h"
#include "lbool.h"
#include "statistics.h"
#include "dl_engine_base.h"

namespace datalog {
    class context;

    class clp : public datalog::engine_base {
        class imp;
        imp* m_imp;
    public:
        clp(context& ctx);
        ~clp();
        virtual lbool query(expr* query);
        virtual void reset_statistics();
        virtual void collect_statistics(statistics& st) const;
        virtual void display_certificate(std::ostream& out) const;        
        virtual expr_ref get_answer();
    };
};

#endif
