/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    ddnf.h

Abstract:

    DDNF based engine.

Author:

    Nikolaj Bjorner (nbjorner) 2014-08-21

Revision History:

--*/
#ifndef _DDNF__H_
#define _DDNF__H_

#include "ast.h"
#include "lbool.h"
#include "statistics.h"
#include "dl_engine_base.h"

namespace datalog {
    class context;

    class ddnf : public engine_base {
        class imp;
        imp* m_imp;
    public:
        ddnf(context& ctx);
        ~ddnf();
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
