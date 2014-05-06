/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    pb_sls.h

Abstract:
   
    SLS for PB optimization.

Author:

    Nikolaj Bjorner (nbjorner) 2014-03-18

Notes:

--*/
#ifndef _PB_SLS_H_
#define _PB_SLS_H_

#include "pb_decl_plugin.h"
#include "model.h"
#include "lbool.h"
#include "params.h"
#include "statistics.h"

namespace smt {

    class pb_sls {
        struct imp;
        imp* m_imp;
    public:        
        pb_sls(ast_manager& m);        
        ~pb_sls();
        void add(expr* f);
        void add(expr* f, rational const& w);
        bool soft_holds(unsigned index);
        void set_model(model_ref& mdl);
        lbool operator()();
        void set_cancel(bool f);
        void collect_statistics(::statistics& st) const;
        void get_model(model_ref& mdl);
        void updt_params(params_ref& p);
        void reset();
    };


};

#endif
