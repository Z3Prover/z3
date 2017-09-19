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
#ifndef PB_SLS_H_
#define PB_SLS_H_

#include "ast/pb_decl_plugin.h"
#include "model/model.h"
#include "util/lbool.h"
#include "util/params.h"
#include "util/statistics.h"

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
        void collect_statistics(::statistics& st) const;
        void get_model(model_ref& mdl);
        void updt_params(params_ref& p);
        void reset();
    };


};

#endif
