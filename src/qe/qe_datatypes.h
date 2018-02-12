/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_datatypes.h

Abstract:

    Model based projection for algebraic datatypes

Author:

    Nikolaj Bjorner (nbjorner) 2015-06-13

Revision History:

--*/


#ifndef __QE_DATATYPES_H_
#define __QE_DATATYPES_H_

#include "ast/datatype_decl_plugin.h"
#include "qe/qe_mbp.h"

namespace qe {

    class datatype_project_plugin : public project_plugin {
        struct imp;
        imp* m_imp;
    public:
        datatype_project_plugin(ast_manager& m);
        ~datatype_project_plugin() override;
        bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) override;
        bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;
        family_id get_family_id() override;
    };

};

#endif
