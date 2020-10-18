/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    mbp_arrays.h

Abstract:

    Model based projection for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2015-06-13

Revision History:

--*/


#pragma once

#include "ast/array_decl_plugin.h"
#include "qe/mbp/mbp_plugin.h"

namespace mbp {

    class array_project_plugin : public project_plugin {
        struct imp;
        imp* m_imp;
    public:
        array_project_plugin(ast_manager& m);
        ~array_project_plugin() override;
        bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) override;
        bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;
        void operator()(model& model, app_ref_vector& vars, expr_ref& fml, app_ref_vector& aux_vars, bool reduce_all_selects);
        family_id get_family_id() override;
        vector<def> project(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;
        void saturate(model& model, func_decl_ref_vector const& shared, expr_ref_vector& lits) override;

    };

};

