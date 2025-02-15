
/*++
Copyright (c) 2025 Microsoft Corporation

--*/


#pragma once

#include "model/model.h"
#include "qe/mbp/mbp_plugin.h"

namespace mbp {

    class euf_project_plugin : public project_plugin {
    public:
        euf_project_plugin(ast_manager& m);
        ~euf_project_plugin() override;
        
        bool project1(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) override;
        bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) override { return false; }
        family_id get_family_id() override;
        bool operator()(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;
        bool project(model& model, app_ref_vector& vars, expr_ref_vector& lits, vector<def>& defs) override;
        void saturate(model& model, func_decl_ref_vector const& shared, expr_ref_vector& lits) override { UNREACHABLE(); }

    };

};

