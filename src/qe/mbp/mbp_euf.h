
/*++
Copyright (c) 2025 Microsoft Corporation

--*/


#pragma once

#include "model/model.h"
#include "qe/mbp/mbp_plugin.h"
#include "qe/mbp/mbp_term_graph.h"

namespace mbp {

    class euf_project_plugin : public project_plugin {
        obj_map<expr, expr*> m_reps;
        obj_map<expr, ptr_vector<expr>> m_parents;
        void solve_eqs(model& model, app_ref_vector& vars, expr_ref_vector& lits, vector<def>& defs);
        bool solve_eqs_saturate(model& model, app_ref_vector& vars, expr_ref_vector& lits, vector<def>& defs);
        bool try_unify(term_graph& g, app* a, expr_ref_vector const& partitions, app_ref_vector& vars, vector<def>& defs);
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

