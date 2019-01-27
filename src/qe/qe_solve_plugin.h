/**
Copyright (c) 2018 Microsoft Corporation

Module Name:

    qe_solve.h

Abstract:

    Light-weight variable solving plugin model for qe-lite and term_graph.

Author:

    Nikolaj Bjorner (nbjorner), Arie Gurfinkel 2018-6-8

Revision History:


--*/

#pragma once

#include "ast/ast.h"
#include "util/plugin_manager.h"
#include "qe/qe_vartest.h"

namespace qe {

    class solve_plugin {
    protected:
        ast_manager&      m;
        family_id         m_id;
        is_variable_proc& m_is_var;

        virtual expr_ref solve(expr* atom, bool is_pos) = 0;
        bool is_variable(expr* e) const { return m_is_var(e); }
    public:
        solve_plugin(ast_manager& m, family_id fid, is_variable_proc& is_var) : m(m), m_id(fid), m_is_var(is_var) {}
        virtual ~solve_plugin() {}
        family_id get_family_id() const { return m_id; }
        /// Process (and potentially augment) a literal
        expr_ref operator() (expr *lit);
    };

    solve_plugin* mk_basic_solve_plugin(ast_manager& m, is_variable_proc& is_var);

    solve_plugin* mk_arith_solve_plugin(ast_manager& m, is_variable_proc& is_var);

    solve_plugin* mk_dt_solve_plugin(ast_manager& m, is_variable_proc& is_var);

    // solve_plugin* mk_bv_solve_plugin(ast_manager& m, is_variable_proc& is_var);

    // solve_plugin* mk_array_solve_plugin(ast_manager& m, is_variable_proc& is_var);
}
