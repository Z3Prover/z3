/*++
Copyright (c) Microsoft Corporation, Arive Gurfinkel 2017

Module Name:

    api_qe.cpp

Abstract:

    Model-based Projection (MBP) and Quantifier Elimination (QE) API

Author:

    Arie Gurfinkel (arie)

Notes:

--*/

#include <iostream>
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "api/api_model.h"
#include "api/api_ast_map.h"
#include "api/api_ast_vector.h"
#include "qe/qe_vartest.h"
#include "qe/qe_lite.h"
#include "muz/spacer/spacer_util.h"
#include "ast/expr_map.h"

extern "C"
{

    static bool to_apps(unsigned n, Z3_app const es[], app_ref_vector& result) {
        for (unsigned i = 0; i < n; ++i) {
            if (!is_app(to_app(es[i]))) {
                return false;
            }
            result.push_back (to_app (es [i]));
        }
        return true;
    }

    Z3_ast Z3_API Z3_qe_model_project (Z3_context c,
                                       Z3_model m,
                                       unsigned num_bounds,
                                       Z3_app const bound[],
                                       Z3_ast body)
    {
        Z3_TRY;
        LOG_Z3_qe_model_project (c, m, num_bounds, bound, body);
        RESET_ERROR_CODE();

        app_ref_vector vars(mk_c(c)->m ());
        if (!to_apps(num_bounds, bound, vars)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            RETURN_Z3(nullptr);
        }

        expr_ref result (mk_c(c)->m ());
        result = to_expr (body);
        model_ref model (to_model_ref (m));
        spacer::qe_project (mk_c(c)->m (), vars, result, *model);
        mk_c(c)->save_ast_trail (result.get ());

        return of_expr (result.get ());
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_qe_model_project_skolem (Z3_context c,
                                              Z3_model mdl,
                                              unsigned num_bounds,
                                              Z3_app const bound[],
                                              Z3_ast body,
                                              Z3_ast_map map)
    {
        Z3_TRY;
        LOG_Z3_qe_model_project_skolem (c, mdl, num_bounds, bound, body, map);
        RESET_ERROR_CODE();

        ast_manager& m = mk_c(c)->m();
        app_ref_vector vars(m);
        if (!to_apps(num_bounds, bound, vars)) {
            RETURN_Z3(nullptr);
        }

        expr_ref result (m);
        result = to_expr (body);
        model_ref model (to_model_ref (mdl));
        expr_map emap (m);

        spacer::qe_project(m, vars, result, model, emap);
        mk_c(c)->save_ast_trail(result);

        obj_map<ast, ast*> &map_z3 = to_ast_map_ref(map);

        for (auto& kv : emap) {
            m.inc_ref(kv.m_key);
            m.inc_ref(kv.m_value);
            map_z3.insert(kv.m_key, kv.m_value);
        }

        return of_expr (result);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_model_extrapolate (Z3_context c,
                                        Z3_model m,
                                        Z3_ast fml)
    {
        Z3_TRY;
        LOG_Z3_model_extrapolate (c, m, fml);
        RESET_ERROR_CODE();

        model_ref model (to_model_ref (m));
        expr_ref_vector facts (mk_c(c)->m ());
        facts.push_back (to_expr (fml));
        flatten_and (facts);

        expr_ref_vector lits (mk_c(c)->m());
        spacer::compute_implicant_literals (*model, facts, lits);

        expr_ref result (mk_c(c)->m ());
        result = mk_and (lits);
        mk_c(c)->save_ast_trail (result);

        return of_expr (result);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_qe_lite (Z3_context c, Z3_ast_vector vars, Z3_ast body)
    {
        Z3_TRY;
        LOG_Z3_qe_lite (c, vars, body);
        RESET_ERROR_CODE();
        ast_ref_vector &vVars = to_ast_vector_ref (vars);

        app_ref_vector vApps (mk_c(c)->m());
        for (ast* v : vVars) {
            app * a = to_app(v);
            if (a->get_kind () != AST_APP) {
                SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
                RETURN_Z3(nullptr);
            }
            vApps.push_back (a);
        }

        expr_ref result (mk_c(c)->m ());
        result = to_expr (body);

        params_ref p;
        qe_lite qe (mk_c(c)->m (), p);
        qe (vApps, result);

        // -- copy back variables that were not eliminated
        if (vApps.size () < vVars.size ()) {
            vVars.reset ();
            for (app* v : vApps) {
                vVars.push_back (v);
            }
        }

        mk_c(c)->save_ast_trail (result);
        return of_expr (result);
        Z3_CATCH_RETURN(nullptr);
    }

}
