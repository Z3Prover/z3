/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_curve_certificate.h

Abstract:

    Certify that an objective is unbounded above along a polynomial curve
    through recent models. The curve starts at the latest model and
    continues it with the backward differences of the earlier models: a
    ray through the last two models, a quadratic through the last three, a
    cubic through the last four, or a unit direction of one objective
    variable. Integer coordinates stay integral at integer parameters. The
    certificate is two solver results over the integer curve parameter t:
    no t >= 0 violates a hard constraint, and the objective along the curve
    is a non-constant polynomial that never drops below its value at the
    latest model. A non-constant polynomial bounded below on the integers
    tends to +oo, so the objective is unbounded above. Unlike the nlsat
    projection this applies to integer and mixed objectives.

Author:

    Lev Nachmanson (levnach) 2026-10-29

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "model/model.h"
#include "util/lbool.h"
#include "util/params.h"

namespace opt {

    class curve_certificate {
    public:
        static unsigned const max_degree = 3;

        curve_certificate(ast_manager& m, params_ref const& p);

        // Returns l_true when obj is unbounded above over the hard
        // constraints. models holds feasible models, the most recent last;
        // at most the last max_degree + 1 are used.
        lbool prove_unbounded(expr_ref_vector const& hard, expr* obj, sref_vector<model> const& models);

        // Describes the curve of the last successful certificate.
        char const* kind_name() const;

    private:
        // c(t) = sum of coefficient[j] * B_j(t) with B_0 = 1, B_1 = t,
        // B_j(t) = t (t + 1) ... (t + j - 1) / j!
        typedef vector<rational> coefficients;

        ast_manager& m;
        arith_util   a;
        params_ref   m_params;
        unsigned     m_degree = 1;
        bool         m_unit = false;

        void collect_constants(expr_ref_vector const& hard, expr* obj, ptr_vector<app>& arith_consts, ptr_vector<app>& other_consts);
        bool is_polynomial(expr* e);
        bool evaluate(model& mdl, ptr_vector<app> const& consts, vector<rational>& values);
        bool certify(expr_ref_vector const& hard, expr* obj, model& latest, ptr_vector<app> const& arith_consts,
                     ptr_vector<app> const& other_consts, vector<coefficients> const& curve, unsigned degree, bool unit);
    };
}
