/**
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_legacy_mbp.cpp

Abstract:

   Legacy Model Based Projection. Used by Grigory Fedyukovich

Author:

    Arie Gurfinkel
    Anvesh Komuravelli
Notes:

--*/
#include <sstream>

#include "ast/array_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/bool_rewriter.h"
#include "muz/base/dl_util.h"
#include "ast/for_each_expr.h"
#include "smt/params/smt_params.h"
#include "model/model.h"
#include "util/ref_vector.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "util/util.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_util.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/expr_replacer.h"
#include "model/model_smt2_pp.h"
#include "ast/scoped_proof.h"
#include "qe/qe_lite.h"
#include "muz/spacer/spacer_qe_project.h"
#include "model/model_pp.h"
#include "ast/rewriter/expr_safe_replace.h"

#include "ast/datatype_decl_plugin.h"
#include "ast/bv_decl_plugin.h"

#include "muz/spacer/spacer_legacy_mev.h"

namespace spacer {
void qe_project(ast_manager& m, app_ref_vector& vars, expr_ref& fml, model_ref& M, expr_map& map)
{
    th_rewriter rw(m);
    // qe-lite; TODO: use qe_lite aggressively
    params_ref p;
    qe_lite qe(m, p, true);
    qe(vars, fml);
    rw(fml);

    TRACE("spacer",
          tout << "After qe_lite:\n";
          tout << mk_pp(fml, m) << "\n";
          tout << "Vars:\n";
    for (unsigned i = 0; i < vars.size(); ++i) {
    tout << mk_pp(vars.get(i), m) << "\n";
    }
         );

    // substitute model values for booleans and
    // use LW projection for arithmetic variables
    if (!vars.empty()) {
        app_ref_vector arith_vars(m);
        expr_substitution sub(m);
        proof_ref pr(m.mk_asserted(m.mk_true()), m);
        expr_ref bval(m);
        model::scoped_model_completion _scm(*M, true);
        for (unsigned i = 0; i < vars.size(); i++) {
            if (m.is_bool(vars.get(i))) {
                // obtain the interpretation of the ith var using model completion
                bval = (*M)(vars.get(i));
                sub.insert(vars.get(i), bval, pr);
            } else {
                arith_vars.push_back(vars.get(i));
            }
        }
        if (!sub.empty()) {
            scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer(m);
            rep->set_substitution(&sub);
            (*rep)(fml);
            rw(fml);
            TRACE("spacer",
                  tout << "Projected Boolean vars:\n" << mk_pp(fml, m) << "\n";
                 );
        }
        // model based projection
        if (!arith_vars.empty()) {
            TRACE("spacer",
                  tout << "Arith vars:\n";
            for (unsigned i = 0; i < arith_vars.size(); ++i) {
            tout << mk_pp(arith_vars.get(i), m) << "\n";
            }
                 );
            {
                scoped_no_proof _sp(m);
                spacer_qe::arith_project(*M, arith_vars, fml, map);
            }
            SASSERT(arith_vars.empty());
            TRACE("spacer",
                  tout << "Projected arith vars:\n" << mk_pp(fml, m) << "\n";
                 );
        }
        SASSERT(M->is_true(fml));
        vars.reset();
        vars.append(arith_vars);
    }
}
}
