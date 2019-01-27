/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    bv_plugin.cpp

Abstract:

    Eliminate Bit-vector variable from formula

Author:

    Nikolaj Bjorner (nbjorner) 2010-02-19

Revision History:

Notes:


--*/

#include "qe/qe.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/bv_decl_plugin.h"
#include "model/model_evaluator.h"

namespace qe {

    class bv_plugin : public qe_solver_plugin {
        expr_safe_replace m_replace;
        bv_util           m_bv;
    public:
        bv_plugin(i_solver_context& ctx, ast_manager& m): 
            qe_solver_plugin(m, m.mk_family_id("bv"), ctx),
            m_replace(m),
            m_bv(m)
        {}

        void assign(contains_app& x, expr* fml, rational const& vl) override {
        }

        bool get_num_branches(contains_app& x, expr* fml, rational& nb) override {
            unsigned sz = m_bv.get_bv_size(x.x());
            nb = power(rational(2), sz);
            return true;
        }

        void subst(contains_app& x, rational const& vl, expr_ref& fml, expr_ref* def) override {
            app_ref c(m_bv.mk_numeral(vl, m_bv.get_bv_size(x.x())), m);
            m_replace.apply_substitution(x.x(), c, fml);
            if (def) {
                *def = m_bv.mk_numeral(vl, m_bv.get_bv_size(x.x()));
            }
        }

        bool project(contains_app& x, model_ref& model, expr_ref& fml) override {
            model_evaluator model_eval(*model);
            expr_ref val_x(m);
            rational val(0);
            unsigned bv_size;
            model_eval(x.x(), val_x);
            m_bv.is_numeral(val_x, val, bv_size);
            subst(x, val, fml, nullptr);
            return true;
        }

        unsigned get_weight(contains_app& contains_x, expr* fml) override {
            return 2;
        }

        bool solve(conj_enum& conjs, expr* fml) override { return false; }

        bool is_uninterpreted(app* f) override {
            switch(f->get_decl_kind()) {
            case OP_BSDIV0: 
            case OP_BUDIV0:
            case OP_BSREM0:
            case OP_BUREM0:
            case OP_BSMOD0:
            case OP_BSDIV_I:
            case OP_BUDIV_I:
            case OP_BSREM_I:
            case OP_BUREM_I:
            case OP_BSMOD_I:
                return true;
            default:
                return false;
            }
            return false;
        }
    };
    
    qe_solver_plugin* mk_bv_plugin(i_solver_context& ctx) {
        return alloc(bv_plugin, ctx, ctx.get_manager());
    }
}
