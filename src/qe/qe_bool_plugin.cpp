/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    qe_bool_plugin.cpp

Abstract:

    Eliminate Boolean variable from formula

Author:

    Nikolaj Bjorner (nbjorner) 2010-02-19

Revision History:

Notes:

    The procedure is a bit naive.
    Consider a co-factoring approach that eliminates all Boolean
    variables in scope in one shot, similar to what we do with
    BDDs.

--*/

#include "qe/qe.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/ast_pp.h"
#include "model/model_evaluator.h"


namespace qe {
    class bool_plugin : public qe_solver_plugin {
        expr_safe_replace m_replace;
    public:
        bool_plugin(i_solver_context& ctx, ast_manager& m):
            qe_solver_plugin(m, m.get_basic_family_id(), ctx),
            m_replace(m)
        {}
        
        void assign(contains_app& x, expr* fml, rational const& vl) override {
            SASSERT(vl.is_zero() || vl.is_one());
        }

        bool get_num_branches(contains_app& x, expr* fml, rational& nb) override {
            nb = rational(2);
            return true;
        }

        void subst(contains_app& x, rational const& vl, expr_ref& fml, expr_ref* def) override {
            SASSERT(vl.is_one() || vl.is_zero());
            expr* tf = (vl.is_one())?m.mk_true():m.mk_false();
            m_replace.apply_substitution(x.x(), tf, fml);
            if (def) {
                *def = tf;
            }
        }

        bool project(contains_app& x, model_ref& model, expr_ref& fml) override {
            model_evaluator model_eval(*model);
            expr_ref val_x(m);
            rational val;
            model_eval(x.x(), val_x);
            CTRACE("qe", (!m.is_true(val_x) && !m.is_false(val_x)),
                   tout << "Boolean is a don't care: " << mk_pp(x.x(), m) << "\n";);
            val = m.is_true(val_x)?rational::one():rational::zero();
            subst(x, val, fml, nullptr);
            return true;
        }

        unsigned get_weight(contains_app& contains_x, expr* fml) override {
            app* x = contains_x.x();            
            bool p = m_ctx.pos_atoms().contains(x);
            bool n = m_ctx.neg_atoms().contains(x);
            if (p && n) {
                return 3;
            }
            return 0;
        }

        bool solve(conj_enum& conjs,expr* fml) override {
            return 
                solve_units(conjs, fml) ||
                solve_polarized(fml);
        }
        
        bool is_uninterpreted(app* a) override {
            return false;
        }

    private:

        bool solve_units(conj_enum& conjs, expr* _fml) {
            expr_ref fml(_fml, m);
            conj_enum::iterator it = conjs.begin(), end = conjs.end();
            unsigned idx;
            for (; it != end; ++it) {
                expr* e = *it;
                if (!is_app(e)) {
                    continue;
                }
                app* a = to_app(e);
                expr* e1;
                if (m_ctx.is_var(a, idx)) {
                    m_replace.apply_substitution(a, m.mk_true(), fml);
                    m_ctx.elim_var(idx, fml, m.mk_true());
                    return true;
                }
                else if (m.is_not(e, e1) && m_ctx.is_var(e1, idx)) {
                    m_replace.apply_substitution(to_app(e1), m.mk_false(), fml);         
                    m_ctx.elim_var(idx, fml, m.mk_false());
                    return true;           
                }
            }
            return false;
        }

        bool solve_polarized(expr* _fml) {
            unsigned num_vars = m_ctx.get_num_vars();
            expr_ref fml(_fml, m), def(m);
            for (unsigned i = 0; i < num_vars; ++i) {
                if (m.is_bool(m_ctx.get_var(i)) &&
                    solve_polarized(m_ctx.contains(i), fml, def)) {
                    m_ctx.elim_var(i, fml, def);
                    return true;
                }
            }
            return false;
        }

        bool solve_polarized( contains_app& contains_x, expr_ref& fml, expr_ref& def) {
            app* x = contains_x.x();            
            bool p = m_ctx.pos_atoms().contains(x);
            bool n = m_ctx.neg_atoms().contains(x);
            TRACE("quant_elim", tout << mk_pp(x, m) << " " << mk_pp(fml, m) << "\n";);
            if (p && n) {
                return false;
            }
            else if (p && !n) {
                atom_set::iterator it = m_ctx.pos_atoms().begin(), end = m_ctx.pos_atoms().end();
                for (; it != end; ++it) {
                    if (x != *it && contains_x(*it)) return false;
                }
                it = m_ctx.neg_atoms().begin(), end = m_ctx.neg_atoms().end();
                for (; it != end; ++it) {
                    if (contains_x(*it)) return false;
                }
                // only occurrences of 'x' must be in positive atoms
                def = m.mk_true();
                m_replace.apply_substitution(x, def, fml);
                return true;
            }
            else if (!p && n) {
                atom_set::iterator it = m_ctx.pos_atoms().begin(), end = m_ctx.pos_atoms().end();
                for (; it != end; ++it) {
                    if (contains_x(*it)) return false;
                }
                it = m_ctx.neg_atoms().begin(), end = m_ctx.neg_atoms().end();
                for (; it != end; ++it) {
                    if (x != *it && contains_x(*it)) return false;
                }
                def = m.mk_false();
                m_replace.apply_substitution(x, def, fml);
                return true;            
            }
            else if (contains_x(fml)) {
                return false;
            }
            else {
                def = m.mk_false();
                return true;
            }
        }
    };
    
    qe_solver_plugin* mk_bool_plugin(i_solver_context& ctx) {
        return alloc(bool_plugin, ctx, ctx.get_manager());
    }
}
