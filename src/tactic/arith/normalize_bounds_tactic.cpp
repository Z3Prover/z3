/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    normalize_bounds_tactic.cpp

Abstract:

    Replace x with x' + l, when l <= x
    where x' is a fresh variable.
    Note that, after the transformation 0 <= x'.

Author:

    Leonardo de Moura (leonardo) 2011-10-21.

Revision History:

--*/
#include "tactic/tactical.h"
#include "tactic/arith/bound_manager.h"
#include "ast/rewriter/th_rewriter.h"
#include "tactic/generic_model_converter.h"
#include "ast/arith_decl_plugin.h"
#include "ast/expr_substitution.h"
#include "ast/ast_smt2_pp.h"

class normalize_bounds_tactic : public tactic {
    struct imp {
        ast_manager &    m;
        bound_manager    m_bm;
        arith_util       m_util;
        th_rewriter      m_rw;
        bool             m_normalize_int_only;
        
        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_bm(m),
            m_util(m),
            m_rw(m, p) {
            updt_params(p);
        }
        
        void updt_params_core(params_ref const & p) {
            m_normalize_int_only = p.get_bool("norm_int_only", true);
        }
        
        void updt_params(params_ref const & p) {
            m_rw.updt_params(p);
            updt_params_core(p);
        }
        
        
        bool is_target(expr * var, rational & val) {
            bool strict;
            return 
                is_uninterp_const(var) && 
                (!m_normalize_int_only || m_util.is_int(var)) && 
                m_bm.has_lower(var, val, strict) && 
                !val.is_zero();
        }
        
        bool is_target(expr * var) {
            rational val;
            return is_target(var, val);
        }
        
        bool has_lowers() {
            bound_manager::iterator it  = m_bm.begin();
            bound_manager::iterator end = m_bm.end();
            for (; it != end; ++it) {
                TRACE("normalize_bounds_tactic", 
                      rational val; bool strict;
                      tout << mk_ismt2_pp(*it, m) << " has_lower: " << m_bm.has_lower(*it, val, strict) << " val: " << val << "\n";);
                if (is_target(*it))
                    return true;
            }
            return false;
        }
        
        void operator()(goal_ref const & in, goal_ref_buffer & result) {
            bool produce_models = in->models_enabled();
            bool produce_proofs = in->proofs_enabled();
            tactic_report report("normalize-bounds", *in);
            
            m_bm(*in);
            
            if (!has_lowers()) {
                result.push_back(in.get());
                // did not increase depth since it didn't do anything.
                return;
            }
            
            generic_model_converter   * gmc  = nullptr;
            if (produce_models) {
                gmc = alloc(generic_model_converter, m, "normalize_bounds");
                in->add(gmc);
            }
            
            unsigned num_norm_bounds = 0;
            expr_substitution subst(m);
            rational val;
            for (expr * x : m_bm) {
                if (is_target(x, val)) {
                    num_norm_bounds++;
                    sort * s = m.get_sort(x);
                    app * x_prime = m.mk_fresh_const(nullptr, s);
                    expr * def = m_util.mk_add(x_prime, m_util.mk_numeral(val, s));
                    subst.insert(x, def);
                    if (produce_models) {
                        gmc->add(to_app(x)->get_decl(), def);
                        gmc->hide(x_prime->get_decl());
                    }
                }
            }
            
            report_tactic_progress(":normalized-bounds", num_norm_bounds);
            
            m_rw.set_substitution(&subst);
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            unsigned size = in->size();
            for (unsigned idx = 0; idx < size; idx++) {
                expr * curr = in->form(idx);
                m_rw(curr, new_curr, new_pr);
                if (produce_proofs) {
                    proof * pr = in->pr(idx);
                    new_pr     = m.mk_modus_ponens(pr, new_pr);
                }
                in->update(idx, new_curr, new_pr, in->dep(idx));
            }
            TRACE("normalize_bounds_tactic", in->display(tout););
            in->inc_depth();
            result.push_back(in.get());
        }
    };

    imp *      m_imp;
    params_ref m_params;

public:
    normalize_bounds_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(normalize_bounds_tactic, m, m_params);
    }

    ~normalize_bounds_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_produce_models(r);
        r.insert("norm_int_only", CPK_BOOL, "(default: true) normalize only the bounds of integer constants.");
    }

    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        try {
            (*m_imp)(in, result);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }
    
    void cleanup() override {
        ast_manager & m = m_imp->m;
        imp * d = alloc(imp, m, m_params);
        std::swap(d, m_imp);        
        dealloc(d);
    }
};

tactic * mk_normalize_bounds_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(normalize_bounds_tactic, m, p));
}
