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
#include"tactical.h"
#include"bound_manager.h"
#include"th_rewriter.h"
#include"extension_model_converter.h"
#include"filter_model_converter.h"
#include"arith_decl_plugin.h"
#include"expr_substitution.h"
#include"ast_smt2_pp.h"

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
        
        virtual void operator()(goal_ref const & in, 
                                goal_ref_buffer & result, 
                                model_converter_ref & mc, 
                                proof_converter_ref & pc,
                                expr_dependency_ref & core) {
            mc = 0; pc = 0; core = 0;
            bool produce_models = in->models_enabled();
            bool produce_proofs = in->proofs_enabled();
            tactic_report report("normalize-bounds", *in);
            
            m_bm(*in);
            
            if (!has_lowers()) {
                result.push_back(in.get());
                // did not increase depth since it didn't do anything.
                return;
            }
            
            extension_model_converter * mc1 = 0;
            filter_model_converter   * mc2  = 0;
            if (produce_models) {
                mc1 = alloc(extension_model_converter, m);
                mc2 = alloc(filter_model_converter, m);
                mc  = concat(mc2, mc1);
            }
            
            unsigned num_norm_bounds = 0;
            expr_substitution subst(m);
            rational val;
            bound_manager::iterator it  = m_bm.begin();
            bound_manager::iterator end = m_bm.end();
            for (; it != end; ++it) {
                expr * x = *it;
                if (is_target(x, val)) {
                    num_norm_bounds++;
                    sort * s = m.get_sort(x);
                    app * x_prime = m.mk_fresh_const(0, s);
                    expr * def = m_util.mk_add(x_prime, m_util.mk_numeral(val, s));
                    subst.insert(x, def);
                    if (produce_models) {
                        mc1->insert(to_app(x)->get_decl(), def);
                        mc2->insert(x_prime->get_decl());
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

    virtual tactic * translate(ast_manager & m) {
        return alloc(normalize_bounds_tactic, m, m_params);
    }

    virtual ~normalize_bounds_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) { 
        insert_produce_models(r);
        r.insert("norm_int_only", CPK_BOOL, "(default: true) normalize only the bounds of integer constants.");
    }

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        try {
            (*m_imp)(in, result, mc, pc, core);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }
    
    virtual void cleanup() {
        ast_manager & m = m_imp->m;
        imp * d = alloc(imp, m, m_params);
        std::swap(d, m_imp);        
        dealloc(d);
    }
};

tactic * mk_normalize_bounds_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(normalize_bounds_tactic, m, p));
}
