/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    elim01_tactic.cpp

Abstract:

    Replace 0-1 integer variables by Booleans.

Author:
 
    Nikolaj Bjorner (nbjorner) 2013-12-7

Notes:

--*/
#include"tactical.h"
#include"cooperate.h"
#include"bound_manager.h"
#include"ast_pp.h"
#include"expr_safe_replace.h" // NB: should use proof-producing expr_substitute in polished version.
#include"arith_decl_plugin.h"
#include"elim01_tactic.h"

class bool2int_model_converter : public model_converter {
    ast_manager&      m;
    arith_util        a;
    func_decl_ref_vector m_refs;
    obj_map<func_decl, func_decl*> m_bool2int;
public:

    bool2int_model_converter(ast_manager& m):
        m(m),
        a(m),
        m_refs(m)
    {}

    virtual void operator()(model_ref & old_model, unsigned goal_idx) {
        SASSERT(goal_idx == 0);
        model * new_model = alloc(model, m);
        unsigned num = old_model->get_num_constants();
        for (unsigned i = 0; i < num; ++i) {
            func_decl* f = old_model->get_constant(i);
            expr* fi = old_model->get_const_interp(f);
            func_decl* f_old;
            if (m_bool2int.find(f, f_old)) {
                if (!fi) {
                    // no-op
                }
                else if (m.is_false(fi)) {
                    fi = a.mk_numeral(rational(0), true);
                }
                else if (m.is_true(fi)) {
                    fi = a.mk_numeral(rational(1), true);
                }
                else {
                    fi = 0;
                }
                new_model->register_decl(f_old, fi);
            }
            else {
                new_model->register_decl(f, fi);
            }
            num = old_model->get_num_functions();
            for (unsigned i = 0; i < num; i++) {
                func_decl * f = old_model->get_function(i);
                func_interp * fi = old_model->get_func_interp(f);
                new_model->register_decl(f, fi->copy());
            }
            new_model->copy_usort_interps(*old_model);
            old_model = new_model;
        }        
    }

    void insert(func_decl* x_new, func_decl* x_old) {
        m_refs.push_back(x_new);
        m_refs.push_back(x_old);
        m_bool2int.insert(x_new, x_old);
    }


    virtual model_converter * translate(ast_translation & translator) {
        bool2int_model_converter* mc = alloc(bool2int_model_converter, translator.to());
        obj_map<func_decl, func_decl*>::iterator it = m_bool2int.begin(), end = m_bool2int.end();
        for (; it != end; ++it) {
            mc->insert(translator(it->m_key), translator(it->m_value));
        }
        return mc;
    }
};


class elim01_tactic : public tactic {
public:
    typedef obj_hashtable<expr> expr_set;
    ast_manager &                    m;
    arith_util                       a;
    params_ref                       m_params;
    
    elim01_tactic(ast_manager & _m, params_ref const & p):
        m(_m),
        a(m) {
    }

    virtual ~elim01_tactic() {
    }
        
    void set_cancel(bool f) {
    }
        
    void updt_params(params_ref const & p) {
        m_params = p;
    }
    
    virtual void operator()(goal_ref const & g, 
                    goal_ref_buffer & result, 
                    model_converter_ref & mc, 
                    proof_converter_ref & pc,
                    expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        mc = 0; pc = 0; core = 0;
        
        tactic_report report("elim01", *g);
        
        expr_safe_replace sub(m);
        bool2int_model_converter* b2i = alloc(bool2int_model_converter, m);
        mc = b2i;
        bound_manager bounds(m);
        bounds(*g);
        
        bound_manager::iterator bit = bounds.begin(), bend = bounds.end();
        for (; bit != bend; ++bit) {
            if (!is_app(*bit)) continue;
            app* x = to_app(*bit);
            bool s1, s2;
            rational lo, hi;
            if (a.is_int(x) && 
                bounds.has_lower(x, lo, s1) && !s1 && lo.is_zero() &&
                bounds.has_upper(x, hi, s2) && !s2 && hi.is_one()) {
                app* x_new = m.mk_fresh_const(x->get_decl()->get_name().str().c_str(), m.mk_bool_sort());
                sub.insert(x, m.mk_ite(x_new, a.mk_numeral(rational(1), true), 
                                       a.mk_numeral(rational(0), true)));
                b2i->insert(x_new->get_decl(), x->get_decl());
            }
        }
               
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        
        for (unsigned i = 0; i < g->size(); i++) {
            expr * curr = g->form(i);
            sub(curr, new_curr);           
            g->update(i, new_curr, new_pr, g->dep(i));
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("pb", g->display(tout););
        SASSERT(g->is_well_sorted());
        
        // TBD: support proof conversion (or not..)
    }
    
    virtual tactic * translate(ast_manager & m) {
        return alloc(elim01_tactic, m, m_params);
    }
        
    virtual void collect_param_descrs(param_descrs & r) {}
        
    virtual void cleanup() {}
};

tactic * mk_elim01_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(elim01_tactic, m, p));
}

