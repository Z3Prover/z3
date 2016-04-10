/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    eq2bv_tactic.cpp

Abstract:

    Extract integer variables that are used as finite domain indicators.
    The integer variables can only occur in equalities.

Author:

    Nikolaj Bjorner (nbjorner) 2015-8-19

Notes:

--*/
#include"tactical.h"
#include"cooperate.h"
#include"bound_manager.h"
#include"ast_pp.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"rewriter_def.h"
#include"ast_util.h"
#include"ast_pp_util.h"

class eq2bv_tactic : public tactic {
    struct eq_rewriter_cfg : public default_rewriter_cfg {
        ast_manager&     m;
        eq2bv_tactic&    t;

        bool is_fd(expr* x, expr* y, expr_ref& result) {
            expr* z;
            rational r;
            if (t.m_fd.find(x, z) && t.a.is_numeral(y, r)) {
                result = m.mk_eq(z, t.bv.mk_numeral(r, m.get_sort(z)));
                return true;
            }
            else {
                return false;
            }
        }

        br_status mk_app_core(func_decl* f, unsigned sz, expr*const* es, expr_ref& result) {
            if (m.is_eq(f)) {
                if (is_fd(es[0], es[1], result)) {
                    return BR_DONE;
                }    
                else if (is_fd(es[1], es[0], result)) {
                    return BR_DONE;
                }
            }    
            return BR_FAILED;            
        }

        bool rewrite_patterns() const { return false; }
        bool flat_assoc(func_decl * f) const { return false; }
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            result_pr = 0;
            return mk_app_core(f, num, args, result);
        }
        eq_rewriter_cfg(eq2bv_tactic& t):m(t.m), t(t) {}
    };        

    class eq_rewriter : public rewriter_tpl<eq_rewriter_cfg> {
        eq_rewriter_cfg m_cfg;
    public:
        eq_rewriter(eq2bv_tactic& t):
            rewriter_tpl<eq_rewriter_cfg>(t.m, false, m_cfg),
            m_cfg(t)
        {}
    };

    class bvmc : public model_converter {
        obj_map<func_decl, func_decl*> m_map;
    public:
        
        void insert(func_decl* c_new, func_decl* c_old) {
            m_map.insert(c_new, c_old);
        }

        virtual void operator()(model_ref& mdl) {
            ast_manager& m = mdl->get_manager();
            bv_util bv(m);
            arith_util a(m);
            rational r;
            model_ref new_m = alloc(model, m);
            new_m->copy_func_interps(*mdl);
            new_m->copy_usort_interps(*mdl);
            unsigned sz = mdl->get_num_constants(), bvsz;
            for (unsigned i = 0; i < sz; ++i) {
                func_decl* f = mdl->get_constant(i), *g;
                expr* val = mdl->get_const_interp(f);
                if (m_map.find(f, g) && bv.is_numeral(val, r, bvsz)) {
                    val = a.mk_numeral(r, true);
                    new_m->register_decl(g, val);
                }
                else {
                    new_m->register_decl(f, val);
                }
            }
            mdl = new_m;
        }
        
        virtual model_converter* translate(ast_translation & translator) {
            bvmc* v = alloc(bvmc);
            obj_map<func_decl, func_decl*>::iterator it = m_map.begin(), end = m_map.end();
            for (; it != end; ++it) {
                v->m_map.insert(translator(it->m_key), translator(it->m_value));
            }
            return v;
        }
    };

public:
    ast_manager &                    m;
    arith_util                       a;
    bv_util                          bv;
    eq_rewriter                      m_rw;
    expr_ref_vector                  m_trail;
    bound_manager                    m_bounds;
    obj_map<expr, expr*>             m_fd;
    obj_map<expr, unsigned>          m_max;
    expr_mark                        m_nonfd;
    ptr_vector<expr>                 m_todo;
        
    eq2bv_tactic(ast_manager & _m):
        m(_m),
        a(m),
        bv(m),
        m_rw(*this),
        m_trail(m),
        m_bounds(m) {
    }

    virtual ~eq2bv_tactic() {
    }
        
        
    void updt_params(params_ref const & p) {
    }
    
    virtual void operator()(
        goal_ref const & g, 
        goal_ref_buffer & result, 
        model_converter_ref & mc, 
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        mc = 0; pc = 0; core = 0;
        m_trail.reset();
        m_fd.reset();
        m_max.reset();
        m_nonfd.reset();
        m_bounds.reset();
        ref<bvmc> mc1 = alloc(bvmc);

        tactic_report report("eq2bv", *g);

        m_bounds(*g);

        for (unsigned i = 0; i < g->size(); i++) {            
            collect_fd(g->form(i));
        }
        cleanup_fd(mc1);
        
        if (m_max.empty()) {
            result.push_back(g.get());
            return;
        }

        for (unsigned i = 0; i < g->size(); i++) {            
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);  
            if (is_bound(g->form(i))) {
                g->update(i, m.mk_true(), 0, 0);
                continue;
            }
            m_rw(g->form(i), new_curr, new_pr);
            if (m.proofs_enabled() && !new_pr) {
                new_pr = m.mk_rewrite(g->form(i), new_curr);
                new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
            }
            g->update(i, new_curr, new_pr, g->dep(i));
        }
        obj_map<expr, unsigned>::iterator it = m_max.begin(), end = m_max.end();
        for (; it != end; ++it) {
            expr* c = it->m_key;
            bool strict;
            rational r;
            expr_ref fml(m);
            if (m_bounds.has_lower(c, r, strict) && !r.is_neg()) {
                SASSERT(!strict);
                expr* d = m_fd.find(c);
                fml = bv.mk_ule(bv.mk_numeral(r, m.get_sort(d)), d);
                g->assert_expr(fml, m_bounds.lower_dep(c));
            }
            if (m_bounds.has_upper(c, r, strict) && !r.is_neg()) {
                SASSERT(!strict);
                expr* d = m_fd.find(c);
                fml = bv.mk_ule(d, bv.mk_numeral(r, m.get_sort(d)));
                g->assert_expr(fml, m_bounds.upper_dep(c));
            }
        }        
        g->inc_depth();
        mc = mc1.get();
        result.push_back(g.get());
        TRACE("pb", g->display(tout););
        SASSERT(g->is_well_sorted());        
    }


    virtual tactic * translate(ast_manager & m) {
        return alloc(eq2bv_tactic, m);
    }
        
    virtual void collect_param_descrs(param_descrs & r) {
    }
        
    virtual void cleanup() {        
    }

    void cleanup_fd(ref<bvmc>& mc) {
        SASSERT(m_fd.empty());
        ptr_vector<expr> rm;
        obj_map<expr, unsigned>::iterator it = m_max.begin(), end = m_max.end();
        for (; it != end; ++it) {
            if (m_nonfd.is_marked(it->m_key)) {
                rm.push_back(it->m_key);
            }
        }
        for (unsigned i = 0; i < rm.size(); ++i) {
            m_max.erase(rm[i]);
        }
        it  = m_max.begin();
        end = m_max.end();
        for (; it != end; ++it) {
            // ensure there are enough elements.
            bool strict;
            rational val;
            if (m_bounds.has_upper(it->m_key, val, strict)) {
                SASSERT(!strict);
                if (val.get_unsigned() > it->m_value) it->m_value = val.get_unsigned();
            }
            else {
                ++it->m_value; 
            }
            unsigned p = next_power_of_two(it->m_value);            
            if (p <= 1) p = 2;
            if (it->m_value == p) p *= 2;
            unsigned n = log2(p);
            app* z = m.mk_fresh_const("z", bv.mk_sort(n));
            m_trail.push_back(z);
            m_fd.insert(it->m_key, z);
            mc->insert(z->get_decl(), to_app(it->m_key)->get_decl());
        }
    }

    bool is_var_const_pair(expr* e, expr* c, unsigned& k) {
        rational r;
        if (is_uninterp_const(e) && a.is_numeral(c, r) && r.is_unsigned() && !m_nonfd.is_marked(e)) {
            k = r.get_unsigned();
            return true;
        }
        else {
            return false;
        }
    }

    bool is_upper(expr* f) {
        expr* e1, *e2;
        unsigned k;
        if ((a.is_le(f, e1, e2) || a.is_ge(f, e2, e1)) && is_var_const_pair(e1, e2, k)) {
            SASSERT(m_bounds.has_upper(e1));
            return true;
        } 
        return false;
    }

    bool is_lower(expr* f) {
        expr* e1, *e2;
        unsigned k;
        if ((a.is_le(f, e1, e2) || a.is_ge(f, e2, e1)) && is_var_const_pair(e2, e1, k)) {
            SASSERT(m_bounds.has_lower(e2));
            return true;
        } 
        return false;
    }

    bool is_bound(expr* f) {
        return is_lower(f) || is_upper(f);
    }

    void collect_fd(expr* f) {
        if (is_bound(f)) return;
        m_todo.push_back(f);
        while (!m_todo.empty()) {
            f = m_todo.back();
            m_todo.pop_back();
            if (m_nonfd.is_marked(f)) {
                continue;
            }
            m_nonfd.mark(f, true);
            expr* e1, *e2;
            if (m.is_eq(f, e1, e2)) {
                if (is_fd(e1, e2) || is_fd(e2, e1)) {
                    continue;
                }            
            }
            if (is_app(f)) {
                m_todo.append(to_app(f)->get_num_args(), to_app(f)->get_args());
            }
            else if (is_quantifier(f)) {
                m_todo.push_back(to_quantifier(f)->get_expr());
            }
        }
    }

    bool is_fd(expr* v, expr* c) {
        unsigned val;
        rational r;
        if (is_uninterp_const(v) && a.is_numeral(c, r) && !m_nonfd.is_marked(v) && a.is_int(v) && r.is_unsigned()) {
            val = r.get_unsigned();
            add_fd(v, val);
            return true;
        }
        return false;
    }

    void add_fd(expr* c, unsigned val) {
        unsigned val2;
        if (!m_max.find(c, val2) || val2 < val) {
            m_max.insert(c, val);
        }
    }
};

tactic * mk_eq2bv_tactic(ast_manager & m) {
    return clean(alloc(eq2bv_tactic, m));
}

