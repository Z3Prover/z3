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
#include "tactic/tactical.h"
#include "tactic/arith/bound_manager.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_util.h"
#include "ast/ast_pp_util.h"

class eq2bv_tactic : public tactic {
    struct eq_rewriter_cfg : public default_rewriter_cfg {
        ast_manager&     m;
        eq2bv_tactic&    t;

        bool is_fd(expr* x, expr* y, expr_ref& result) {
            expr* z;
            rational r;
            if (t.m_fd.find(x, z) && t.a.is_numeral(y, r)) {
                result = m.mk_eq(z, t.bv.mk_numeral(r, z->get_sort()));
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
            result_pr = nullptr;
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
        func_decl_ref_vector m_vars;
        vector<rational> m_values;
    public:
        bvmc(ast_manager& m): m_vars(m) {}
        
        void insert(func_decl* c_new, func_decl* c_old) {
            m_map.insert(c_new, c_old);
        }

        void insert(func_decl* var, rational const& val) { 
            m_vars.push_back(var);
            m_values.push_back(val);
        }

        void operator()(model_ref& mdl) override {
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
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                func_decl* f = m_vars.get(i);
                new_m->register_decl(f, a.mk_numeral(m_values[i], f->get_range()));
            }
            mdl = new_m;
        }
        
        model_converter* translate(ast_translation & translator) override {
            bvmc* v = alloc(bvmc, translator.to());
            for (auto const& kv : m_map) {
                v->m_map.insert(translator(kv.m_key), translator(kv.m_value));
            }
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                v->insert(translator(m_vars.get(i)), m_values[i]);
            }
            return v;
        }

        void display(std::ostream & out) override {
            ast_manager& m = m_vars.get_manager();
            for (auto const& kv : m_map) {
                out << "(model-set " << kv.m_key->get_name() << " " << kv.m_value->get_name() << ")\n";
            }
            for (unsigned i = 0; i < m_vars.size(); ++i) {
                func_decl* v = m_vars.get(i);
                out << "(model-add " << v->get_name() << " () " << mk_pp(v->get_range(), m) << " " << m_values[i] << ")\n";
            }
        }

        void get_units(obj_map<expr, bool>& units) override { units.reset(); }

    };

public:
    ast_manager &                    m;
    arith_util                       a;
    bv_util                          bv;
    eq_rewriter                      m_rw;
    expr_ref_vector                  m_trail;
    bound_manager                    m_bounds;
    obj_map<expr, expr*>             m_fd;
    obj_map<expr, rational>          m_max;
    expr_mark                        m_nonfd;
    expr_mark                        m_has_eq;
    ptr_vector<expr>                 m_todo;
        
    eq2bv_tactic(ast_manager & _m):
        m(_m),
        a(m),
        bv(m),
        m_rw(*this),
        m_trail(m),
        m_bounds(m) {
    }

    ~eq2bv_tactic() override {
    }
        
        
    void updt_params(params_ref const & p) override {
    }
    
    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        m_trail.reset();
        m_fd.reset();
        m_max.reset();
        m_nonfd.reset();
        m_has_eq.reset();
        m_bounds.reset();
        ref<bvmc> mc1 = alloc(bvmc, m);

        tactic_report report("eq2bv", *g);

        m_bounds(*g);

        if (m_bounds.inconsistent() || g->proofs_enabled()) {
            g->inc_depth();
            result.push_back(g.get());
            return;
        }
        
        for (unsigned i = 0; i < g->size(); i++) {            
            collect_fd(g->form(i));
        }
        cleanup_fd(mc1);
        
        if (m_max.empty()) {
            result.push_back(g.get());
            return;
        }

        for (unsigned i = 0; !g->inconsistent() && i < g->size(); i++) {            
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);  
            app_ref var(m);
            if (is_bound(g->form(i), var) && !m_has_eq.is_marked(var)) {
                if (m.proofs_enabled()) {
                    new_pr = m.mk_rewrite(g->form(i), m.mk_true());
                    new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
                }
                bool strict = true;
                rational v;
                bool has_val = 
                    (m_bounds.has_upper(var, v, strict) && !strict && v.is_unsigned()) ||
                    (m_bounds.has_lower(var, v, strict) && !strict && v.is_unsigned());

                if (has_val) {
                    mc1->insert(to_app(var)->get_decl(), v);
                    g->update(i, m.mk_true(), new_pr, nullptr);
                    continue;
                }
            }
            if (is_bound(g->form(i), var) && m_max.contains(var)) {
                new_curr = m.mk_true();
                if (m.proofs_enabled()) {
                    new_pr = m.mk_rewrite(g->form(i), new_curr);
                    new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
                }
                g->update(i, new_curr, new_pr);
                continue;
            }
            m_rw(g->form(i), new_curr, new_pr);

            if (g->form(i) == new_curr)
                continue;
            if (m.proofs_enabled()) {
                if (!new_pr) new_pr = m.mk_rewrite(g->form(i), new_curr);
                new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
            }
            g->update(i, new_curr, new_pr, g->dep(i));
        }
        for (auto & kv : m_max) {
            expr* c = kv.m_key;
            bool strict;
            rational r;
            expr_ref fml(m);
            if (m_bounds.has_lower(c, r, strict) && !r.is_neg()) {
                SASSERT(!strict);
                expr* d = m_fd.find(c);
                fml = bv.mk_ule(bv.mk_numeral(r, d->get_sort()), d);
                g->assert_expr(fml, m_bounds.lower_dep(c));
            }
            if (m_bounds.has_upper(c, r, strict) && !r.is_neg()) {
                SASSERT(!strict);
                expr* d = m_fd.find(c);
                fml = bv.mk_ule(d, bv.mk_numeral(r, d->get_sort()));
                g->assert_expr(fml, m_bounds.upper_dep(c));
            }
        }        
        g->inc_depth();
        g->add(mc1.get());
        result.push_back(g.get());
    }


    tactic * translate(ast_manager & m) override {
        return alloc(eq2bv_tactic, m);
    }
        
    void collect_param_descrs(param_descrs & r) override {
    }
        
    void cleanup() override {
    }

    void cleanup_fd(ref<bvmc>& mc) {
        SASSERT(m_fd.empty());
        ptr_vector<expr> rm;
        for (auto& kv : m_max) 
            if (m_nonfd.is_marked(kv.m_key))
                rm.push_back(kv.m_key);
        
        for (expr* r : rm)
            m_max.erase(r);

        for (auto& kv : m_max) {
            expr* key = kv.m_key;
            rational& value = kv.m_value;

            // ensure there are enough elements.
            bool strict;
            rational bound;            
            
            if (m_bounds.has_upper(key, bound, strict))
                value = std::max(value, bound);            
            else 
                ++value;
            
            if (m_bounds.has_lower(key, bound, strict))               
                value = std::max(value, bound);
            
            ++value;

            unsigned p = value.get_num_bits();      
            if (p <= 1) p = 2;
            app* z = m.mk_fresh_const("z", bv.mk_sort(p));
            m_trail.push_back(z);
            m_fd.insert(key, z);
            mc->insert(z->get_decl(), to_app(key)->get_decl());
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

    bool is_upper(expr* f, unsigned& k, app_ref& var) {
        expr* e1, *e2;
        if ((a.is_le(f, e1, e2) || a.is_ge(f, e2, e1)) && is_var_const_pair(e1, e2, k)) {
            SASSERT(m_bounds.has_upper(e1));
            var = to_app(e1);
            return true;
        } 
        return false;
    }

    bool is_lower(expr* f, unsigned& k, app_ref& var) {
        expr* e1, *e2;
        if ((a.is_le(f, e1, e2) || a.is_ge(f, e2, e1)) && is_var_const_pair(e2, e1, k)) {
            SASSERT(m_bounds.has_lower(e2));
            var = to_app(e2);
            return true;
        } 
        return false;
    }


    bool is_bound(expr* f, app_ref& var) {
        unsigned k;
        return is_lower(f, k, var) || is_upper(f, k, var);
    }

    void mark_has_eq(expr* e) {
        if (is_uninterp_const(e)) {
            m_has_eq.mark(e, true);
        }
    }

    void collect_fd(expr* f) {
        m_trail.push_back(f);
        app_ref var(m);
        if (is_bound(f, var)) {
            return;
        }
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
                mark_has_eq(e1);
                mark_has_eq(e2);
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
        rational r;
        if (is_uninterp_const(v) && a.is_numeral(c, r) && !m_nonfd.is_marked(v) && a.is_int(v) && r.is_unsigned()) {
            add_fd(v, r);
            return true;
        }
        return false;
    }

    void add_fd(expr* c, rational val) {
        rational val2;
        if (!m_max.find(c, val2) || val2 < val) {
            m_max.insert(c, val);
        }
    }
};

tactic * mk_eq2bv_tactic(ast_manager & m) {
    return clean(alloc(eq2bv_tactic, m));
}

