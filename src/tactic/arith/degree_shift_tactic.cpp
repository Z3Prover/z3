/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    degree_shift_tactic.cpp

Abstract:

    Simple degree shift procedure. 
    Basic idea: if goal G contains a real variable x, x occurs with degrees
    d_1, ..., d_k in G, and n = gcd(d_1, ..., d_k) > 1. 
    Then, replace x^n with a new fresh variable y.

Author:

    Leonardo de Moura (leonardo) 2011-12-30.

Revision History:

--*/
#include"tactical.h"
#include"filter_model_converter.h"
#include"extension_model_converter.h"
#include"cooperate.h"
#include"arith_decl_plugin.h"
#include"simplify_tactic.h"
#include"ast_smt2_pp.h"
#include"rewriter_def.h"

class degree_shift_tactic : public tactic {
    struct     imp {
        ast_manager &            m;
        arith_util               m_autil;
        obj_map<app, rational>   m_var2degree;
        obj_map<app, app*>       m_var2var;
        obj_map<app, proof*>     m_var2pr;
        expr_ref_vector          m_pinned;
        ptr_vector<expr>         m_todo;
        rational                 m_one;
        bool                     m_produce_models;
        bool                     m_produce_proofs;

        expr * mk_power(expr * t, rational const & k) {
            if (k.is_one())
                return t;
            else
                return m_autil.mk_power(t, m_autil.mk_numeral(k, false));
        }

        struct rw_cfg : public default_rewriter_cfg {
            imp & o;
            rw_cfg(imp & _o):o(_o) {}
            
            br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
                arith_util & u = o.m_autil;
                if (!is_decl_of(f, u.get_family_id(), OP_POWER) || !is_app(args[0]))
                    return BR_FAILED;
                ast_manager & m = o.m;
                rational g;
                app * t = to_app(args[0]);
                if (!o.m_var2degree.find(t, g))
                    return BR_FAILED;
                SASSERT(g > rational(1));
                SASSERT(g.is_int());
                rational k;
                VERIFY(u.is_numeral(args[1], k));
                SASSERT(gcd(k, g) == g);
                rational new_k = div(k, g);
                expr * new_arg = o.m_var2var.find(t);
                result = o.mk_power(new_arg, new_k);
                if (o.m_produce_proofs) {
                    proof * pr = o.m_var2pr.find(t);
                    app * fact = m.mk_eq(m.mk_app(f, num, args), result);
                    result_pr  = m.mk_th_lemma(u.get_family_id(), fact, 1, &pr);
                }
                return BR_DONE;
            }
        };

        class rw : public rewriter_tpl<rw_cfg> {
            rw_cfg m_cfg;
        public:
            rw(imp & o):
                rewriter_tpl<rw_cfg>(o.m, o.m_produce_proofs, m_cfg),
                m_cfg(o) {
            }
        };

        scoped_ptr<rw>   m_rw;

        imp(ast_manager & _m):
            m(_m),
            m_autil(_m),
            m_pinned(_m),
            m_one(1),
            m_rw(0) {
        }


        void checkpoint() {
            if (m.canceled())
                throw tactic_exception(m.limit().get_cancel_msg());
            cooperate("degree_shift");
        }

        void visit(expr * t, expr_fast_mark1 & visited) {
            if (!visited.is_marked(t)) {
                visited.mark(t);
                m_todo.push_back(t);
            }
        }

        void save_degree(expr * t, rational const & k) {
            SASSERT(k.is_int());
            if (is_uninterp_const(t) && m_autil.is_real(t)) {
                rational old_k;
                if (m_var2degree.find(to_app(t), old_k)) {
                    old_k = gcd(k, old_k);
                    m_var2degree.insert(to_app(t), old_k);
                }
                else {
                    m_var2degree.insert(to_app(t), k);
                }
            }
        }

        void visit_args(expr * t, expr_fast_mark1 & visited) {
            if (is_app(t)) {
                unsigned num_args = to_app(t)->get_num_args();
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg = to_app(t)->get_arg(i);
                    save_degree(arg, m_one);
                    visit(arg, visited);
                }
            }
        }

        void collect(expr * t, expr_fast_mark1 & visited) {
            rational k;
            visit(t, visited);
            while (!m_todo.empty()) {
                checkpoint();
                expr * t = m_todo.back();
                m_todo.pop_back();
                if (is_var(t))
                    continue;
                if (is_quantifier(t)) {
                    unsigned num_children = to_quantifier(t)->get_num_children();
                    for (unsigned i = 0; i < num_children; i ++)
                        visit(to_quantifier(t)->get_child(i), visited);
                }
                else {
                    SASSERT(is_app(t));
                    if (m_autil.is_power(t) && m_autil.is_numeral(to_app(t)->get_arg(1), k) && k.is_int() && k.is_pos()) {
                        expr * arg = to_app(t)->get_arg(0);
                        save_degree(arg, k);
                        visit_args(arg, visited);
                    }
                    else {
                        visit_args(t, visited);
                    }
                }
            }
        }

        void display_candidates(std::ostream & out) {
            out << "candidates:\n";
            obj_map<app, rational>::iterator it  = m_var2degree.begin();
            obj_map<app, rational>::iterator end = m_var2degree.end();
            for (; it != end; ++it) {
                if (!it->m_value.is_one()) {
                    out << "POWER: " << it->m_value << "\n" << mk_ismt2_pp(it->m_key, m) << "\n";
                }
            }
        }

        void collect(goal const & g) {
            m_var2degree.reset();
            expr_fast_mark1 visited;
            unsigned sz = g.size();
            for (unsigned i = 0; i < sz; i++) {
                collect(g.form(i), visited);
            }
            
            TRACE("degree_shift", display_candidates(tout););
        }

        void discard_non_candidates() {
            m_pinned.reset();
            ptr_vector<app> to_delete;
            obj_map<app, rational>::iterator it  = m_var2degree.begin();
            obj_map<app, rational>::iterator end = m_var2degree.end();
            for (; it != end; ++it) {
                if (it->m_value.is_one())
                    to_delete.push_back(it->m_key);
                else
                    m_pinned.push_back(it->m_key); // make sure it is not deleted during simplifications
            }
            ptr_vector<app>::iterator it2  = to_delete.begin();
            ptr_vector<app>::iterator end2 = to_delete.end();
            for (; it2 != end2; ++it2) 
                m_var2degree.erase(*it2);
        }

        void prepare_substitution(model_converter_ref & mc) {
            SASSERT(!m_var2degree.empty());
            filter_model_converter * fmc = 0;
            extension_model_converter * xmc = 0;
            if (m_produce_models) {
                fmc = alloc(filter_model_converter, m);
                xmc = alloc(extension_model_converter, m);
                mc = concat(fmc, xmc);
            }
            obj_map<app, rational>::iterator it  = m_var2degree.begin();
            obj_map<app, rational>::iterator end = m_var2degree.end();
            for (; it != end; ++it) {
                SASSERT(it->m_value.is_int());
                SASSERT(it->m_value >= rational(2));
                app * fresh = m.mk_fresh_const(0, it->m_key->get_decl()->get_range());
                m_pinned.push_back(fresh);
                m_var2var.insert(it->m_key, fresh);
                if (m_produce_models) {
                    fmc->insert(fresh->get_decl());
                    xmc->insert(it->m_key->get_decl(), mk_power(fresh, rational(1)/it->m_value));
                }
                if (m_produce_proofs) {
                    expr * s  = mk_power(it->m_key, it->m_value);
                    expr * eq = m.mk_eq(fresh, s);
                    proof * pr1 = m.mk_def_intro(eq);
                    proof * result_pr = m.mk_apply_def(fresh, s, pr1);
                    m_pinned.push_back(result_pr);
                    m_var2pr.insert(it->m_key, result_pr);
                }
            }
        }

        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            m_produce_proofs = g->proofs_enabled();
            m_produce_models = g->models_enabled();
            tactic_report report("degree_shift", *g);
            collect(*g);
            discard_non_candidates();
            if (!m_var2degree.empty()) {
                prepare_substitution(mc);
                m_rw = alloc(rw, *this);
                
                // substitute
                expr_ref  new_curr(m);
                proof_ref new_pr(m);
                unsigned   size = g->size();
                for (unsigned idx = 0; idx < size; idx++) {
                    checkpoint();
                    expr * curr = g->form(idx);
                    (*m_rw)(curr, new_curr, new_pr);
                    if (m_produce_proofs) {
                        proof * pr = g->pr(idx);
                        new_pr     = m.mk_modus_ponens(pr, new_pr);
                    }
                    g->update(idx, new_curr, new_pr, g->dep(idx));
                }

                // add >= 0 constraints for variables with even degree
                obj_map<app, rational>::iterator it  = m_var2degree.begin();
                obj_map<app, rational>::iterator end = m_var2degree.end();
                for (; it != end; ++it) {
                    SASSERT(it->m_value.is_int());
                    SASSERT(it->m_value >= rational(2));
                    if (it->m_value.is_even()) {
                        app * new_var  = m_var2var.find(it->m_key);
                        app * new_c    = m_autil.mk_ge(new_var, m_autil.mk_numeral(rational(0), false));
                        proof * new_pr = 0;
                        if (m_produce_proofs) {
                            proof * pr = m_var2pr.find(it->m_key);
                            new_pr     = m.mk_th_lemma(m_autil.get_family_id(), new_c, 1, &pr);
                        }
                        g->assert_expr(new_c, new_pr, 0);
                    }
                }
            }
            g->inc_depth();
            result.push_back(g.get());
            TRACE("degree_shift", g->display(tout); if (mc) mc->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };
    
    imp *      m_imp;
public:
    degree_shift_tactic(ast_manager & m) {
        m_imp = alloc(imp, m);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(degree_shift_tactic, m);
    }
        
    virtual ~degree_shift_tactic() {
        dealloc(m_imp);
    }

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
    }
    
    virtual void cleanup() {
        imp * d = alloc(imp, m_imp->m);
        std::swap(d, m_imp);        
        dealloc(d);
    }

};

tactic * mk_degree_shift_tactic(ast_manager & m, params_ref const & p) {
    params_ref mul2power_p;
    mul2power_p.set_bool("mul_to_power", true);
    return and_then(using_params(mk_simplify_tactic(m), mul2power_p),
                    clean(alloc(degree_shift_tactic, m)));
}

