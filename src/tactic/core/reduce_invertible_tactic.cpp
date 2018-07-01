/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    reduce_invertible_tactic.cpp

Abstract:

    Reduce invertible variables.

Author:

    Nuno Lopes (nlopes)         2018-6-30
    Nikolaj Bjorner (nbjorner)

Notes:

 1. Walk through top-level uninterpreted constants.

--*/

#include "util/cooperate.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/rewriter_def.h"
#include "tactic/tactic.h"
#include "tactic/core/reduce_invertible_tactic.h"
#include "tactic/core/collect_occs.h"
#include "tactic/generic_model_converter.h"

class reduce_invertible_tactic : public tactic {
    ast_manager& m;
    bv_util      m_bv;

public:
    reduce_invertible_tactic(ast_manager & m):
        m(m),
        m_bv(m)
    {}

    ~reduce_invertible_tactic() override { }

    tactic * translate(ast_manager & m) override {
        return alloc(reduce_invertible_tactic, m);
    }
    
    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        TRACE("reduce_invertible", g->display(tout););
        tactic_report report("reduce-invertible", *g);
        m_inverted.reset();
        m_parents.reset();
        collect_parents(g);
        collect_occs occs;
        obj_hashtable<expr> vars;
        generic_model_converter_ref mc;
        occs(*g, vars);
        expr_safe_replace sub(m);
        expr_ref p(m), new_v(m);
        for (expr* v : vars) {
            if (is_invertible(v, p, new_v, &mc)) {
                mark_inverted(p);
                sub.insert(p, new_v);
            }
        }
        reduce_q_rw rw(*this);
        unsigned sz = g->size();
        for (unsigned idx = 0; idx < sz; idx++) {
            checkpoint();
            expr* f = g->form(idx);
            expr_ref f_new(m);
            sub(f, f_new);
            rw(f_new, f_new);
            proof_ref new_pr(m);
            if (f == f_new) continue;
            if (g->proofs_enabled()) {
                proof * pr = g->pr(idx);
                new_pr     = m.mk_modus_ponens(pr, new_pr);
            }
            g->update(idx, f_new, new_pr, g->dep(idx));
        }  
        if (mc) g->add(mc.get());
        result.push_back(g.get());
        g->inc_depth();        
    }

    void cleanup() override {}

private:


    void checkpoint() { 
        if (m.canceled())
            throw tactic_exception(m.limit().get_cancel_msg());
        cooperate("reduce-invertible");
    }

    expr_mark        m_inverted;
    void mark_inverted(expr *p) {
        ptr_buffer<expr> todo;
        todo.push_back(p);
        while (!todo.empty()) {
            p = todo.back();
            todo.pop_back();
            if (!m_inverted.is_marked(p)) {
                m_inverted.mark(p, true);
                if (is_app(p)) {
                    for (expr* arg : *to_app(p)) {
                        todo.push_back(arg);
                    }
                }
                else if (is_quantifier(p)) {
                    todo.push_back(to_quantifier(p)->get_expr());
                }
            }
        }
    }

    // store up to two parents of expression.
    struct parents {
        parents(): m_p1(nullptr), m_p2(nullptr) {}
        expr* m_p1;
        expr* m_p2;
    };
    svector<parents> m_parents;
    struct parent_collector {
        reduce_invertible_tactic& c;
        parent_collector(reduce_invertible_tactic& c):c(c) {}
        void operator()(app* n) {
            for (expr* arg : *n) {
                c.m_parents.reserve(arg->get_id() + 1, parents());
                parents& p = c.m_parents[arg->get_id()];
                if (!p.m_p1) p.m_p1 = n; else p.m_p2 = n;
            }
        }
        void operator()(expr*) {}
    };

    void collect_parents(goal_ref const& g) {
        parent_collector proc(*this);
        expr_fast_mark1 visited;
        unsigned sz = g->size();
        for (unsigned i = 0; i < sz; i++) {
            checkpoint();
            quick_for_each_expr(proc, visited, g->form(i));
        }        
    }    

    void ensure_mc(generic_model_converter_ref* mc) {
        if (mc && !(*mc)) *mc = alloc(generic_model_converter, m, "reduce-invertible");        
    }

    // TBD: could be made to be recursive, by walking multiple layers of parents.
    
    bool is_invertible(expr* v, expr_ref& p, expr_ref& new_v, generic_model_converter_ref* mc) {
        p = m_parents[v->get_id()].m_p1;
        if (m_parents[v->get_id()].m_p2 || !p) return false;
        if (m_inverted.is_marked(p)) return false;
        if (mc && !is_ground(p)) return false;
        if (m_bv.is_bv_add(p)) {
            if (mc) {
                ensure_mc(mc);
                // if we solve for v' := v + t
                // then the value for v is v' - t
                expr_ref def(v, m);
                for (expr* arg : *to_app(p)) {
                    if (arg != v) def = m_bv.mk_bv_sub(def, arg);
                }
                (*mc)->add(v, def);
            }
            new_v = v;
            return true;
        }
        if (m_bv.is_bv_mul(p)) {
            expr_ref rest(m);
            for (expr* arg : *to_app(p)) {
                if (arg != v) 
                    if (rest) 
                        rest = m_bv.mk_bv_mul(rest, arg);
                    else
                        rest = arg;
            }
            if (!rest) return false;

            // create case split on
            // divisbility of 2
            // v * t -> 
            // def for v:
            //   if t is odd -> v / t
            //   if t/2 is odd -> 2*(v/t)
            //   if t/4 is odd -> 4*(v/t)
            // .. if t = 0 -> 0

            unsigned sz = m_bv.get_bv_size(p);
            expr_ref bit1(m_bv.mk_numeral(1, 1), m);
            new_v = m_bv.mk_numeral(0, sz);
            expr_ref div(m), def(m);
            if (mc) {
                ensure_mc(mc);
                div = m.mk_app(m_bv.get_fid(), OP_BUDIV_I, v, rest);
                def = new_v;
            }
            for (unsigned i = sz; i-- > 0; ) {
                expr_ref extr_i(m_bv.mk_extract(i, i, rest), m);
                expr_ref cond(m.mk_eq(extr_i, bit1), m);
                expr_ref part(v, m);
                if (i > 0) {
                    part = m_bv.mk_concat(m_bv.mk_extract(sz-1, i, v), m_bv.mk_numeral(0, i));
                }
                new_v = m.mk_ite(cond, part, new_v);
                if (def) {
                    expr_ref shl = div;
                    if (i > 0) shl = m_bv.mk_bv_shl(div, m_bv.mk_numeral(i, sz));
                    def = m.mk_ite(cond, shl, def);
                }
            }
            if (def) {
                (*mc)->add(v, def);
            }
            return true;
        }
        if (m_bv.is_bv_xor(p)) {
            if (mc) {
                ensure_mc(mc);
                (*mc)->add(v, p);
            }
            new_v = v;
            return true;
        }
        if (m_bv.is_bv_sub(p)) {
            // TBD
        }
        if (m_bv.is_bv_neg(p)) {
            // TBD
        }
        if (m_bv.is_bv_udivi(p)) {
            // TBD
        }
        // sdivi, sremi, uremi, smodi
        // TBD


        expr* e1 = nullptr, *e2 = nullptr;
        if (m.is_eq(p, e1, e2)) {
            if (mc && has_diagonal(e1)) {
                ensure_mc(mc);
                new_v = m.mk_fresh_const("eq", m.mk_bool_sort());
                SASSERT(v == e1 || v == e2);
                expr* other = (v == e1) ? e2 : e1;
                (*mc)->hide(new_v);
                (*mc)->add(v, m.mk_ite(new_v, other, mk_diagonal(other)));
                return true;
            }
            else if (mc) {
                // diagonal functions for other types depend on theory.
                return false;
            }
            else if (is_var(v) && is_non_singleton_sort(m.get_sort(v))) {
                new_v = m.mk_var(to_var(v)->get_idx(), m.mk_bool_sort());                
                return true;
            }
        }
        return false;
    }

    bool has_diagonal(expr* e) {
        return 
            m_bv.is_bv(e) || 
            m.is_bool(e);
    }

    expr * mk_diagonal(expr* e) {
        if (m_bv.is_bv(e)) return m_bv.mk_bv_neg(e);
        if (m.is_bool(e)) return m.mk_not(e);
        UNREACHABLE();
        return e;
    }

    bool is_non_singleton_sort(sort* s) {
        if (m.is_uninterp(s)) return false;
        sort_size sz = s->get_num_elements();
        if (sz.is_finite() && sz.size() == 1) return false;
        return true;
    }

    struct reduce_q_rw_cfg : public default_rewriter_cfg {
        ast_manager&              m;
        reduce_invertible_tactic& t;

        reduce_q_rw_cfg(reduce_invertible_tactic& t): m(t.m), t(t) {}
        
        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            if (is_lambda(old_q)) return false;
            if (has_quantifiers(new_body)) return false;
            ref_buffer<var, ast_manager> vars(m);
            ptr_buffer<sort> new_sorts;
            unsigned n = old_q->get_num_decls();
            for (unsigned i = 0; i < n; ++i) {
                sort* srt = old_q->get_decl_sort(i);
                vars.push_back(m.mk_var(n - i - 1, srt));
                new_sorts.push_back(srt);
            }
            // for each variable, collect parents,
            // ensure they are in uniqe location and not under other quantifiers.
            // if they are invertible, then produce inverting expression.
            //
            expr_safe_replace sub(m);
            t.m_parents.reset();
            t.m_inverted.reset();
            expr_ref p(m), new_v(m);
            
            {
                parent_collector proc(t);           
                expr_fast_mark1 visited;
                quick_for_each_expr(proc, visited, new_body);
            }
            bool has_new_var = false;
            for (unsigned i = 0; i < vars.size(); ++i) {
                var* v = vars[i];
                if (!occurs_under_nested_q(v, new_body) && t.is_invertible(v, p, new_v, nullptr)) {
                    t.mark_inverted(p);
                    sub.insert(p, new_v);
                    new_sorts[i] = m.get_sort(new_v);
                    has_new_var |= new_v != v;
                }
            }
            if (has_new_var) {
                sub(new_body, result);
                result = m.mk_quantifier(old_q->get_kind(), new_sorts.size(), new_sorts.c_ptr(), old_q->get_decl_names(), result);
                result_pr = nullptr;
                return true;
            }
            if (!sub.empty()) {
                sub(new_body, result);
                result = m.update_quantifier(old_q,  old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, result);
                result_pr = nullptr;
                return true;
            }
            return false;
        }

        bool occurs_under_nested_q(var* v, expr* body) {
            return has_quantifiers(body);
        }
    };

    struct reduce_q_rw : rewriter_tpl<reduce_q_rw_cfg> {
        reduce_q_rw_cfg m_cfg;
    public:
        reduce_q_rw(reduce_invertible_tactic& t):
            rewriter_tpl<reduce_q_rw_cfg>(t.m, false, m_cfg),
            m_cfg(t) {}
    };


};

tactic * mk_reduce_invertible_tactic(ast_manager & m, params_ref const &) {
    return alloc(reduce_invertible_tactic, m);
}

