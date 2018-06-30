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
        collect_parents(g);
        collect_occs occs;
        obj_hashtable<expr> vars;
        generic_model_converter_ref mc;
        //occs(*g, vars);
        expr_safe_replace sub(m);
        expr_ref p(m);
        for (expr* v : vars) {
            if (is_invertible(v, p, &mc)) {
                sub.insert(v, p);
            }
        }
        if (sub.empty()) {
            result.push_back(g.get());
            return;
        }
        unsigned sz = g->size();
        for (unsigned idx = 0; idx < sz; idx++) {
            checkpoint();
            expr* f = g->form(idx);
            expr_ref f_new(m);
            sub(f, f_new);
            proof_ref new_pr(m);
            if (f == f_new) continue;
            if (g->proofs_enabled()) {
                proof * pr = g->pr(idx);
                new_pr     = m.mk_modus_ponens(pr, new_pr);
            }
            g->update(idx, f_new, new_pr, g->dep(idx));
        }        
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
                c.m_parents.reserve(n->get_id() + 1, parents());
                parents& p = c.m_parents[n->get_id()];
                if (!p.m_p1) p.m_p1 = n; else p.m_p2 = n;
            }
        }
        void operator()(expr*) {}
    };

    void collect_parents(goal_ref const& g) {
        m_parents.reset();
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
    
    bool is_invertible(expr* v, expr_ref& new_v, generic_model_converter_ref* mc) {
        expr* p1 = m_parents[v->get_id()].m_p1;
        if (m_parents[v->get_id()].m_p2 || !p1) return false;

        if (m_bv.is_bv_add(p1)) {
            if (mc) {
                ensure_mc(mc);
                // if we solve for v' := v + t
                // then the value for v is v' - t
                expr_ref def(v, m);
                for (expr* arg : *to_app(p1)) {
                    if (arg != v) def = m_bv.mk_bv_sub(def, arg);
                }
                (*mc)->add(v, def);
            }
            new_v = v;
            return true;
        }
        if (m_bv.is_bv_mul(p1)) {
            // if multiplier by odd number, then just return division.
            // if general multiplier, then create case split on
            // divisbility of 2
            // v * t -> if (t & 0x1) v / t (if (!(t & 0x1) && (t & 0x3)) ..
        }
        if (m_bv.is_bv_xor(p1)) {
            
        }
        return false;
    }

    struct reduce_q_cfg : public default_rewriter_cfg {
        ast_manager&              m;
        reduce_invertible_tactic& t;

        reduce_q_cfg(reduce_invertible_tactic& t): m(t.m), t(t) {}
        
        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            ref_buffer<var, ast_manager> vars(m);
            unsigned n = old_q->get_num_decls();
            for (unsigned i = 0; i < n; ++i) {
                vars.push_back(m.mk_var(n - i - 1, old_q->get_decl_sort(i)));
            }
            // for each variable, collect parents,
            // ensure they are in uniqe location and not under other quantifiers.
            // if they are invertible, then produce inverting expression.
            //
            expr_safe_replace sub(m);
            {
                t.m_parents.reset();
                expr_ref p(m);
                parent_collector proc(t);           
                expr_fast_mark1 visited;
                quick_for_each_expr(proc, visited, new_body);
                for (var* v : vars) {
                    if (!occurs_under_nested_q(v, new_body) && t.is_invertible(v, p, nullptr)) {
                        sub.insert(v, p);
                    }
                }
            }
            if (!sub.empty()) {
                sub(new_body, result);
                result_pr = nullptr;
                return true;
            }
            return false;
        }

        bool occurs_under_nested_q(var* v, expr* body) {
            return !has_quantifiers(body);
        }
    };

};

tactic * mk_reduce_invertible_tactic(ast_manager & m, params_ref const &) {
    return alloc(reduce_invertible_tactic, m);
}

