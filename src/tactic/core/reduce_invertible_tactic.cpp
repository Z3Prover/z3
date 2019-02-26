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
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/rewriter_def.h"
#include "tactic/tactic.h"
#include "tactic/core/reduce_invertible_tactic.h"
#include "tactic/core/collect_occs.h"
#include "tactic/generic_model_converter.h"
#include <cstdint>

namespace {
class reduce_invertible_tactic : public tactic {
    ast_manager& m;
    bv_util      m_bv;
    arith_util   m_arith;

public:
    reduce_invertible_tactic(ast_manager & m):
        m(m),
        m_bv(m),
        m_arith(m)
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
        expr_ref new_v(m);
        expr * p;
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
            if (f == f_new) continue;
            proof_ref new_pr(m);
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

    // store one parent of expression, or null if multiple
    struct parents {
        parents(): m_p(0) {}
        uintptr_t m_p;

        void set(expr * e) {
            SASSERT((uintptr_t)e != 1);
            if (!m_p) m_p = (uintptr_t)e;
            else m_p = 1;
        }

        expr * get() const {
          return m_p == 1 ? nullptr : (expr*)m_p;
        }
    };
    svector<parents> m_parents;
    struct parent_collector {
        reduce_invertible_tactic& c;
        parent_collector(reduce_invertible_tactic& c):c(c) {}
        void operator()(app* n) {
            for (expr* arg : *n) {
                c.m_parents.reserve(arg->get_id() + 1);
                c.m_parents[arg->get_id()].set(n);
            }
        }

        void operator()(var* v) {
            c.m_parents.reserve(v->get_id() + 1);
        }

        void operator()(quantifier* q) {}
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

    bool is_full_domain_var(expr* v, rational& model) {
        auto f = is_app(v) ? to_app(v)->get_decl() : nullptr;
        if (!f || f->get_family_id() != m_bv.get_family_id() || f->get_arity() == 0)
            return false;

        switch (f->get_decl_kind()) {
        case OP_BADD:
        case OP_BSUB:
        case OP_BSHL:
        case OP_BASHR:
        case OP_BLSHR:
        case OP_BOR:
            model = rational::zero();
            return true;

        case OP_BAND:
            model = rational::power_of_two(m_bv.get_bv_size(v)) - rational::one();
            return true;

        case OP_BMUL:
        case OP_BSDIV:
        case OP_BSDIV0:
        case OP_BSDIV_I:
        case OP_BUDIV:
        case OP_BUDIV0:
        case OP_BUDIV_I:
            model = rational::one();
            return true;

        default:
            return false;
        }
    }

    bool rewrite_unconstr(expr* v, expr_ref& new_v, generic_model_converter_ref* mc, unsigned max_var) {
        rational mdl;
        if (!is_full_domain_var(v, mdl))
            return false;

        rational r;
        app* a = to_app(v);
        expr* fst_arg = a->get_arg(0);
        bool fst_is_var = is_var(fst_arg);

        for (unsigned i = 0, n = a->get_num_args(); i != n; ++i) {
            auto arg = a->get_arg(i);
            if (!m_parents[arg->get_id()].get() || is_var(arg) != fst_is_var)
                return false;

            if (fst_is_var && to_var(arg)->get_idx() >= max_var)
                return false;

            if (m_bv.is_numeral(arg, r) && r != mdl)
                return false;
        }

        if (mc) {
            ensure_mc(mc);
            expr_ref num(m_bv.mk_numeral(mdl, get_sort(fst_arg)), m);
            for (unsigned i = 1, n = a->get_num_args(); i != n; ++i) {
                (*mc)->add(a->get_arg(i), num);
            }
        }
        new_v = fst_arg;
        return true;
    }

    // TBD: could be made to be recursive, by walking multiple layers of parents.
    
    bool is_invertible(expr* v, expr*& p, expr_ref& new_v, generic_model_converter_ref* mc, unsigned max_var = 0) {
        p = m_parents[v->get_id()].get();
        if (!p) return false;
        if (m_inverted.is_marked(p)) return false;
        if (mc && !is_ground(p)) return false;

        if (m_bv.is_bv_xor(p) ||
            m_bv.is_bv_not(p) ||
            m_bv.is_bv_neg(p)) {
            if (mc) {
                ensure_mc(mc);
                (*mc)->add(v, p);
            }
            new_v = v;
            return true;
        }

        if (rewrite_unconstr(p, new_v, mc, max_var))
            return true;

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
                if (arg != v) { 
                    if (rest) 
                        rest = m_bv.mk_bv_mul(rest, arg);
                    else
                        rest = arg;
                }
            }
            if (!rest) return false;

            // create case split on
            // divisbility of 2
            // v * t -> 
            // if t = 0, set v' := 0 and the solution for v is 0.
            // otherwise,
            // let i be the position of the least bit of t set to 1
            // then extract[sz-1:i](v) ++ zero[i-1:0] is the invertible of v * t
            // thus
            //    extract[i+1:0](t) = 1 ++ zero[i-1:0] -> extract[sz-1:i](v) ++ zero[i-1:0]
            // to reproduce the original v from t
            // solve for v*t = extract[sz-1:i](v') ++ zero[i-1:0]
            // using values for t and v'
            // thus
            //
            //    udiv(extract[sz-1:i](v') ++ zero[i-1:0], t)
            // 
            // TBD: this argument is flawed. Unit test breaks with either
            // the above or udiv(v, t)

            unsigned sz = m_bv.get_bv_size(p);
            expr_ref bit1(m_bv.mk_numeral(1, 1), m);
            new_v = m_bv.mk_numeral(0, sz);
            for (unsigned i = sz; i-- > 0; ) {
                expr_ref extr_i(m_bv.mk_extract(i, i, rest), m);
                expr_ref cond(m.mk_eq(extr_i, bit1), m);
                expr_ref part(v, m);
                if (i > 0) {
                    part = m_bv.mk_concat(m_bv.mk_extract(sz-1, i, v), m_bv.mk_numeral(0, i));
                }
                new_v = m.mk_ite(cond, part, new_v);
            }
            if (mc) {
                ensure_mc(mc);
                expr_ref div(m), def(m);
                div = m.mk_app(m_bv.get_fid(), OP_BUDIV_I, v, rest);
                def = m_bv.mk_numeral(0, sz);
                def = m.mk_ite(m.mk_eq(def, rest), def, div);
                (*mc)->add(v, def);
                TRACE("invertible_tactic", tout << def << "\n";);
            }
            return true;
        }
        if (m_bv.is_bv_sub(p)) {
            // TBD
        }
        if (m_bv.is_bv_udivi(p)) {
            // TBD
        }
        // sdivi, sremi, uremi, smodi
        // TBD

        if (m_arith.is_mul(p) && m_arith.is_real(p)) {
            expr_ref rest(m);
            for (expr* arg : *to_app(p)) {
                if (arg != v) {
                    if (rest) 
                        rest = m_arith.mk_mul(rest, arg);
                    else
                        rest = arg;
                }
            }
            if (!rest) return false;
            expr_ref zero(m_arith.mk_real(0), m);
            new_v = m.mk_ite(m.mk_eq(zero, rest), zero, v);
            if (mc) {
                ensure_mc(mc);
                expr_ref def(m_arith.mk_div(v, rest), m);
                (*mc)->add(v, def);
            }
            return true;        
        }


        expr* e1 = nullptr, *e2 = nullptr;

        // t / v -> if t = 0 then 0 else v 
        // inverse: t = 0 then 1 else v / t
        if (m_arith.is_div(p, e1, e2) && e2 == v) {
            expr_ref zero(m_arith.mk_real(0), m);
            new_v = m.mk_ite(m.mk_eq(zero, e1), zero, v);
            if (mc) {
                ensure_mc(mc);
                expr_ref def(m.mk_ite(m.mk_eq(zero, e1), m_arith.mk_real(1), m_arith.mk_div(e1, v)), m);
                (*mc)->add(v, def);
            }
            return true;
        }
        
        // v / t unless t != 0
        if (m_arith.is_div(p, e1, e2) && e1 == v) {
            return false;
        }
       
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
            m.is_bool(e) ||
            m_arith.is_int_real(e);
    }

    expr * mk_diagonal(expr* e) {
        if (m_bv.is_bv(e)) return m_bv.mk_bv_neg(e);
        if (m.is_bool(e)) return m.mk_not(e);
        if (m_arith.is_int(e)) return m_arith.mk_add(m_arith.mk_int(1), e);
        if (m_arith.is_real(e)) return m_arith.mk_add(m_arith.mk_real(1), e);
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
            // ensure they are in unique location and not under other quantifiers.
            // if they are invertible, then produce inverting expression.
            //
            expr_safe_replace sub(m);
            t.m_parents.reset();
            t.m_inverted.reset();
            expr_ref new_v(m);
            expr * p;
            
            {
                parent_collector proc(t);           
                expr_fast_mark1 visited;
                quick_for_each_expr(proc, visited, new_body);
            }
            bool has_new_var = false;
            for (unsigned i = 0; i < vars.size(); ++i) {
                var* v = vars[i];
                if (!occurs_under_nested_q(v, new_body) && t.is_invertible(v, p, new_v, nullptr, vars.size())) {
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
}

tactic * mk_reduce_invertible_tactic(ast_manager & m, params_ref const &) {
    return alloc(reduce_invertible_tactic, m);
}
