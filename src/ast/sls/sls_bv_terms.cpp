/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls_terms.cpp

Abstract:

    normalize bit-vector expressions to use only binary operators.

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/

#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/sls/sls_bv_terms.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/bv_rewriter.h"

namespace sls {

    bv_terms::bv_terms(sls::context& ctx):
        m(ctx.get_manager()), 
        bv(m),
        m_axioms(m) {}

    void bv_terms::register_term(expr* e) {
        auto r = ensure_binary(e);
        if (r != e) {
            bool_rewriter br(m);
            m_axioms.push_back(br.mk_eq_rw(e, r));
        }
    }

    expr_ref bv_terms::ensure_binary(expr* e) {
        expr* x, * y;
        expr_ref r(m);
        if (false && (bv.is_bv_sdiv(e, x, y) || bv.is_bv_sdiv0(e, x, y) || bv.is_bv_sdivi(e, x, y)))
            r = mk_sdiv(x, y);
        else if (bv.is_bv_smod(e, x, y) || bv.is_bv_smod0(e, x, y) || bv.is_bv_smodi(e, x, y))
            r = mk_smod(x, y);
        else if (bv.is_bv_srem(e, x, y) || bv.is_bv_srem0(e, x, y) || bv.is_bv_sremi(e, x, y)) 
            r = mk_srem(x, y);        
        else
            r = e;                   
        return r;
    }

    expr_ref bv_terms::mk_sdiv(expr* x, expr* y) {
        // d = udiv(abs(x), abs(y))
        // y = 0, x >= 0 -> -1
        // y = 0, x < 0 -> 1
        // x = 0, y != 0 -> 0
        // x > 0, y < 0 -> -d
        // x < 0, y > 0 -> -d
        // x > 0, y > 0 -> d
        // x < 0, y < 0 -> d
        bool_rewriter br(m);
        bv_rewriter bvr(m);
        unsigned sz = bv.get_bv_size(x);
        rational N = rational::power_of_two(sz);
        expr_ref z(bv.mk_zero(sz), m);
        expr_ref o(bv.mk_one(sz), m);
        expr_ref n1(bv.mk_numeral(N - 1, sz), m);
        expr_ref signx = bvr.mk_ule(bv.mk_numeral(N / 2, sz), x);
        expr_ref signy = bvr.mk_ule(bv.mk_numeral(N / 2, sz), y);
        expr_ref absx = br.mk_ite(signx, bvr.mk_bv_neg(x), x);
        expr_ref absy = br.mk_ite(signy, bvr.mk_bv_neg(y), y);
        expr_ref d = expr_ref(bv.mk_bv_udiv(absx, absy), m);
        expr_ref r = br.mk_ite(br.mk_eq_rw(signx, signy), d, bvr.mk_bv_neg(d));
        r = br.mk_ite(br.mk_eq_rw(z, y),
                br.mk_ite(signx, o, n1),
                     br.mk_ite(br.mk_eq_rw(x, z), z, r));
        return r;
    }

    expr_ref bv_terms::mk_smod(expr* x, expr* y) {
        // u := umod(abs(x), abs(y))
        // u = 0 ->  0
        // y = 0 ->  x
        // x < 0, y < 0 ->  -u
        // x < 0, y >= 0 ->  y - u
        // x >= 0, y < 0 ->  y + u
        // x >= 0, y >= 0 ->  u
        bool_rewriter br(m);
        bv_rewriter bvr(m);
        unsigned sz = bv.get_bv_size(x);
        expr_ref z(bv.mk_zero(sz), m);
        expr_ref abs_x = br.mk_ite(bvr.mk_sle(z, x), x, bvr.mk_bv_neg(x));
        expr_ref abs_y = br.mk_ite(bvr.mk_sle(z, y), y, bvr.mk_bv_neg(y));
        expr_ref u = bvr.mk_bv_urem(abs_x, abs_y);
        expr_ref r(m);
        r = br.mk_ite(br.mk_eq_rw(u, z), z,
                br.mk_ite(br.mk_eq_rw(y, z), x,
                    br.mk_ite(br.mk_and(bvr.mk_sle(z, x), bvr.mk_sle(z, x)), u,
                        br.mk_ite(bvr.mk_sle(z, x), bvr.mk_bv_add(y, u),
                            br.mk_ite(bv.mk_sle(z, y), bvr.mk_bv_sub(y, u), bvr.mk_bv_neg(u))))));
        return r;
    }

    expr_ref bv_terms::mk_srem(expr* x, expr* y) {
        // y = 0 -> x
        // else x - sdiv(x, y) * y
        expr_ref r(m);
        bool_rewriter br(m);
        bv_rewriter bvr(m);
        expr_ref z(bv.mk_zero(bv.get_bv_size(x)), m);
        r = br.mk_ite(br.mk_eq_rw(y, z), x, bvr.mk_bv_sub(x, bvr.mk_bv_mul(y, mk_sdiv(x, y)))); 
        return r;
    }

    bool bv_terms::is_bv_predicate(expr* e) const {
        if (!e || !is_app(e) || !m.is_bool(e))
            return false;
        auto a = to_app(e);
        if (a->get_family_id() == bv.get_family_id())
            return true;
        if (m.is_eq(e) && bv.is_bv(a->get_arg(0)))
            return true;
        return false;
    }

    ptr_vector<expr> const& bv_terms::uninterp_occurs(expr* e) {
        unsigned id = e->get_id();
        m_uninterp_occurs.reserve(id + 1);
        if (!m_uninterp_occurs[id].empty())
            return m_uninterp_occurs[id];
        register_uninterp(e);
        return m_uninterp_occurs[id];
    }

    void bv_terms::register_uninterp(expr* e) {
        m_uninterp_occurs.reserve(e->get_id() + 1);
        auto& occs = m_uninterp_occurs[e->get_id()];
        ptr_vector<expr> todo;
        todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
        expr_mark marked;
        expr* c, * th, * el;
        for (unsigned i = 0; i < todo.size(); ++i) {
            e = todo[i];
            if (marked.is_marked(e))
                continue;
            marked.mark(e);
            if (is_app(e) && to_app(e)->get_family_id() == bv.get_fid()) {
                for (expr* arg : *to_app(e))
                    todo.push_back(arg);
            }
            else if (m.is_bool(e) && to_app(e)->get_family_id() == basic_family_id) {
                for (expr* arg : *to_app(e))
                    todo.push_back(arg);
            }
            else if (m.is_ite(e, c, th, el)) {
                todo.push_back(c);
                //if (ctx.is_true(c))
                    todo.push_back(th);
                //else
                    todo.push_back(el);
            }
            else if (is_uninterp(e) && (m.is_bool(e) || bv.is_bv(e))) 
                occs.push_back(e);            
        }
    }
}
