/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls.cpp

Abstract:

    A Stochastic Local Search (SLS) engine
    Uses invertibility conditions, 
    interval annotations
    don't care annotations

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/

#include "ast/ast_ll_pp.h"
#include "ast/sls/bv_sls.h"
#include "ast/rewriter/th_rewriter.h"

namespace bv {

    sls_terms::sls_terms(ast_manager& m): 
        m(m), 
        bv(m),
        m_rewriter(m),
        m_assertions(m),
        m_pinned(m),
        m_translated(m), 
        m_terms(m){}


    void sls_terms::assert_expr(expr* e) {
        m_assertions.push_back(ensure_binary(e));
    }

    expr* sls_terms::ensure_binary(expr* e) {
        expr* top = e;
        m_pinned.push_back(e);
        m_todo.push_back(e);
        {
            expr_fast_mark1 mark;
            for (unsigned i = 0; i < m_todo.size(); ++i) {
                expr* e = m_todo[i];
                if (!is_app(e))
                    continue;
                if (m_translated.get(e->get_id(), nullptr))
                    continue;
                if (mark.is_marked(e))
                    continue;
                mark.mark(e);
                for (auto arg : *to_app(e))
                    m_todo.push_back(arg);
            }
        }
        std::stable_sort(m_todo.begin(), m_todo.end(), [&](expr* a, expr* b) { return get_depth(a) < get_depth(b); });
        for (expr* e : m_todo)
            ensure_binary_core(e);
        m_todo.reset();
        return m_translated.get(top->get_id());
    }

    void sls_terms::ensure_binary_core(expr* e) {
        if (m_translated.get(e->get_id(), nullptr))
            return;
        
        app* a = to_app(e);
        auto arg = [&](unsigned i) {
            return m_translated.get(a->get_arg(i)->get_id());
        };
        unsigned num_args = a->get_num_args();
        expr_ref r(m);
#define FOLD_OP(oper)           \
        r = arg(0);             \
        for (unsigned i = 1; i < num_args; ++i)\
            r = oper(r, arg(i)); \

        if (m.is_and(e)) {
            FOLD_OP(m.mk_and);
        }
        else if (m.is_or(e)) {
            FOLD_OP(m.mk_or);
        }
        else if (m.is_xor(e)) {
            FOLD_OP(m.mk_xor);
        }
        else if (bv.is_bv_and(e)) {
            FOLD_OP(bv.mk_bv_and);
        }
        else if (bv.is_bv_or(e)) {
            FOLD_OP(bv.mk_bv_or);
        }
        else if (bv.is_bv_xor(e)) {
            FOLD_OP(bv.mk_bv_xor);
        }
        else if (bv.is_bv_add(e)) {
            FOLD_OP(bv.mk_bv_add);
        }
        else if (bv.is_bv_mul(e)) {
            FOLD_OP(bv.mk_bv_mul);
        }
        else if (bv.is_concat(e)) {
            FOLD_OP(bv.mk_concat);
        }
        else if (m.is_distinct(e)) {
            expr_ref_vector es(m);
            for (unsigned i = 0; i < num_args; ++i)
                for (unsigned j = i + 1; j < num_args; ++j)
                    es.push_back(m.mk_not(m.mk_eq(arg(i), arg(j))));
            r = m.mk_and(es);
        }
        else if (bv.is_bv_sdiv(e) || bv.is_bv_sdiv0(e) || bv.is_bv_sdivi(e)) {
            r = mk_sdiv(arg(0), arg(1));
        }
        else if (bv.is_bv_smod(e) || bv.is_bv_smod0(e) || bv.is_bv_smodi(e)) {
            r = mk_smod(arg(0), arg(1));
        }
        else if (bv.is_bv_srem(e) || bv.is_bv_srem0(e) || bv.is_bv_sremi(e)) {
            r = mk_srem(arg(0), arg(1));
        }
        else {
            for (unsigned i = 0; i < num_args; ++i)
                m_args.push_back(arg(i));
            r = m.mk_app(a->get_decl(), num_args, m_args.data());
            m_args.reset();
        }
        m_translated.setx(e->get_id(), r);
    }

    expr_ref sls_terms::mk_sdiv(expr* x, expr* y) {
        // d = udiv(abs(x), abs(y))
        // y = 0, x >= 0 -> -1
        // y = 0, x < 0 -> 1
        // x = 0, y != 0 -> 0
        // x > 0, y < 0 -> -d
        // x < 0, y > 0 -> -d
        // x > 0, y > 0 -> d
        // x < 0, y < 0 -> d
        unsigned sz = bv.get_bv_size(x);
        rational N = rational::power_of_two(sz);
        expr_ref z(bv.mk_zero(sz), m);
        expr* signx = bv.mk_ule(bv.mk_numeral(N / 2, sz), x);
        expr* signy = bv.mk_ule(bv.mk_numeral(N / 2, sz), y);
        expr* absx = m.mk_ite(signx, bv.mk_bv_neg(x), x);
        expr* absy = m.mk_ite(signy, bv.mk_bv_neg(y), y);
        expr* d = bv.mk_bv_udiv(absx, absy);
        expr_ref r(m.mk_ite(m.mk_eq(signx, signy), d, bv.mk_bv_neg(d)), m);
        r = m.mk_ite(m.mk_eq(z, y),
                     m.mk_ite(signx, bv.mk_one(sz), bv.mk_numeral(N - 1, sz)),
                     m.mk_ite(m.mk_eq(x, z), z, r));
        m_rewriter(r);
        return r;
    }

    expr_ref sls_terms::mk_smod(expr* x, expr* y) {
        // u := umod(abs(x), abs(y))
        // u = 0 ->  0
        // y = 0 ->  x
        // x < 0, y < 0 ->  -u
        // x < 0, y >= 0 ->  y - u
        // x >= 0, y < 0 ->  y + u
        // x >= 0, y >= 0 ->  u
        unsigned sz = bv.get_bv_size(x);
        expr_ref z(bv.mk_zero(sz), m);
        expr_ref abs_x(m.mk_ite(bv.mk_sle(z, x), x, bv.mk_bv_neg(x)), m);
        expr_ref abs_y(m.mk_ite(bv.mk_sle(z, y), y, bv.mk_bv_neg(y)), m);
        expr_ref u(bv.mk_bv_urem(abs_x, abs_y), m);
        expr_ref r(m);
        r = m.mk_ite(m.mk_eq(u, z), z,
                m.mk_ite(m.mk_eq(y, z), x,
                    m.mk_ite(m.mk_and(bv.mk_sle(z, x), bv.mk_sle(z, x)), u,
                        m.mk_ite(bv.mk_sle(z, x), bv.mk_bv_add(y, u),
                            m.mk_ite(bv.mk_sle(z, y), bv.mk_bv_sub(y, u), bv.mk_bv_neg(u))))));
        m_rewriter(r);
        return r;
    }

    expr_ref sls_terms::mk_srem(expr* x, expr* y) {
        // y = 0 -> x
        // else x - sdiv(x, y) * y
        expr_ref r(m);
        r = m.mk_ite(m.mk_eq(y, bv.mk_zero(bv.get_bv_size(x))),
                     x, bv.mk_bv_sub(x, bv.mk_bv_mul(y, mk_sdiv(x, y))));
        m_rewriter(r);
        return r;
    }


    void sls_terms::init() {
        // populate terms
        expr_fast_mark1 mark;
        for (expr* e : m_assertions)
            m_todo.push_back(e);
        while (!m_todo.empty()) {
            expr* e = m_todo.back();
            m_todo.pop_back();
            if (mark.is_marked(e) || !is_app(e))
                continue;
            mark.mark(e);            
            m_terms.setx(e->get_id(), to_app(e));
            for (expr* arg : *to_app(e))
                m_todo.push_back(arg);
        }       
        // populate parents
        m_parents.reset();
        m_parents.reserve(m_terms.size());
        for (expr* e : m_terms) {
            if (!e || !is_app(e))
                continue;
            for (expr* arg : *to_app(e))
                m_parents[arg->get_id()].push_back(e);                
        }
        m_assertion_set.reset();
        for (auto a : m_assertions)
            m_assertion_set.insert(a->get_id());
    }

    void sls_terms::updt_params(params_ref const& p) {
        params_ref q = p;
        q.set_bool("flat", false);
        m_rewriter.updt_params(q);
    }


}
