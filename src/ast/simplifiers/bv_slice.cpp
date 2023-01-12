/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bv_slice.cpp

Abstract:

    simplifier for extracting bit-vector ranges

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/simplifiers/bv_slice.h"

namespace bv {

    void slice::reduce() {
        process_eqs();
        apply_subst();
    }

    void slice::process_eqs() {
        for (unsigned i : indices()) {
            auto const [f, p, d] = m_fmls[i]();
            process_eq(f);
        }  
    }

    void slice::process_eq(expr* e) {
        expr* x, * y;
        if (!m.is_eq(e, x, y))
            return;
        if (!m_bv.is_bv(x))
            return;
        m_xs.reset();
        m_ys.reset();
        get_concats(x, m_xs);
        get_concats(y, m_ys);
        slice_eq();
    }

    void slice::slice_eq() {
        unsigned i = m_xs.size(), j = m_ys.size();
        unsigned offx = 0, offy = 0;
        while (0 < i) {
            SASSERT(0 < j);
            expr* x = m_xs[i - 1]; // least significant bits are last 
            expr* y = m_ys[j - 1];
            SASSERT(offx == 0 || offy == 0);
            unsigned szx = m_bv.get_bv_size(x);
            unsigned szy = m_bv.get_bv_size(y);
            SASSERT(offx < szx);
            SASSERT(offy < szy);
            if (szx - offx == szy - offy) {
                register_slice(offx, szx - 1, x);
                register_slice(offy, szy - 1, y);
                --i;
                --j;
                offx = 0;
                offy = 0;
            }
            else if (szx - offx < szy - offy) {
                register_slice(offx, szx - 1, x);
                register_slice(offy, offy + szx - offx - 1, y);
                offy += szx - offx;
                offx = 0;
                --i;
            }
            else {
                register_slice(offy, szy - 1, y);
                register_slice(offx, offx + szy - offy - 1, x);
                offx += szy - offy;
                offy = 0;
                --j;
            }
        }
    }

    void slice::register_slice(unsigned lo, unsigned hi, expr* x) {
        SASSERT(lo <= hi && hi < m_bv.get_bv_size(x));
        unsigned l, h;
        while (m_bv.is_extract(x, l, h, x)) {
            // x[l:h][lo:hi] = x[l+lo:l+hi]
            hi += l;
            lo += l;
            SASSERT(lo <= hi && hi < m_bv.get_bv_size(x));
        }
        unsigned sz = m_bv.get_bv_size(x);
        if (hi - lo + 1 == sz)
            return;
        SASSERT(0 < lo || hi + 1 < sz);
        auto& b = m_boundaries.insert_if_not_there(x, uint_set());

        struct remove_set : public trail {
            uint_set& b;
            unsigned i;
            remove_set(uint_set& b, unsigned i) :b(b), i(i) {}
            void undo() override {
                b.remove(i);
            }
        };
        if (lo > 0 && !b.contains(lo)) {
            b.insert(lo); 
            if (num_scopes() > 0)
                m_trail.push(remove_set(b, lo));
        }
        if (hi + 1 < sz && !b.contains(hi + 1)) {
            b.insert(hi + 1); 
            if (num_scopes() > 0)
                m_trail.push(remove_set(b, hi+ 1));
        }
    }

    expr* slice::mk_extract(unsigned hi, unsigned lo, expr* x) {
        unsigned l, h;
        while (m_bv.is_extract(x, l, h, x)) {
            lo += l;
            hi += l;
        }
        if (lo == 0 && hi + 1 == m_bv.get_bv_size(x))
            return x;
        else
            return m_bv.mk_extract(hi, lo, x);
    }

    void slice::apply_subst() {
        if (m_boundaries.empty())
            return;            
        expr_ref_vector cache(m), pin(m);
        ptr_vector<expr> todo, args;
        expr* c;
        for (unsigned i : indices()) {
            auto const [f, p, d] = m_fmls[i]();
            todo.push_back(f);
            pin.push_back(f);
            while (!todo.empty()) {
                expr* e = todo.back();
                c = cache.get(e->get_id(), nullptr);
                if (c) {
                    todo.pop_back();
                    continue;
                }
                if (!is_app(e)) {
                    cache.setx(e->get_id(), e);
                    todo.pop_back();
                    continue;
                }
                args.reset();
                unsigned sz = todo.size();
                bool change = false;
                for (expr* arg : *to_app(e)) {
                    c = cache.get(arg->get_id(), nullptr);
                    if (c) {
                        args.push_back(c);
                        change |= c != arg;
                        SASSERT(c->get_sort() == arg->get_sort());
                    }
                    else
                        todo.push_back(arg);
                }
                if (sz == todo.size()) {
                    todo.pop_back();
                    if (change)
                        cache.setx(e->get_id(), m_rewriter.mk_app(to_app(e)->get_decl(), args));
                    else
                        cache.setx(e->get_id(), e);
                    SASSERT(e->get_sort() == cache.get(e->get_id())->get_sort());
                    uint_set b;
                    if (m_boundaries.find(e, b)) {
                        expr* r = cache.get(e->get_id());
                        expr_ref_vector xs(m);
                        unsigned lo = 0;
                        for (unsigned hi : b) {
                            xs.push_back(mk_extract(hi - 1, lo, r));
                            lo = hi;
                        }
                        xs.push_back(mk_extract(m_bv.get_bv_size(r) - 1, lo, r));
                        xs.reverse();
                        expr_ref xc(m_bv.mk_concat(xs), m);
                        cache.setx(e->get_id(), xc);    
                        SASSERT(e->get_sort() == xc->get_sort());
                    }
                }
            }
            c = cache.get(f->get_id());
            if (c != f)                 
                m_fmls.update(i, dependent_expr(m, c, nullptr, d));            
        }
    }

    void slice::get_concats(expr* x, ptr_vector<expr>& xs) {
        while (m_bv.is_concat(x)) {
            xs.append(to_app(x)->get_num_args(), to_app(x)->get_args()); 
            x = xs.back();
            xs.pop_back();
        }
        xs.push_back(x);
    }
}
