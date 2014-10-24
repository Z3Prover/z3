/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pdr_closure.cpp

Abstract:

    Utility functions for computing closures.

Author:

    Nikolaj Bjorner (nbjorner) 2013-9-1.

Revision History:

--*/

#include "pdr_closure.h"
#include "pdr_context.h"
#include "expr_safe_replace.h"

namespace pdr {

    expr_ref scaler::operator()(expr* e, expr* k, obj_map<func_decl, expr*>* translate) {
        m_cache[0].reset();
        m_cache[1].reset();
        m_translate = translate;
        m_k = k;
        return scale(e, false);
    }

    expr_ref scaler::scale(expr* e, bool is_mul) {
        expr* r;
        if (m_cache[is_mul].find(e, r)) {
            return expr_ref(r, m);
        }
        if (!is_app(e)) {
            return expr_ref(e, m);
        }
        app* ap = to_app(e);
        if (m_translate && m_translate->find(ap->get_decl(), r)) {
            return expr_ref(r, m);
        }
        if (!is_mul && a.is_numeral(e)) {
            return expr_ref(a.mk_mul(m_k, e), m);
        }
        expr_ref_vector args(m);
        bool is_mul_rec = is_mul || a.is_mul(e);
        for (unsigned i = 0; i < ap->get_num_args(); ++i) {
            args.push_back(scale(ap->get_arg(i), is_mul_rec));
        }
        expr_ref result(m);
        result = m.mk_app(ap->get_decl(), args.size(), args.c_ptr());
        m_cache[is_mul].insert(e, result);
        return result;
    }

    expr_ref scaler::undo_k(expr* e, expr* k) {
        expr_safe_replace sub(m);
        th_rewriter rw(m);
        expr_ref result(e, m);
        sub.insert(k, a.mk_numeral(rational(1), false));
        sub(result);
        rw(result);
        return result;
    }


    closure::closure(pred_transformer& p, bool is_closure):
        m(p.get_manager()), m_pt(p), a(m), 
        m_is_closure(is_closure), m_sigma(m), m_trail(m) {}


    void closure::add_variables(unsigned num_vars, expr_ref_vector& fmls) {
        manager& pm = m_pt.get_pdr_manager();
        SASSERT(num_vars > 0);
        while (m_vars.size() < num_vars) {
            m_vars.resize(m_vars.size()+1);
            m_sigma.push_back(m.mk_fresh_const("sigma", a.mk_real()));
        }

        unsigned sz = m_pt.sig_size();        

        for (unsigned i = 0; i < sz; ++i) {
            expr* var;
            ptr_vector<expr> vars;
            func_decl* fn0 = m_pt.sig(i);
            func_decl* fn1 = pm.o2n(fn0, 0);
            sort* srt = fn0->get_range();
            if (a.is_int_real(srt)) {
                for (unsigned j = 0; j < num_vars; ++j) {
                    if (!m_vars[j].find(fn1, var)) {
                        var  = m.mk_fresh_const(fn1->get_name().str().c_str(), srt);
                        m_trail.push_back(var);               
                        m_vars[j].insert(fn1, var);
                    }
                    vars.push_back(var);
                }
                fmls.push_back(m.mk_eq(m.mk_const(fn1), a.mk_add(num_vars, vars.c_ptr())));
            }
        }
        if (m_is_closure) {
            for (unsigned i = 0; i < num_vars; ++i) {
                fmls.push_back(a.mk_ge(m_sigma[i].get(), a.mk_numeral(rational(0), a.mk_real())));
            }
        }
        else {
            // is interior:
            for (unsigned i = 0; i < num_vars; ++i) {
                fmls.push_back(a.mk_gt(m_sigma[i].get(), a.mk_numeral(rational(0), a.mk_real())));
            }
        }
        fmls.push_back(m.mk_eq(a.mk_numeral(rational(1), a.mk_real()), a.mk_add(num_vars, m_sigma.c_ptr())));
    }

    expr_ref closure::close_fml(expr* e) {
        expr* e0, *e1, *e2;
        expr_ref result(m);
        if (a.is_lt(e, e1, e2)) {
            result = a.mk_le(e1, e2);
        }
        else if (a.is_gt(e, e1, e2)) {
            result = a.mk_ge(e1, e2);
        }
        else if (m.is_not(e, e0) && a.is_ge(e0, e1, e2)) {
            result = a.mk_le(e1, e2);
        }
        else if (m.is_not(e, e0) && a.is_le(e0, e1, e2)) {
            result = a.mk_ge(e1, e2);
        }
        else if (a.is_ge(e) || a.is_le(e) || m.is_eq(e) ||
                 (m.is_not(e, e0) && (a.is_gt(e0) || a.is_lt(e0)))) {
            result = e;
        }
        else {
            IF_VERBOSE(1, verbose_stream() << "Cannot close: " << mk_pp(e, m) << "\n";);
            result = m.mk_true();
        }
        return result;        
    }

    expr_ref closure::close_conjunction(expr* fml) {
        expr_ref_vector fmls(m);
        qe::flatten_and(fml, fmls);
        for (unsigned i = 0; i < fmls.size(); ++i) {
            fmls[i] = close_fml(fmls[i].get());            
        }
        return qe::mk_and(fmls);
    }

    expr_ref closure::relax(unsigned i, expr* fml) {
        scaler sc(m);
        expr_ref result = sc(fml, m_sigma[i].get(), &m_vars[i]);
        return close_conjunction(result);
    }

    expr_ref closure::operator()(expr_ref_vector const& As) {
        if (As.empty()) {
            return expr_ref(m.mk_false(), m);
        }
        if (As.size() == 1) {
            return expr_ref(As[0], m);
        }
        expr_ref_vector fmls(m);
        expr_ref B(m);
        add_variables(As.size(), fmls);
        for (unsigned i = 0; i < As.size(); ++i) {
            fmls.push_back(relax(i, As[i]));
        }
        B = qe::mk_and(fmls);
        return B;
    }

}
