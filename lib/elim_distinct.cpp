/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    elim_distinct.cpp

Abstract:

    Replace one distinct(t0, ..., tn) with (t0 = 0 and ... and tn = n)
    when the sort of t0...tn is uninterpreted.

Author:

    Leonardo de Moura (leonardo) 2011-04-28

Revision History:

--*/
#include"elim_distinct.h"
#include"assertion_set.h"
#include"model_converter.h"
#include"arith_decl_plugin.h"
#include"rewriter_def.h"
#include"critical_flet.h"

struct elim_distinct::imp {
    struct mc : public model_converter {
        ast_ref_vector                  m_asts;
        sort *                          m_usort;
        obj_map<func_decl, func_decl *> m_inv_map; 
    public:
        mc(ast_manager & m):m_asts(m) {
        } 
    };

    struct u2i_cfg : public default_rewriter_cfg {
        arith_util                       m_autil;
        ast_ref_vector                   m_asts;
        sort *                           m_usort;
        sort *                           m_int_sort;
        obj_map<func_decl, func_decl *>  m_f2f;

        ast_manager & m() const { return m_asts.get_manager(); }

        bool must_remap(func_decl * f) const {
            if (f->get_range() == m_usort) 
                return true;
            for (unsigned i = 0; i < f->get_arity(); i++) {
                if (f->get_domain(i) == m_usort) 
                    return true;
            }
            return false;
        }

        sort * remap(sort * s) {
            return (s == m_usort) ? m_int_sort : s;
        }

        func_decl * remap(func_decl * f) {
            ptr_buffer<sort> new_domain;
            sort * new_range = remap(f->get_range());
            for (unsigned i = 0; i < f->get_arity(); i++)
                new_domain.push_back(remap(f->get_domain(i)));
            func_decl * new_f = m().mk_func_decl(f->get_name(), new_domain.size(), new_domain.c_ptr(), new_range);
            m_asts.push_back(new_f);
            m_asts.push_back(f);
            m_f2f.insert(f, new_f);
            return new_f;
        }

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            result_pr = 0;
            func_decl * new_f;
            if (m_f2f.find(f, new_f)) {
                result = m().mk_app(new_f, num, args);
                return BR_DONE;
            }

            if (!must_remap(f))
                return BR_FAILED;

            if (m().is_eq(f)) {
                result = m().mk_eq(args[0], args[1]);
                return BR_DONE;
            }

            if (m().is_ite(f)) {
                result = m().mk_ite(args[0], args[1], args[2]);
                return BR_DONE;
            }

            if (f->get_family_id() != null_family_id || f->get_info() != 0) {
                throw elim_distinct_exception("uninterpreted sort is used in interpreted function symbol");
            }

            new_f = remap(f);
            result = m().mk_app(new_f, num, args);
            return BR_DONE;
        }

        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            throw elim_distinct_exception("elim-distinct tactic does not support quantifiers");
        }

        u2i_cfg(ast_manager & m, sort * u):
            m_autil(m),
            m_asts(m),
            m_usort(u) {
            m_asts.push_back(u);
            m_int_sort = m_autil.mk_int();
            m_asts.push_back(m_int_sort);
        }
    };
    
    class u2i : public rewriter_tpl<u2i_cfg> {
        u2i_cfg m_cfg;
    public:
        u2i(ast_manager & m, sort * u):
            rewriter_tpl<u2i_cfg>(m, false, m_cfg),
            m_cfg(m, u) {
            if (m.proofs_enabled())
                throw elim_distinct_exception("elim-distinct tactic does not support proof generation");
        }
        arith_util & autil() { return cfg().m_autil; }
    };

    ast_manager & m_manager;
    u2i *         m_u2i;

    imp(ast_manager & m):m_manager(m), m_u2i(0) {}
    ast_manager & m() const { return m_manager; }
    
    bool is_distinct(expr * t) {
        if (!m().is_distinct(t))
            return false;
        if (to_app(t)->get_num_args() == 0)
            return false;
        return m().is_uninterp(m().get_sort(to_app(t)->get_arg(0)));
    }
    
    model_converter * operator()(assertion_set & s, app * d) {
        if (d && !is_distinct(d))
            d = 0;
        app * r = 0; 
        unsigned sz = s.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = s.form(i);
            if (curr == d)
                break;
            if (is_distinct(curr)) {
                if (!r || to_app(curr)->get_num_args() > r->get_num_args())
                    r = to_app(curr);
            }
        }
        if (d != 0)
            r = d;
        if (r == 0)
            return 0;
        sort * u = m().get_sort(to_app(r)->get_arg(0));
        u2i    conv(m(), u);
        {
            critical_flet<u2i*> l1(m_u2i, &conv);
            expr_ref new_curr(m());
            for (unsigned i = 0; i < sz; i++) {
                expr * curr = s.form(i);
                if (curr == r) {
                    unsigned num = r->get_num_args();
                    for (unsigned j = 0; j < num; j++) {
                        expr * arg = r->get_arg(j);
                        conv(arg, new_curr);
                        expr * eq  = m().mk_eq(new_curr, conv.autil().mk_numeral(rational(j), true));
                        s.assert_expr(eq);
                    }
                    new_curr = m().mk_true();
                }
                else {
                    conv(curr, new_curr);
                }
            
                s.update(i, new_curr);
            }
        }
        
        // TODO: create model converter
        return 0;
    }

    void cancel() {
        // Remark: m_u2i is protected by the omp global critical section.
        // If this is a performance problem, then replace critical_flet by a custom flet that uses a different 
        // section name
        #pragma omp critical (critical_flet)
        {
            if (m_u2i)
                m_u2i->cancel();
        }
    }
};

template class rewriter_tpl<elim_distinct::imp::u2i_cfg>;

elim_distinct::elim_distinct(ast_manager & m) {
    m_imp = alloc(imp, m);
}
    
elim_distinct::~elim_distinct() {
    dealloc(m_imp);
}

model_converter * elim_distinct::operator()(assertion_set & s, app * d) {
    return m_imp->operator()(s, d);
}

void elim_distinct::cancel() {
    m_imp->cancel();
}

void elim_distinct::reset() {
    cleanup();
}

void elim_distinct::cleanup() {
    ast_manager & m = m_imp->m();
    dealloc(m_imp);
    m_imp = alloc(imp, m);
}
