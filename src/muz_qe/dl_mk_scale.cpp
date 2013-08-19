/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_scale.cpp

Abstract:


Author:

    Nikolaj Bjorner (nbjorner) 2013-08-19

Revision History:

--*/

#include"dl_mk_scale.h"
#include"dl_context.h"

namespace datalog {


    mk_scale::mk_scale(context & ctx, unsigned priority):
        plugin(priority),
        m(ctx.get_manager()),
        m_ctx(ctx),
        a(m),
        m_trail(m) {        
    }

    mk_scale::~mk_scale() { }
        
    rule_set * mk_scale::operator()(rule_set const & source) {
        if (!m_ctx.get_params().scale()) {
            return 0;
        }
        context& ctx = source.get_context();
        rule_manager& rm = source.get_rule_manager();
        rule_set * result = alloc(rule_set, ctx);
        unsigned sz = source.get_num_rules();
        rule_ref new_rule(rm);
        app_ref_vector tail(m);
        app_ref head(m);
        svector<bool> neg;
        ptr_vector<sort> vars;
        for (unsigned i = 0; i < sz; ++i) {            
            rule & r = *source.get_rule(i);
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned tsz  = r.get_tail_size();
            tail.reset();
            neg.reset();
            vars.reset();
            r.get_vars(vars);
            m_cache.reset();
            m_trail.reset();
            unsigned num_vars = vars.size();
            for (unsigned j = utsz; j < tsz; ++j) {
                tail.push_back(mk_pred(num_vars, r.get_tail(j)));
                neg.push_back(false);
            }
            for (unsigned j = 0; j < utsz; ++j) {
                tail.push_back(mk_constraint(num_vars, r.get_tail(j)));
                neg.push_back(false);
            }
            tail.push_back(a.mk_gt(m.mk_var(num_vars, a.mk_real()), a.mk_numeral(rational(0), false)));
            neg.push_back(false);
            new_rule = rm.mk(mk_pred(num_vars, r.get_head()), tail.size(), tail.c_ptr(), neg.c_ptr(), r.name(), true);
            result->add_rule(new_rule);                
            if (source.is_output_predicate(r.get_decl())) {
                result->set_output_predicate(new_rule->get_decl());
            }            
        }
        TRACE("dl", result->display(tout););
        return result;
    }

    app_ref mk_scale::mk_pred(unsigned num_vars, app* q) {
        func_decl* f = q->get_decl();
        ptr_vector<sort> domain(f->get_arity(), f->get_domain());
        domain.push_back(a.mk_real());
        func_decl_ref g(m);
        g = m.mk_func_decl(f->get_name(), f->get_arity() + 1, domain.c_ptr(), f->get_range());
        ptr_vector<expr> args(q->get_num_args(), q->get_args());
        args.push_back(m.mk_var(num_vars, a.mk_real()));
        m_ctx.register_predicate(g, false);
        return app_ref(m.mk_app(g, q->get_num_args() + 1, args.c_ptr()), m);
    }

    app_ref mk_scale::mk_constraint(unsigned num_vars, app* q) {
        expr* r = linearize(num_vars, q);
        SASSERT(is_app(r));
        return app_ref(to_app(r), m);
    }

    expr* mk_scale::linearize(unsigned num_vars, expr* e) {
        expr* r;
        if (m_cache.find(e, r)) {
            return expr_ref(r, m);
        }
        if (!is_app(e)) {
            return expr_ref(e, m);
        }
        expr_ref result(m);
        app* ap = to_app(e);
        if (ap->get_family_id() == m.get_basic_family_id() ||
            a.is_add(e) || a.is_sub(e) ||
            a.is_le(e)  || a.is_ge(e)  ||
            a.is_lt(e)  || a.is_gt(e)) {
            expr_ref_vector args(m);
            for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                args.push_back(linearize(num_vars, ap->get_arg(i)));                
            }
            result = m.mk_app(ap->get_decl(), args.size(), args.c_ptr());
        }
        else if (a.is_numeral(e)) {
            result = a.mk_mul(m.mk_var(num_vars, a.mk_real()), e);
        }
        else {
            result = e;
        }
        m_trail.push_back(result);
        m_cache.insert(e, result);
        return result;
    }

};
