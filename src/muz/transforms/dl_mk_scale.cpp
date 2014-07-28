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
#include"fixedpoint_params.hpp"

namespace datalog {

    class mk_scale::scale_model_converter : public model_converter {
        ast_manager& m;
        func_decl_ref_vector m_trail;
        arith_util   a;
        obj_map<func_decl, func_decl*> m_new2old;
    public:
        scale_model_converter(ast_manager& m): m(m), m_trail(m), a(m) {}

        virtual ~scale_model_converter() {}

        void add_new2old(func_decl* new_f, func_decl* old_f) {
            m_trail.push_back(old_f);
            m_trail.push_back(new_f);
            m_new2old.insert(new_f, old_f);
        }
       
        virtual void operator()(model_ref& md) {
            model_ref old_model = alloc(model, m);
            obj_map<func_decl, func_decl*>::iterator it  = m_new2old.begin();
            obj_map<func_decl, func_decl*>::iterator end = m_new2old.end();
            for (; it != end; ++it) {
                func_decl* old_p = it->m_value;
                func_decl* new_p = it->m_key;
                func_interp* old_fi = alloc(func_interp, m, old_p->get_arity());

                if (new_p->get_arity() == 0) {
                    old_fi->set_else(md->get_const_interp(new_p));
                }
                else {
                    func_interp* new_fi = md->get_func_interp(new_p);
                    expr_ref_vector subst(m);
                    var_subst vs(m, false);
                    expr_ref tmp(m);

                    if (!new_fi) {
                        TRACE("dl", tout << new_p->get_name() << " has no value in the current model\n";);
                        dealloc(old_fi);
                        continue;
                    }
                    for (unsigned i = 0; i < old_p->get_arity(); ++i) {
                        subst.push_back(m.mk_var(i, old_p->get_domain(i)));
                    }
                    subst.push_back(a.mk_numeral(rational(1), a.mk_real()));

                    // Hedge that we don't have to handle the general case for models produced
                    // by Horn clause solvers.
                    SASSERT(!new_fi->is_partial() && new_fi->num_entries() == 0);
                    vs(new_fi->get_else(), subst.size(), subst.c_ptr(), tmp);
                    old_fi->set_else(tmp);
                    old_model->register_decl(old_p, old_fi);
                }
            }
    
            // register values that have not been scaled.
            unsigned sz = md->get_num_constants();
            for (unsigned i = 0; i < sz; ++i) {
                func_decl* c = md->get_constant(i);
                if (!m_new2old.contains(c)) {
                    old_model->register_decl(c, md->get_const_interp(c));
                }
            }
            sz = md->get_num_functions();
            for (unsigned i = 0; i < sz; ++i) {
                func_decl* f = md->get_function(i);
                if (!m_new2old.contains(f)) {
                    func_interp* fi = md->get_func_interp(f);
                    old_model->register_decl(f, fi->copy());
                }
            }
            md = old_model;
            //TRACE("dl", model_smt2_pp(tout, m, *md, 0); );
        }

        virtual model_converter * translate(ast_translation & translator) {
            UNREACHABLE();
            return 0;
        }
    };


    mk_scale::mk_scale(context & ctx, unsigned priority):
        plugin(priority),
        m(ctx.get_manager()),
        m_ctx(ctx),
        a(m),
        m_trail(m),
        m_eqs(m) {        
    }

    mk_scale::~mk_scale() { 
    }
        
    rule_set * mk_scale::operator()(rule_set const & source) {
        if (!m_ctx.scale()) {
            return 0;
        }
        rule_manager& rm = source.get_rule_manager();
        rule_set * result = alloc(rule_set, m_ctx);
        unsigned sz = source.get_num_rules();
        rule_ref new_rule(rm);
        app_ref_vector tail(m);
        app_ref head(m);
        svector<bool> neg;
        ptr_vector<sort> vars;
        ref<scale_model_converter> smc;
        if (m_ctx.get_model_converter()) {
            smc = alloc(scale_model_converter, m);
        }
        m_mc = smc.get();

        for (unsigned i = 0; i < sz; ++i) {            
            rule & r = *source.get_rule(i);
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned tsz  = r.get_tail_size();
            tail.reset();
            vars.reset();
            m_cache.reset();
            m_trail.reset();
            m_eqs.reset();
            r.get_vars(m, vars);
            unsigned num_vars = vars.size();
            for (unsigned j = 0; j < utsz; ++j) {
                tail.push_back(mk_pred(num_vars, r.get_tail(j)));
            }
            for (unsigned j = utsz; j < tsz; ++j) {
                tail.push_back(mk_constraint(num_vars, r.get_tail(j)));
            }
            app_ref new_pred = mk_pred(num_vars, r.get_head());
            tail.append(m_eqs);
            tail.push_back(a.mk_gt(m.mk_var(num_vars, a.mk_real()), a.mk_numeral(rational(0), false)));
            neg.resize(tail.size(), false);
            new_rule = rm.mk(new_pred, tail.size(), tail.c_ptr(), neg.c_ptr(), r.name(), true);
            result->add_rule(new_rule);                
            if (source.is_output_predicate(r.get_decl())) {
                result->set_output_predicate(new_rule->get_decl());
            }            
        }
        TRACE("dl", result->display(tout););
        if (m_mc) {
            m_ctx.add_model_converter(m_mc);
        }
        m_trail.reset();
        m_cache.reset();
        return result;
    }

    app_ref mk_scale::mk_pred(unsigned sigma_idx, app* q) {
        func_decl* f = q->get_decl();
        ptr_vector<sort> domain(f->get_arity(), f->get_domain());
        domain.push_back(a.mk_real());
        func_decl_ref g(m);
        g = m.mk_func_decl(f->get_name(), f->get_arity() + 1, domain.c_ptr(), f->get_range());
        expr_ref_vector args(m);
        for (unsigned i = 0; i < q->get_num_args(); ++i) {
            expr* arg = q->get_arg(i);
            rational val;
            if (a.is_numeral(arg, val)) {
                if (val.is_zero()) {
                    // arg is unchanged.
                }
                else if (val.is_one()) {
                    arg = m.mk_var(sigma_idx, a.mk_real());
                }
                else {
                    // create a fresh variable 'v', add 'v == sigma*arg'
                    expr* v = m.mk_var(sigma_idx + 1 + m_eqs.size(), a.mk_real());
                    m_eqs.push_back(m.mk_eq(v, a.mk_mul(arg, m.mk_var(sigma_idx, a.mk_real()))));
                    arg = v;
                }
            }
            args.push_back(arg);
        }
        args.push_back(m.mk_var(sigma_idx, a.mk_real()));
        m_ctx.register_predicate(g, false);
        if (m_mc) {
            m_mc->add_new2old(g, f);
        }
        return app_ref(m.mk_app(g, q->get_num_args() + 1, args.c_ptr()), m);
    }

    app_ref mk_scale::mk_constraint(unsigned sigma_idx, app* q) {
        expr* r = linearize(sigma_idx, q);
        SASSERT(is_app(r));
        return app_ref(to_app(r), m);
    }

    expr* mk_scale::linearize(unsigned sigma_idx, expr* e) {
        expr* r;
        if (m_cache.find(e, r)) {
            return r;
        }
        if (!is_app(e)) {
            return e;
        }
        expr_ref result(m);
        app* ap = to_app(e);
        if (ap->get_family_id() == m.get_basic_family_id() ||
            a.is_add(e) || a.is_sub(e) ||
            a.is_le(e)  || a.is_ge(e)  ||
            a.is_lt(e)  || a.is_gt(e)) {
            expr_ref_vector args(m);
            for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                args.push_back(linearize(sigma_idx, ap->get_arg(i)));                
            }
            result = m.mk_app(ap->get_decl(), args.size(), args.c_ptr());
        }
        else if (a.is_numeral(e)) {
            result = a.mk_mul(m.mk_var(sigma_idx, a.mk_real()), e);
        }
        else {
            result = e;
        }
        m_trail.push_back(result);
        m_cache.insert(e, result);
        return result;
    }

};
