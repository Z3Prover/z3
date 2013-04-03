/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_quantifier_abstraction.cpp

Abstract:

    Create quantified Horn clauses from benchmarks with arrays.

Author:

    Ken McMillan 
    Andrey Rybalchenko
    Nikolaj Bjorner (nbjorner) 2013-04-02

Revision History:

--*/

#include "dl_mk_quantifier_abstraction.h"
#include "dl_context.h"
#include "expr_safe_replace.h"
#include "expr_abstract.h"

namespace datalog {


    // model converter: 
    // Given model for P^(x, y, i, a[i])
    // create model: P(x,y,a) == forall i . P^(x,y,i,a[i])
    // requires substitution and list of bound variables.

    class mk_quantifier_abstraction::qa_model_converter : public model_converter {
        ast_manager&            m;
        func_decl_ref_vector    m_old_funcs;
        func_decl_ref_vector    m_new_funcs;
        vector<expr_ref_vector> m_subst;
        vector<svector<bool> >  m_bound;

    public:

        qa_model_converter(ast_manager& m):
            m(m), m_old_funcs(m), m_new_funcs(m) {}

        virtual ~qa_model_converter() {}

        virtual model_converter * translate(ast_translation & translator) { 
            return alloc(qa_model_converter, m);
        }

        void insert(func_decl* old_p, func_decl* new_p, expr_ref_vector& sub, svector<bool> const& bound) {
            m_old_funcs.push_back(old_p);
            m_new_funcs.push_back(new_p);
            m_subst.push_back(sub);
            m_bound.push_back(bound);
        }

        virtual void operator()(model_ref & model) {
            for (unsigned i = 0; i < m_new_funcs.size(); ++i) {
                func_decl* p = m_new_funcs[i].get();
                func_decl* q = m_old_funcs[i].get();
                expr_ref_vector const& s = m_subst[i];
                svector<bool> const& is_bound  = m_bound[i];
                func_interp* f = model->get_func_interp(p);
                expr_ref body(m);                
                unsigned arity_p = p->get_arity();
                unsigned arity_q = q->get_arity();
                SASSERT(0 < arity_p);
                model->register_decl(p, f);
                func_interp* g = alloc(func_interp, m, arity_q);

                if (f) {
                    body = f->get_interp();
                    SASSERT(!f->is_partial());
                    SASSERT(body);                    
                }
                else {
                    body = m.mk_false();  
                }
                // TBD. create quantifier wrapper around body.

                // 1. replace variables by the compound terms from 
                //    the original predicate.
                expr_safe_replace sub(m);
                for (unsigned i = 0; i < s.size(); ++i) {
                    sub.insert(m.mk_var(i, m.get_sort(s[i])), s[i]);
                }
                sub(body);
                sub.reset();

                // 2. replace bound variables by constants.
                expr_ref_vector consts(m), bound(m), free(m);
                ptr_vector<sort> sorts;
                svector<symbol> names;
                for (unsigned i = 0; i < q->get_arity(); ++i) {
                    sort* s = q->get_domain(i);
                    consts.push_back(m.mk_fresh_const("C", s));
                    sub.insert(m.mk_var(i, s), consts.back());
                    if (is_bound[i]) {
                        bound.push_back(consts.back());
                        names.push_back(symbol(i));
                        sorts.push_back(s);
                    }
                    else {
                        free.push_back(consts.back());
                    }
                }
                sub(body);                
                sub.reset();

                // 3. abstract and quantify those variables that should be bound.
                expr_abstract(m, 0, bound.size(), bound.c_ptr(), body, body);
                body = m.mk_forall(names.size(), sorts.c_ptr(), names.c_ptr(), body);

                // 4. replace remaining constants by variables.                                
                for (unsigned i = 0; i < free.size(); ++i) {
                    sub.insert(free[i].get(), m.mk_var(i, m.get_sort(free[i].get())));
                }
                sub(body);                
                g->set_else(body);
                model->register_decl(q, g);
            }  
        }                        
    };

    mk_quantifier_abstraction::mk_quantifier_abstraction(
        context & ctx, unsigned priority):
        plugin(priority),
        m(ctx.get_manager()),
        m_ctx(ctx),
        a(m),
        m_refs(m) {        
    }

    mk_quantifier_abstraction::~mk_quantifier_abstraction() {        
    }

    func_decl* mk_quantifier_abstraction::declare_pred(func_decl* old_p) {

        unsigned sz = old_p->get_arity();
        unsigned num_arrays = 0;
        for (unsigned i = 0; i < sz; ++i) {
            if (a.is_array(old_p->get_domain(i))) {
                num_arrays++;
            }
        }
        if (num_arrays == 0) {
            return 0;
        }

        func_decl* new_p = 0;
        if (!m_old2new.find(old_p, new_p)) {
            expr_ref_vector sub(m);
            svector<bool> bound;
            sort_ref_vector domain(m);
            expr_ref arg(m);
            for (unsigned i = 0; i < sz; ++i) {
                sort* s = old_p->get_domain(i);
                unsigned lookahead = 0;
                sort* s0 = s;
                while (a.is_array(s0)) {
                    lookahead += get_array_arity(s0);
                    s0 = get_array_range(s0);
                }
                arg = m.mk_var(bound.size() + lookahead, s);
                while (a.is_array(s)) {
                    unsigned arity = get_array_arity(s);
                    expr_ref_vector args(m);
                    for (unsigned j = 0; j < arity; ++j) {
                        domain.push_back(get_array_domain(s, j));
                        args.push_back(m.mk_var(bound.size(), domain.back()));
                        bound.push_back(true);
                    }
                    arg = mk_select(arg, args.size(), args.c_ptr());
                    s = get_array_range(s);
                }
                domain.push_back(s);
                bound.push_back(false);
                sub.push_back(arg);
            }          
            SASSERT(old_p->get_range() == m.mk_bool_sort());
            new_p = m.mk_func_decl(old_p->get_name(), domain.size(), domain.c_ptr(), old_p->get_range());
            m_refs.push_back(new_p);
            m_ctx.register_predicate(new_p, false);
            if (m_mc) {
                m_mc->insert(old_p, new_p, sub, bound);
            }
        }
        return new_p;
    }

    app_ref mk_quantifier_abstraction::mk_head(app* p, unsigned idx) {
        func_decl* new_p = declare_pred(p->get_decl());
        if (!new_p) {
            return app_ref(p, m);
        }
        expr_ref_vector args(m);
        expr_ref arg(m);
        unsigned sz = p->get_num_args();
        for (unsigned i = 0; i < sz; ++i) {
            arg = p->get_arg(i);
            sort* s = m.get_sort(arg);
            while (a.is_array(s)) {
                unsigned arity = get_array_arity(s);
                for (unsigned j = 0; j < arity; ++j) {
                    args.push_back(m.mk_var(idx++, get_array_domain(s, j)));
                }
                arg = mk_select(arg, arity, args.c_ptr()+args.size()-arity);
                s = get_array_range(s);
            }
            args.push_back(arg);
        }
        return app_ref(m.mk_app(new_p, args.size(), args.c_ptr()), m);        
    }

    app_ref mk_quantifier_abstraction::mk_tail(app* p) {
        func_decl* old_p = p->get_decl();
        func_decl* new_p = declare_pred(old_p);
        if (!new_p) {
            return app_ref(p, m);
        }
        SASSERT(new_p->get_arity() > old_p->get_arity());
        unsigned num_extra_args = new_p->get_arity() - old_p->get_arity();
        var_shifter shift(m);
        expr_ref p_shifted(m);
        shift(p, num_extra_args, p_shifted);
        app* ps = to_app(p_shifted);
        expr_ref_vector args(m);
        app_ref_vector  pats(m);
        sort_ref_vector vars(m);
        svector<symbol> names;
        expr_ref arg(m);
        unsigned idx = 0;
        unsigned sz = p->get_num_args();
        for (unsigned i = 0; i < sz; ++i) {
            arg = ps->get_arg(i);
            sort* s = m.get_sort(arg);
            bool is_pattern = false;
            while (a.is_array(s)) {
                is_pattern = true;
                unsigned arity = get_array_arity(s);
                for (unsigned j = 0; j < arity; ++j) {
                    vars.push_back(get_array_domain(s, j));
                    names.push_back(symbol(idx));
                    args.push_back(m.mk_var(idx++, vars.back()));
                }
                arg = mk_select(arg, arity, args.c_ptr()+args.size()-arity);
                s = get_array_range(s);
            }
            if (is_pattern) {
                pats.push_back(to_app(arg));
            }
            args.push_back(arg);
        }
        expr* pat = 0;
        expr_ref pattern(m);
        pattern = m.mk_pattern(pats.size(), pats.c_ptr());
        pat = pattern.get();
        app_ref result(m);
        symbol qid, skid;
        result = m.mk_app(new_p, args.size(), args.c_ptr());
        result = m.mk_eq(m.mk_forall(vars.size(), vars.c_ptr(), names.c_ptr(), result, 1, qid, skid, 1, &pat), m.mk_true());
        return result;
    }

    expr * mk_quantifier_abstraction::mk_select(expr* arg, unsigned num_args, expr* const* args) {
        ptr_vector<expr> args2;
        args2.push_back(arg);
        args2.append(num_args, args);
        return a.mk_select(args2.size(), args2.c_ptr());                
    }
        
    rule_set * mk_quantifier_abstraction::operator()(rule_set const & source) {
        TRACE("dl", tout << "quantify " << source.get_num_rules() << " " << m_ctx.get_params().quantify_arrays() << "\n";);
        if (!m_ctx.get_params().quantify_arrays()) {
            return 0;
        }
        m_refs.reset();
        m_old2new.reset();
        m_new2old.reset();
        rule_manager& rm = source.get_rule_manager();
        rule_set * result = alloc(rule_set, m_ctx);
        unsigned sz = source.get_num_rules();
        rule_ref new_rule(rm);
        app_ref_vector tail(m);
        app_ref head(m);
        svector<bool> neg;
        rule_counter& vc = rm.get_counter();

        if (m_ctx.get_model_converter()) {
            m_mc = alloc(qa_model_converter, m);
        }

        for (unsigned i = 0; i < sz; ++i) {            
            tail.reset();
            neg.reset();
            rule & r = *source.get_rule(i);
            unsigned cnt = vc.get_max_rule_var(r)+1;
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned tsz = r.get_tail_size();
            for (unsigned j = 0; j < utsz; ++j) {
                tail.push_back(mk_tail(r.get_tail(j)));
                neg.push_back(r.is_neg_tail(j));
            }
            for (unsigned j = utsz; j < tsz; ++j) {
                tail.push_back(r.get_tail(j));
                neg.push_back(false);
            }
            head = mk_head(r.get_head(), cnt);

            new_rule = rm.mk(head, tail.size(), tail.c_ptr(), neg.c_ptr(), r.name(), true);
            TRACE("dl", r.display(m_ctx, tout); new_rule->display(m_ctx, tout););
            result->add_rule(new_rule);
        }        
        
        // proof converter: proofs are not necessarily preserved using this transformation.

        if (m_old2new.empty()) {
            dealloc(result);
            dealloc(m_mc);
            result = 0;
        }
        else {
            m_ctx.add_model_converter(m_mc);
        }
        m_mc = 0;

        return result;
    }


};


