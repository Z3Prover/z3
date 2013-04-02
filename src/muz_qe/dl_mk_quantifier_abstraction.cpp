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

namespace datalog {

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
            sort_ref_vector domain(m);
            for (unsigned i = 0; i < sz; ++i) {
                sort* s = old_p->get_domain(i);
                while (a.is_array(s)) {
                    unsigned arity = get_array_arity(s);
                    for (unsigned j = 0; j < arity; ++j) {
                        domain.push_back(get_array_domain(s, j));
                    }
                    s = get_array_range(s);
                }
                domain.push_back(s);
            }          
            SASSERT(old_p->get_range() == m.mk_bool_sort());
            new_p = m.mk_func_decl(old_p->get_name(), domain.size(), domain.c_ptr(), old_p->get_range());
            m_refs.push_back(new_p);
            m_ctx.register_predicate(new_p);
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
                ptr_vector<expr> args2;
                args2.push_back(arg);
                args2.append(arity, args.c_ptr()-arity);
                arg = a.mk_select(args2.size(), args2.c_ptr());
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
                ptr_vector<expr> args2;
                args2.push_back(arg);
                args2.append(arity, args.c_ptr()-arity);
                arg = a.mk_select(args2.size(), args2.c_ptr());
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
        
    rule_set * mk_quantifier_abstraction::operator()(rule_set const & source) {
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
            result->add_rule(new_rule);

        }        

        // model converter: TBD.
        // proof converter: TBD.

        if (m_old2new.empty()) {
            dealloc(result);
            result = 0;
        }
        return result;
    }


};


