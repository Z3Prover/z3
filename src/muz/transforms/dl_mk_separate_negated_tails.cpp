/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    mk_separate_negated_tails.cpp

Abstract:

    <see header>

Author:

    Nikolaj Bjorner (nbjorner) 2013-09-09

Revision History:

--*/

#include "dl_mk_separate_negated_tails.h"
#include "dl_context.h"

namespace datalog {

    mk_separate_negated_tails::mk_separate_negated_tails(context& ctx, unsigned priority):
        plugin(priority),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_ctx(ctx)
    {}

    bool mk_separate_negated_tails::has_private_vars(rule const& r, unsigned j) {
        get_private_vars(r, j);
        return !m_vars.empty();
    }

    void mk_separate_negated_tails::get_private_vars(rule const& r, unsigned j) {
        m_vars.reset();
        m_fv.reset();
        m_fv(r.get_head());
        for (unsigned i = 0; i < r.get_tail_size(); ++i) {
            if (i != j) {
                m_fv.accumulate(r.get_tail(i));
            }
        }
        
        app* p = r.get_tail(j);
        for (unsigned i = 0; i < p->get_num_args(); ++i) {
            expr* v = p->get_arg(i);
            if (is_var(v)) {
                unsigned idx = to_var(v)->get_idx();
                if (!m_fv.contains(idx)) {
                    m_vars.push_back(v);
                }
            }
        }
    }

    void mk_separate_negated_tails::abstract_predicate(app* p, app_ref& q, rule_set& rules) {
        expr_ref_vector args(m);
        sort_ref_vector sorts(m);
        func_decl_ref fn(m);
        for (unsigned i = 0; i < p->get_num_args(); ++i) {
            expr* arg = p->get_arg(i);
            if (!m_vars.contains(arg)) {
                args.push_back(arg);
                sorts.push_back(m.get_sort(arg));
            }
        }
        fn = m.mk_fresh_func_decl(p->get_decl()->get_name(), symbol("N"), sorts.size(), sorts.c_ptr(), m.mk_bool_sort());
        m_ctx.register_predicate(fn, false);
        q = m.mk_app(fn, args.size(), args.c_ptr());
        bool is_neg = true;
        rules.add_rule(rm.mk(q, 1, & p, &is_neg));
    }

    void mk_separate_negated_tails::create_rule(rule const&r, rule_set& rules) {
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned ptsz = r.get_positive_tail_size();
        unsigned tsz  = r.get_tail_size();
        app_ref_vector tail(m);
        app_ref p(m);
        svector<bool> neg;
        for (unsigned i = 0; i < ptsz; ++i) {
            tail.push_back(r.get_tail(i));
            neg.push_back(false);
        }
        for (unsigned i = ptsz; i < utsz; ++i) {
            get_private_vars(r, i);
            if (!m_vars.empty()) {
                abstract_predicate(r.get_tail(i), p, rules);
                tail.push_back(p);
                neg.push_back(false);
            }
            else {
                neg.push_back(true);
                tail.push_back(r.get_tail(i));
            }
        }
        for (unsigned i = utsz; i < tsz; ++i) {
            tail.push_back(r.get_tail(i));
            neg.push_back(false);
        }
        rules.add_rule(rm.mk(r.get_head(), tail.size(), tail.c_ptr(), neg.c_ptr(), r.name()));
    }
    
    rule_set * mk_separate_negated_tails::operator()(rule_set const& src) {
        scoped_ptr<rule_set> result = alloc(rule_set, m_ctx);
        bool has_new_rule = false;
        unsigned sz = src.get_num_rules();
        for (unsigned i = 0; i < sz; ++i) {            
            bool change = false;
            rule & r = *src.get_rule(i);
            unsigned utsz = r.get_uninterpreted_tail_size();
            unsigned ptsz = r.get_positive_tail_size();
            for (unsigned j = ptsz; j < utsz; ++j) {
                SASSERT(r.is_neg_tail(j));
                if (has_private_vars(r, j)) {
                    create_rule(r, *result);
                    has_new_rule = true;
                    change = true;
                    break;
                }
            }
            if (!change) {
                result->add_rule(&r);
            }
        }
        if (!has_new_rule) {
            return 0;
        }
        else {
            result->inherit_predicates(src);
            return result.detach();
        }
    }
}
