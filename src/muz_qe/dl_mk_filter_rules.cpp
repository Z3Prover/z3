/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_filter_rules.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-18.

Revision History:

--*/

#include"dl_mk_filter_rules.h"
#include"dl_context.h"
#include"for_each_expr.h"
#include"ast_pp.h"

namespace datalog {

    mk_filter_rules::mk_filter_rules(context & ctx):
            plugin(2000),
            m_context(ctx),
            m_manager(ctx.get_manager()),
            m_result(0), 
            m_pinned(m_manager) {
    }
    mk_filter_rules::~mk_filter_rules() {
        ptr_vector<filter_key> to_dealloc;
        filter_cache::iterator it = m_tail2filter.begin();
        filter_cache::iterator end = m_tail2filter.end();
        for(; it!=end; ++it) {
            to_dealloc.push_back(it->m_key);
        }
        m_tail2filter.reset();
        ptr_vector<filter_key>::iterator dit = to_dealloc.begin();
        ptr_vector<filter_key>::iterator dend = to_dealloc.end();
        for(; dit!=dend; ++dit) {
            dealloc(*dit);
        }
    }
            
    /**
       \brief Return true if \c pred is a cadidate for a "filter" rule.
    */
    bool mk_filter_rules::is_candidate(app * pred) {
        if (!m_context.get_rule_manager().is_predicate(pred)) {
            TRACE("mk_filter_rules", tout << mk_pp(pred, m_manager) << "\nis not a candidate because it is interpreted.\n";);
            return false;
        }
        var_idx_set used_vars;
        unsigned n  = pred->get_num_args();
        for (unsigned i = 0; i < n; i++) {
            expr * arg = pred->get_arg(i);
            if (m_manager.is_value(arg))
                return true;
            SASSERT(is_var(arg));
            unsigned vidx = to_var(arg)->get_idx();
            if (used_vars.contains(vidx))
                return true;
            used_vars.insert(vidx);
        }
        return false;
    }

    /**
       \brief Create a "filter" (if it doesn't exist already) for the given predicate.
    */
    func_decl *  mk_filter_rules::mk_filter_decl(app * pred, var_idx_set const & non_local_vars) {
        sort_ref_buffer filter_domain(m_manager);

        filter_key * key = alloc(filter_key, m_manager);
        mk_new_rule_tail(m_manager, pred, non_local_vars, filter_domain, key->filter_args, key->new_pred);
        func_decl * filter_decl = 0;
        if (!m_tail2filter.find(key, filter_decl)) {
            filter_decl = m_context.mk_fresh_head_predicate(pred->get_decl()->get_name(), symbol("filter"), 
                filter_domain.size(), filter_domain.c_ptr(), pred->get_decl());

            m_pinned.push_back(filter_decl);
            m_tail2filter.insert(key, filter_decl);
            app_ref filter_head(m_manager);
            filter_head = m_manager.mk_app(filter_decl, key->filter_args.size(), key->filter_args.c_ptr());
            app * filter_tail = key->new_pred;
            rule * filter_rule = m_context.get_rule_manager().mk(filter_head, 1, &filter_tail, (const bool *)0);
            filter_rule->set_accounting_parent_object(m_context, m_current);
            m_result->add_rule(filter_rule);
        }
        else {
            dealloc(key);
        }
        SASSERT(filter_decl != 0);
        SASSERT(filter_decl->get_arity()==filter_domain.size());
        return filter_decl;
    }

    void mk_filter_rules::process(rule * r) {
        m_current = r;
        app * new_head = r->get_head();
        app_ref_vector new_tail(m_manager);
        svector<bool>  new_is_negated;
        unsigned sz = r->get_tail_size();
        bool rule_modified = false;
        for (unsigned i = 0; i < sz; i++) {
            app * tail = r->get_tail(i);
            if (is_candidate(tail)) {
                TRACE("mk_filter_rules", tout << "is_candidate: " << mk_pp(tail, m_manager) << "\n";);
                var_idx_set non_local_vars;
                collect_non_local_vars(m_manager, r, tail, non_local_vars);
                func_decl * filter_decl = mk_filter_decl(tail, non_local_vars);
                ptr_buffer<expr> new_args;
                var_idx_set used_vars;
                unsigned num_args = tail->get_num_args(); 
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg = tail->get_arg(i);
                    if (is_var(arg)) {
                        unsigned vidx = to_var(arg)->get_idx();
                        if (non_local_vars.contains(vidx) && !used_vars.contains(vidx)) {
                            new_args.push_back(arg);
                            used_vars.insert(vidx);
                        }
                    }
                }
                SASSERT(new_args.size() == filter_decl->get_arity());
                new_tail.push_back(m_manager.mk_app(filter_decl, new_args.size(), new_args.c_ptr()));
                rule_modified = true;
            }
            else {
                new_tail.push_back(tail);
            }
            new_is_negated.push_back(r->is_neg_tail(i));
        }
        if(rule_modified) {
            remove_duplicate_tails(new_tail, new_is_negated);
            SASSERT(new_tail.size() == new_is_negated.size());
            rule * new_rule = m_context.get_rule_manager().mk(new_head, new_tail.size(), new_tail.c_ptr(), new_is_negated.c_ptr());
            new_rule->set_accounting_parent_object(m_context, m_current);
            m_result->add_rule(new_rule);
            m_modified = true;
        }
        else {
            m_result->add_rule(r);
        }
    }

    rule_set * mk_filter_rules::operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc) {
        // TODO mc, pc
        m_tail2filter.reset();
        m_result           = alloc(rule_set, m_context);
        m_modified         = false;
        unsigned num_rules = source.get_num_rules();
        for (unsigned i = 0; i < num_rules; i++) {
            rule * r = source.get_rule(i);
            process(r);
        }
        if(!m_modified) {
            dealloc(m_result);
            return static_cast<rule_set *>(0);
        }
        return m_result;
    }

};
