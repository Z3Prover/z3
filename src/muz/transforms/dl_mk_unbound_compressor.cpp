/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_unbound_compressor.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-10-04.

Revision History:

--*/

#include<utility>
#include<sstream>
#include "muz/transforms/dl_mk_unbound_compressor.h"

namespace datalog {

    mk_unbound_compressor::mk_unbound_compressor(context & ctx) :
        plugin(500),
        m_context(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_rules(rm),
        m_pinned(m) {
    }

    void mk_unbound_compressor::reset() {
        m_rules.reset();
        m_todo.reset();
        m_in_progress.reset();
        m_map.reset();
        m_pinned.reset();
    }

    bool mk_unbound_compressor::is_unbound_argument(rule * r, unsigned head_index) {
        app * head = r->get_head();
        expr * head_arg = head->get_arg(head_index);
        unsigned var_idx;
        return 
            is_var(head_arg, var_idx) &&
            rm.collect_tail_vars(r).contains(var_idx);
    }

    void mk_unbound_compressor::add_task(func_decl * pred, unsigned arg_index) {
        SASSERT(pred->get_arity() > 0);

        c_info ci(pred, arg_index);
        if (m_map.contains(ci)) {
            return; //this task was already added
        }

        unsigned parent_arity = pred->get_arity();
        sort * const * parent_domain = pred->get_domain();
        symbol const& parent_name = pred->get_name();
        unsigned arity = parent_arity-1;
        ptr_vector<sort> domain;
        for (unsigned i = 0; i < parent_arity; i++) {
            if (i != arg_index) {
                domain.push_back(parent_domain[i]);
            }
        }

        std::stringstream name_suffix;
        name_suffix << "compr_arg_" << arg_index;

        func_decl * cpred = m_context.mk_fresh_head_predicate(parent_name, symbol(name_suffix.str().c_str()), 
            arity, domain.c_ptr(), pred);
        m_pinned.push_back(cpred);
        m_pinned.push_back(pred);

        m_todo.push_back(ci);
        m_map.insert(ci, cpred);
        TRACE("dl", tout << "inserting: " << pred->get_name() << " " << arg_index << " for " << cpred->get_name() << "\n";);
    }

    void mk_unbound_compressor::detect_tasks(rule_set const& source, unsigned rule_index) {
        rule * r = m_rules.get(rule_index);
        var_idx_set& tail_vars = rm.collect_tail_vars(r);

        app * head = r->get_head();
        func_decl * head_pred = head->get_decl();
        if (source.is_output_predicate(head_pred)) {
            //we don't compress output predicates
            return;
        }

        unsigned n = head_pred->get_arity();
        
        rm.get_counter().reset();
        rm.get_counter().count_vars(head, 1);

        for (unsigned i = 0; i < n; i++) {
            expr * arg = head->get_arg(i);
            unsigned var_idx;
            if (is_var(arg, var_idx) && 
                !tail_vars.contains(var_idx) && 
                (1 == rm.get_counter().get(var_idx))) {
                TRACE("dl", r->display(m_context, tout << "Compress: "););
                add_task(head_pred, i);
                break;
                //we compress out the unbound arguments one by one
            }
        }
    }

    // 
    // l_undef if nothing to compress.
    // l_true if compressed.
    // l_false if removed.
    // 
    lbool mk_unbound_compressor::try_compress(rule_set const& source, unsigned rule_index) {
        rule * r = m_rules.get(rule_index);
        var_idx_set& tail_vars = rm.collect_tail_vars(r);
        
        app * head = r->get_head();
        func_decl * head_pred = head->get_decl();
        unsigned head_arity = head_pred->get_arity();

        rm.get_counter().reset();
        rm.get_counter().count_vars(head);

        unsigned arg_index;
        for (arg_index = 0; arg_index < head_arity; arg_index++) {
            expr * arg = head->get_arg(arg_index);
            unsigned var_idx;
            if (is_var(arg, var_idx) && 
                !tail_vars.contains(var_idx) && 
                (rm.get_counter().get(var_idx) == 1) && 
                m_in_progress.contains(c_info(head_pred, arg_index))) {
                break;
            }
        }
        if (arg_index == head_arity) {
            //we didn't find anything to compress
            return l_undef;
        }
        c_info ci(head_pred, arg_index);

        SASSERT(arg_index < head_arity);
        SASSERT(m_in_progress.contains(ci));
        func_decl * cpred = m_map.find(ci);
        ptr_vector<expr> cargs;
        for (unsigned i=0; i < head_arity; i++) {
            if (i != arg_index) {
                cargs.push_back(head->get_arg(i));
            }
        }

        app_ref chead(m.mk_app(cpred, head_arity-1, cargs.c_ptr()), m);

        m_modified = true;
        if (r->get_tail_size()==0 && m_context.get_rule_manager().is_fact(chead)) {
            m_non_empty_rels.insert(cpred);
            m_context.add_fact(chead);
            //remove the rule that became fact by placing the last rule on its place
            m_head_occurrence_ctr.dec(m_rules.get(rule_index)->get_decl());
            unsigned new_size = m_rules.size() - 1;
            rule* last_rule = m_rules.get(new_size);
            TRACE("dl", tout << "remove\n"; r->display(m_context, tout); 
                  tout << "shift\n"; last_rule->display(m_context, tout););
            if (rule_index < new_size) {
                m_rules.set(rule_index, last_rule);
            }
            m_rules.shrink(new_size);
            return l_false;
        }
        else {
            rule_ref new_rule(m_context.get_rule_manager().mk(r, chead, r->name()), m_context.get_rule_manager());
            new_rule->set_accounting_parent_object(m_context, r);

            m_head_occurrence_ctr.dec(m_rules.get(rule_index)->get_decl());
            TRACE("dl", tout << "remove\n"; r->display(m_context, tout); 
                  tout << "set\n"; new_rule->display(m_context, tout););
            m_rules.set(rule_index, new_rule);
            m_head_occurrence_ctr.inc(m_rules.get(rule_index)->get_decl());
            detect_tasks(source, rule_index);
            return l_true;
        }
    }

    rule_ref mk_unbound_compressor::mk_decompression_rule(rule * r, unsigned tail_index, unsigned arg_index) {
        rule_ref res(m_context.get_rule_manager());

        app * orig_dtail = r->get_tail(tail_index); //dtail ~ decompressed tail
        c_info ci(orig_dtail->get_decl(), arg_index);

        TRACE("dl", tout << "retrieving: " << ci.first->get_name() << " " << ci.second << "\n";);

        func_decl * dtail_pred = m_map.find(ci);
        ptr_vector<expr> dtail_args;
        unsigned orig_dtail_arity = orig_dtail->get_num_args();
        for (unsigned i = 0; i < orig_dtail_arity; i++) {
            if (i != arg_index) {
                dtail_args.push_back(orig_dtail->get_arg(i));
            }
        }
        SASSERT(dtail_args.size()==dtail_pred->get_arity());
        app_ref dtail(m.mk_app(dtail_pred, dtail_args.size(), dtail_args.c_ptr()), m);

        svector<bool> tails_negated;
        app_ref_vector tails(m);
        unsigned tail_len = r->get_tail_size();
        for (unsigned i = 0; i < tail_len; i++) {
            tails_negated.push_back(r->is_neg_tail(i));
            if (i == tail_index && !r->is_neg_tail(i)) {
                tails.push_back(dtail);
            }
            else {
                tails.push_back(r->get_tail(i));
            }
        }

        // Accumulate negated filtered rule instead 
        // of replacing the original predicate.
        if (r->is_neg_tail(tail_index)) {
            tails_negated.push_back(true);
            tails.push_back(dtail);
        }

        res = m_context.get_rule_manager().mk( r->get_head(), tails.size(), tails.c_ptr(), tails_negated.c_ptr());
        res->set_accounting_parent_object(m_context, r);
        m_context.get_rule_manager().fix_unbound_vars(res, true);        
        return res;
    }


    //TODO: avoid rule duplicity
    //If two predicates are compressed in a rule, applying decompression 
    //to the results can cause a rule being added multiple times:
    //P:- R(x,y), S(x,y)
    //is decompressed into rules
    //P:- R1(x), S(x,y)
    //P:- R(x,y), S1(x)
    //and each of these rules is again decompressed giving the same rule
    //P:- R1(x), S1(x)
    //P:- R1(x), S1(x)

    void mk_unbound_compressor::add_decompression_rule(rule_set const& source, rule * r, unsigned tail_index, unsigned arg_index) {
        rule_ref new_rule = mk_decompression_rule(r, tail_index, arg_index);
        unsigned new_rule_index = m_rules.size();
        m_rules.push_back(new_rule);
        TRACE("dl", r->display(m_context, tout); new_rule->display(m_context, tout); );
        m_context.get_rule_manager().mk_rule_rewrite_proof(*r, *new_rule.get());
        m_head_occurrence_ctr.inc(new_rule->get_decl());
        detect_tasks(source, new_rule_index);
        m_modified = true;
    }

    void mk_unbound_compressor::replace_by_decompression_rule(rule_set const& source, unsigned rule_index, unsigned tail_index, unsigned arg_index) {
        rule * r = m_rules.get(rule_index);
        rule_ref new_rule = mk_decompression_rule(r, tail_index, arg_index);
        TRACE("dl", tout << "remove\n"; r->display(m_context, tout); tout << "set\n"; new_rule->display(m_context, tout););
        m_rules.set(rule_index, new_rule);
        // we don't update the m_head_occurrence_ctr because the head predicate doesn't change
        detect_tasks(source, rule_index);
        m_modified = true;
    }
    
    void mk_unbound_compressor::add_in_progress_indices(unsigned_vector& arg_indices, app* p) {
        arg_indices.reset();
        for (unsigned i = 0; i < p->get_num_args(); ++i) {
            if (m_in_progress.contains(c_info(p->get_decl(), i))) {
                SASSERT(m_map.contains(c_info(p->get_decl(), i)));
                arg_indices.push_back(i);
            }
        }
    }

    bool mk_unbound_compressor::decompress_rule(rule_set const& source, rule* r, unsigned_vector const& arg_indices, unsigned rule_index, unsigned tail_index) {
        app * t = r->get_tail(tail_index);
        func_decl * t_pred = t->get_decl();
        bool is_negated_predicate = r->is_neg_tail(tail_index);

        bool replace_original_rule = false;
        for (unsigned i = 0; i < arg_indices.size(); ++i) {
            unsigned arg_index = arg_indices[i];
            
            SASSERT(m_in_progress.contains(c_info(t_pred, arg_index)));
            SASSERT(m_map.contains(c_info(t_pred, arg_index)));
            bool can_remove_orig_rule = 
                arg_indices.empty() &&
                !m_non_empty_rels.contains(t_pred) &&
                m_head_occurrence_ctr.get(t_pred) == 0;                
            
            if (can_remove_orig_rule || is_negated_predicate) {
                replace_original_rule = true;
                replace_by_decompression_rule(source, rule_index, tail_index, arg_index);
                // NB. arg_indices becomes stale after original rule is replaced.
                if (is_negated_predicate && !can_remove_orig_rule) {
                    break;
                }
            }
            else {
                add_decompression_rule(source, r, tail_index, arg_index);
            }
        }
        return replace_original_rule;
    }

    
    void mk_unbound_compressor::add_decompression_rules(rule_set const& source, unsigned rule_index) {
        
        unsigned_vector arg_indices;
        
        // this value is updated inside the loop if replace_by_decompression_rule is called
        rule_ref r(m_rules.get(rule_index), m_context.get_rule_manager());

        unsigned utail_len = r->get_uninterpreted_tail_size();
        unsigned tail_index = 0;
        while (tail_index < utail_len) {
            app * t = r->get_tail(tail_index);

            add_in_progress_indices(arg_indices, t);

            bool replace_original_rule = decompress_rule(source, r, arg_indices, rule_index, tail_index);

            if (replace_original_rule) {
                // update r with the new rule
                rule * new_rule = m_rules.get(rule_index);
                SASSERT(new_rule->get_uninterpreted_tail_size() >= utail_len);
                // here we check that the rule replacement didn't affect other uninterpreted literals 
                // in the tail (aside of variable renaming)
                SASSERT(tail_index==0 || new_rule->get_decl(tail_index-1) == r->get_decl(tail_index-1));

                r = new_rule;

                //we have replaced the original rule, with one that has different
                //content of the tail_index -th tail. we will therefore not do
                //tail_index++, so that we examine the new tail literal as well
            }
            else {
                tail_index++;
            }
        }
    }

    rule_set * mk_unbound_compressor::operator()(rule_set const & source) {
        // TODO mc

        if (!m_context.compress_unbound()) {
            return nullptr;
        }

        m_modified = false;

        SASSERT(m_rules.empty());

        rel_context_base* rel = m_context.get_rel_context();
        if (rel) {
            rel->collect_non_empty_predicates(m_non_empty_rels);
        }
        unsigned init_rule_cnt = source.get_num_rules();
        for (unsigned i = 0; i < init_rule_cnt; i++) {
            rule * r = source.get_rule(i);
            m_rules.push_back(r);
            m_head_occurrence_ctr.inc(r->get_decl());
        }

        for (unsigned i = 0; i < init_rule_cnt; i++) {
            detect_tasks(source, i);
        }

        while (!m_todo.empty()) {
            m_in_progress.reset();
            while (!m_todo.empty()) {
                m_in_progress.insert(m_todo.back());
                m_todo.pop_back();
            }
            for (unsigned rule_index = 0; rule_index < m_rules.size(); ) {
                switch (try_compress(source, rule_index)) {
                case l_true:
                case l_undef:
                    add_decompression_rules(source, rule_index); //m_rules.size() can be increased here
                    ++rule_index;
                    break;
                case l_false:
                    break;
                }
            }
        }

        rule_set * result = static_cast<rule_set *>(nullptr);
        if (m_modified) {
            result = alloc(rule_set, m_context);
            unsigned fin_rule_cnt = m_rules.size();
            for (unsigned i=0; i<fin_rule_cnt; i++) {
                result->add_rule(m_rules.get(i));
            }
            result->inherit_predicates(source);
        }
        reset();
        return result;
    }


};
