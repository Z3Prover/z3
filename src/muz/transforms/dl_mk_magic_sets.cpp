/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_magic_sets.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-10-04.

Revision History:

--*/

#include<utility>
#include<sstream>
#include "ast/ast_pp.h"
#include "muz/transforms/dl_mk_magic_sets.h"

namespace datalog {

    mk_magic_sets::mk_magic_sets(context & ctx, func_decl* goal) :
        plugin(10000, true),
        m_context(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_pinned(m), 
        m_goal(goal, m) {
    }

    void mk_magic_sets::reset() {
        m_extentional.reset();
        m_todo.reset();
        m_adorned_preds.reset();
        m_adornments.reset();
        m_magic_preds.reset();
        m_pinned.reset();
    }

    void mk_magic_sets::adornment::populate(app * lit, const var_idx_set & bound_vars) {
        SASSERT(empty());
        unsigned arity = lit->get_num_args();
        for (unsigned i = 0; i < arity; i++) {
            const expr * arg = lit->get_arg(i);
            bool bound = !is_var(arg) || bound_vars.contains(to_var(arg)->get_idx());
            push_back(bound ? AD_BOUND : AD_FREE);
        }
    }

    std::string mk_magic_sets::adornment::to_string() const {
        std::string res;
        const_iterator eit = begin();
        const_iterator eend = end();
        for (; eit != eend; ++eit) {
            res += (*eit == AD_BOUND)?'b':'f';
        }
        return res;
    }
    
    unsigned get_bound_arg_count(app * lit, const var_idx_set & bound_vars) {
        unsigned res = 0;
        unsigned n = lit->get_num_args();
        for (unsigned i = 0; i < n; i++) {
            const expr * arg = lit->get_arg(i);
            if (!is_var(arg) || bound_vars.contains(to_var(arg)->get_idx())) {
                SASSERT(is_var(arg) || is_app(arg));
                SASSERT(!is_app(arg) || to_app(arg)->get_num_args()==0);
                res++;
            }
        }
        return res;
    }

    float mk_magic_sets::get_unbound_cost(app * lit, const var_idx_set & bound_vars) {
        func_decl * pred = lit->get_decl();
        float res = 1;
        unsigned n = lit->get_num_args();
        for (unsigned i = 0; i < n; i++) {
            const expr * arg = lit->get_arg(i);
            if (is_var(arg) && !bound_vars.contains(to_var(arg)->get_idx())) {
                res *= m_context.get_sort_size_estimate(pred->get_domain(i));
            }
            //res-=1;
        }
        return res;
    }

    /**
       \brief From \c cont which is list of indexes of tail literals of rule \c r, select
       the index pointing to a literal with at least one bound variable that will be the next
       bound literal in the process of creating an adorned rule. If all literals are unbound,
       return -1.
     */
    int mk_magic_sets::pop_bound(unsigned_vector & cont, rule * r, const var_idx_set & bound_vars) {
        float best_cost;
        int candidate_index = -1;
        unsigned n = cont.size();
        for (unsigned i=0; i<n; i++) {
            app * lit = r->get_tail(cont[i]);
            unsigned bound_cnt = get_bound_arg_count(lit, bound_vars);
            if (bound_cnt==0) {
                continue;
            }
            float cost = get_unbound_cost(lit, bound_vars);
            if (candidate_index==-1 || cost<best_cost) {
                best_cost = cost;
                candidate_index = i;
            }
        }
        if (candidate_index==-1) {
            return -1;
        }
        if (candidate_index != static_cast<int>(n-1)) {
            std::swap(cont[candidate_index], cont[n-1]);
        }
        unsigned res = cont.back();
        cont.pop_back();
        return res;
    }

    app * mk_magic_sets::adorn_literal(app * lit, const var_idx_set & bound_vars) {
        SASSERT(!m_extentional.contains(lit->get_decl()));
        func_decl * old_pred = lit->get_decl();
        SASSERT(m.is_bool(old_pred->get_range()));
        adornment_desc adn(old_pred);
        adn.m_adornment.populate(lit, bound_vars);
        func_decl *& new_pred = m_adorned_preds.insert_if_not_there(adn, nullptr);
        if (new_pred==nullptr) {
            std::string suffix = "ad_"+adn.m_adornment.to_string();
            new_pred = m_context.mk_fresh_head_predicate(
                old_pred->get_name(), symbol(suffix.c_str()), 
                old_pred->get_arity(), old_pred->get_domain(), old_pred);
            m_pinned.push_back(new_pred);
            m_todo.push_back(adn);
            m_adornments.insert(new_pred, adn.m_adornment);
        }
        app * res = m.mk_app(new_pred, lit->get_args());
        m_pinned.push_back(res);
        return res;
    }
    
    app * mk_magic_sets::create_magic_literal(app * l) {
        func_decl * l_pred = l->get_decl();
        SASSERT(m.is_bool(l_pred->get_range()));
        pred_adornment_map::obj_map_entry * ae = m_adornments.find_core(l_pred);
        SASSERT(ae);
        const adornment & adn = ae->get_data().m_value;

        unsigned l_arity = l->get_num_args();
        ptr_vector<expr> bound_args;
        for (unsigned i=0; i<l_arity; i++) {
            if (adn[i]==AD_BOUND) {
                bound_args.push_back(l->get_arg(i));
            }
        }

        func_decl *& mag_pred = m_magic_preds.insert_if_not_there(l_pred, 0);
        if (mag_pred==nullptr) {
            unsigned mag_arity = bound_args.size();

            ptr_vector<sort> mag_domain;
            for (unsigned i=0; i<l_arity; i++) {
                if (adn[i]==AD_BOUND) {
                    mag_domain.push_back(l_pred->get_domain(i));
                }
            }

            mag_pred = m_context.mk_fresh_head_predicate(l_pred->get_name(), symbol("ms"), 
                mag_arity, mag_domain.data(), l_pred);
            m_pinned.push_back(mag_pred);
        }

        app * res = m.mk_app(mag_pred, bound_args.data());
        m_pinned.push_back(res);
        return res;
    }

    void mk_magic_sets::create_magic_rules(app * head, unsigned tail_cnt, app * const * tail, bool const* negated, rule_set& result) {
        //TODO: maybe include relevant interpreted predicates from the original rule
        ptr_vector<app> new_tail;
        bool_vector negations;
        new_tail.push_back(create_magic_literal(head));
        new_tail.append(tail_cnt, tail);
        negations.push_back(false);
        negations.append(tail_cnt, negated);

        for (unsigned i=0; i<tail_cnt; i++) {
            if (m_extentional.contains(tail[i]->get_decl())) {
                continue;
            }
            app * mag_head = create_magic_literal(tail[i]);
            rule * r = m_context.get_rule_manager().mk(mag_head, i+1, new_tail.data(), negations.data());
            TRACE("dl", r->display(m_context,tout); );
            result.add_rule(r);
        }
    }

    void mk_magic_sets::transform_rule(const adornment & head_adornment,  rule * r, rule_set& result) {
        app * head = r->get_head();
        unsigned head_len = head->get_num_args();
        SASSERT(head_len==head_adornment.size());

        var_idx_set bound_vars;
        for (unsigned i=0; i<head_len; i++) {
            expr * arg = head->get_arg(i);
            if (head_adornment[i]==AD_BOUND && is_var(arg)) {
                bound_vars.insert(to_var(arg)->get_idx());
            }
        }

        unsigned processed_tail_len = r->get_uninterpreted_tail_size();
        unsigned_vector exten_tails;
        unsigned_vector inten_tails;
        for (unsigned i=0; i<processed_tail_len; i++) {
            app * t = r->get_tail(i);
            if (m_extentional.contains(t->get_decl())) {
                exten_tails.push_back(i);
            }
            else {
                inten_tails.push_back(i);
            }
        }

        ptr_vector<app> new_tail;
        bool_vector negations;
        while (new_tail.size()!=processed_tail_len) {
            bool intentional = false;
            int curr_index = pop_bound(exten_tails, r, bound_vars);
            if (curr_index==-1) {
                curr_index = pop_bound(inten_tails, r,bound_vars);
                if (curr_index!=-1) {
                    intentional = true;
                }
            }
            if (curr_index==-1) {
                if (!exten_tails.empty()) {
                    curr_index = exten_tails.back();
                    exten_tails.pop_back();
                }
                else {
                    SASSERT(!inten_tails.empty());
                    curr_index = inten_tails.back();
                    inten_tails.pop_back();
                    intentional = true;
                }
            }
            SASSERT(curr_index!=-1);
            app * curr = r->get_tail(curr_index);
            if (intentional) {
                curr = adorn_literal(curr, bound_vars);
            }
            new_tail.push_back(curr);
            negations.push_back(r->is_neg_tail(curr_index));
            bound_vars |= rm.collect_vars(curr);
        }


        func_decl * new_head_pred = nullptr;
        VERIFY( m_adorned_preds.find(adornment_desc(head->get_decl(), head_adornment), new_head_pred) );
        app * new_head = m.mk_app(new_head_pred, head->get_args());

        SASSERT(new_tail.size()==r->get_uninterpreted_tail_size());
        create_magic_rules(new_head, new_tail.size(), new_tail.data(), negations.data(), result);

        unsigned tail_len = r->get_tail_size();
        for (unsigned i=processed_tail_len; i<tail_len; i++) {
            new_tail.push_back(r->get_tail(i));
            negations.push_back(r->is_neg_tail(i));
        }

        new_tail.push_back(create_magic_literal(new_head));
        negations.push_back(false);

        rule * nr = m_context.get_rule_manager().mk(new_head, new_tail.size(), new_tail.data(), negations.data(), r->name());
        result.add_rule(nr);
        nr->set_accounting_parent_object(m_context, r);
    }
    
    void mk_magic_sets::create_transfer_rule(const adornment_desc & d, rule_set& result) {
        func_decl * adn_pred = m_adorned_preds.find(d);
        unsigned arity = adn_pred->get_arity();
        SASSERT(arity == d.m_pred->get_arity());

        ptr_vector<expr> args;
        for (unsigned i=0; i<arity; i++) {
            args.push_back(m.mk_var(i, adn_pred->get_domain(i)));
        }

        app * lit = m.mk_app(d.m_pred, args.data());
        app * adn_lit = m.mk_app(adn_pred, args.data());
        app * mag_lit = create_magic_literal(adn_lit);

        app * tail[] = {lit, mag_lit};

        rule * r = m_context.get_rule_manager().mk(adn_lit, 2, tail, nullptr);
        result.add_rule(r);
    }

    rule_set * mk_magic_sets::operator()(rule_set const & source) {

        if (!m_context.magic_sets_for_queries()) {
            return nullptr;
        }
        SASSERT(source.contains(m_goal));
        SASSERT(source.get_predicate_rules(m_goal).size() == 1);

        app * goal_head = source.get_predicate_rules(m_goal)[0]->get_head();

        unsigned init_rule_cnt = source.get_num_rules();
        {
            func_decl_set intentional;
            for (unsigned i=0; i<init_rule_cnt; i++) {
                func_decl* pred = source.get_rule(i)->get_decl();
                intentional.insert(pred);
            }
            //now we iterate through all predicates and collect the set of extentional ones
            const rule_dependencies * deps;
            rule_dependencies computed_deps(m_context);
            if (source.is_closed()) {
                deps = &source.get_dependencies();
            }
            else {
                computed_deps.populate(source);
                deps = &computed_deps;
            }
            rule_dependencies::iterator it = deps->begin();
            rule_dependencies::iterator end = deps->end();
            for (; it!=end; ++it) {
                func_decl * pred = it->m_key;
                if (intentional.contains(pred)) {
                    continue;
                }
                SASSERT(it->m_value->empty());//extentional predicates have no dependency
                m_extentional.insert(pred);
            }
        }

        //adornment goal_adn;
        //goal_adn.populate(goal_head, );
        var_idx_set empty_var_idx_set;
        adorn_literal(goal_head, empty_var_idx_set);

        scoped_ptr<rule_set> result = alloc(rule_set, m_context);
        result->inherit_predicates(source);

        while (!m_todo.empty()) {
            adornment_desc task = m_todo.back();
            m_todo.pop_back();
            const rule_vector & pred_rules = source.get_predicate_rules(task.m_pred);
            rule_vector::const_iterator it = pred_rules.begin();
            rule_vector::const_iterator end = pred_rules.end();
            for (; it != end; ++it) {
                rule * r = *it;
                transform_rule(task.m_adornment, r, *result);
            }
            if (!m_context.get_rel_context()->is_empty_relation(task.m_pred)) {
                //we need a rule to copy facts that are already in a relation into the adorned
                //relation (since out intentional predicates can have facts, not only rules)
                create_transfer_rule(task, *result);
            }
        }

        app * adn_goal_head = adorn_literal(goal_head, empty_var_idx_set);
        app * mag_goal_head = create_magic_literal(adn_goal_head);
        SASSERT(mag_goal_head->is_ground());
        rule * mag_goal_rule = m_context.get_rule_manager().mk(mag_goal_head, 0, nullptr, nullptr);
        result->add_rule(mag_goal_rule);

        rule * back_to_goal_rule = m_context.get_rule_manager().mk(goal_head, 1, &adn_goal_head, nullptr);
        result->add_rule(back_to_goal_rule);
        return result.detach();
    }
};

