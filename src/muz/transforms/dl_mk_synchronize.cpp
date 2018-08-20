/*++
Copyright (c) 2017-2018 Saint-Petersburg State University

Module Name:

    dl_mk_synchronize.h

Abstract:

    Rule transformer that attempts to merge recursive iterations
    relaxing the shape of the inductive invariant.

Author:

    Dmitry Mordvinov (dvvrd) 2017-05-24
    Lidiia Chernigovskaia (LChernigovskaya) 2017-10-20

Revision History:

--*/
#include "muz/transforms/dl_mk_synchronize.h"
#include <algorithm>

namespace datalog {

    typedef mk_synchronize::item_set_vector item_set_vector;

    mk_synchronize::mk_synchronize(context& ctx, unsigned priority):
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager())
    {}

    bool mk_synchronize::is_recursive(rule &r, func_decl &decl) const {
        func_decl *hdecl = r.get_head()->get_decl();
        // AG: shouldn't decl appear in the body?
        if (hdecl == &decl)  return true;
        auto & strata = m_stratifier->get_strats();
        unsigned num_of_stratum = m_stratifier->get_predicate_strat(hdecl);
        return strata[num_of_stratum]->contains(&decl);
    }

    bool mk_synchronize::has_recursive_premise(app * app) const {
        func_decl* app_decl = app->get_decl();
        if (m_deps->get_deps(app_decl).contains(app_decl)) {
            return true;
        }
        rule_stratifier::comp_vector const & strata = m_stratifier->get_strats();
        unsigned num_of_stratum = m_stratifier->get_predicate_strat(app_decl);
        return strata[num_of_stratum]->size() > 1;
    }

    item_set_vector mk_synchronize::add_merged_decls(ptr_vector<app> & apps) {
        unsigned sz = apps.size();
        item_set_vector merged_decls;
        merged_decls.resize(sz);
        auto & strata = m_stratifier->get_strats();
        for (unsigned j = 0; j < sz; ++j) {
            unsigned nos;
            nos = m_stratifier->get_predicate_strat(apps[j]->get_decl());
            merged_decls[j] = strata[nos];
        }
        return merged_decls;
    }

    void mk_synchronize::add_new_rel_symbols(unsigned idx,
                                             item_set_vector const & decls,
                                             ptr_vector<func_decl> & decls_buf,
                                             bool & was_added) {
        if (idx >= decls.size()) {
            string_buffer<> buffer;
            ptr_vector<sort> domain;
            for (auto &d : decls_buf) {
                buffer << d->get_name() << "!!";
                domain.append(d->get_arity(), d->get_domain());
            }

            symbol new_name = symbol(buffer.c_str());

            if (!m_cache.contains(new_name)) {
                was_added = true;
                func_decl* orig = decls_buf[0];
                func_decl* product_pred = m_ctx.mk_fresh_head_predicate(new_name,
                    symbol::null, domain.size(), domain.c_ptr(), orig);
                m_cache.insert(new_name, product_pred);
            }
            return;
        }

        // -- compute Cartesian product of decls, and create a new
        // -- predicate for each element of the product
        for (auto &p : *decls[idx]) {
            decls_buf[idx] = p;
            add_new_rel_symbols(idx + 1, decls, decls_buf, was_added);
        }
    }

    void mk_synchronize::replace_applications(rule & r, rule_set & rules,
                                              ptr_vector<app> & apps) {
        app_ref replacing = product_application(apps);

        ptr_vector<app> new_tail;
        svector<bool> new_tail_neg;
        unsigned n = r.get_tail_size() - apps.size() + 1;
        unsigned tail_idx = 0;
        new_tail.resize(n);
        new_tail_neg.resize(n);
        new_tail[0] = replacing;
        new_tail_neg[0] = false;

        for (unsigned i = 0; i < r.get_positive_tail_size(); ++i) {
            app* tail = r.get_tail(i);
            if (!apps.contains(tail)) {
                ++tail_idx;
                new_tail[tail_idx] = tail;
                new_tail_neg[tail_idx] = false;
            }
        }
        for (unsigned i = r.get_positive_tail_size(); i < r.get_uninterpreted_tail_size(); ++i) {
            ++tail_idx;
            new_tail[tail_idx] = r.get_tail(i);
            new_tail_neg[tail_idx] = true;
        }
        for (unsigned i = r.get_uninterpreted_tail_size(); i < r.get_tail_size(); ++i) {
            ++tail_idx;
            new_tail[tail_idx] = r.get_tail(i);
            new_tail_neg[tail_idx] = false;
        }

        rule_ref new_rule(rm);
        new_rule = rm.mk(r.get_head(), tail_idx + 1,
            new_tail.c_ptr(), new_tail_neg.c_ptr(), symbol::null, false);
        rules.replace_rule(&r, new_rule.get());
    }

    rule_ref mk_synchronize::rename_bound_vars_in_rule(rule * r,
                                                       unsigned & var_idx) {
        // AG: shift all variables in a rule so that lowest var index is var_idx?
        // AG: update var_idx in the process?
        ptr_vector<sort> sorts;
        r->get_vars(m, sorts);
        expr_ref_vector revsub(m);
        revsub.resize(sorts.size());
        for (unsigned i = 0; i < sorts.size(); ++i) {
            if (sorts[i]) {
                revsub[i] = m.mk_var(var_idx++, sorts[i]);
            }
        }

        rule_ref new_rule(rm);
        new_rule = rm.mk(r);
        rm.substitute(new_rule, revsub.size(), revsub.c_ptr());
        return new_rule;
    }

    vector<rule_ref_vector> mk_synchronize::rename_bound_vars(item_set_vector const & heads,
                                                              rule_set & rules) {
        // AG: is every item_set in heads corresponds to rules that are merged?
        // AG: why are bound variables renamed in the first place?
        // AG: the data structure seems too complex
        vector<rule_ref_vector> result;
        unsigned var_idx = 0;
        for (auto item : heads) {
            rule_ref_vector dst_vector(rm);
            for (auto *head : *item) {
                for (auto *r : rules.get_predicate_rules(head)) {
                    rule_ref new_rule = rename_bound_vars_in_rule(r, var_idx);
                    dst_vector.push_back(new_rule.get());
                }
            }
            result.push_back(dst_vector);
        }
        return result;
    }

    void mk_synchronize::add_rec_tail(vector< ptr_vector<app> > & recursive_calls,
                                      app_ref_vector & new_tail,
                                      svector<bool> & new_tail_neg,
                                      unsigned & tail_idx) {
        unsigned max_sz = 0;
        for (auto &rc : recursive_calls)
            max_sz= std::max(rc.size(), max_sz);

        unsigned n = recursive_calls.size();
        ptr_vector<app> merged_recursive_calls;

        for (unsigned j = 0; j < max_sz; ++j) {
            merged_recursive_calls.reset();
            merged_recursive_calls.resize(n);
            for (unsigned i = 0; i < n; ++i) {
                unsigned sz = recursive_calls[i].size();
                merged_recursive_calls[i] =
                    j < sz ? recursive_calls[i][j] : recursive_calls[i][sz - 1];
            }
            ++tail_idx;
            new_tail[tail_idx] = product_application(merged_recursive_calls);
            new_tail_neg[tail_idx] = false;
        }
    }

    void mk_synchronize::add_non_rec_tail(rule & r, app_ref_vector & new_tail,
                                          svector<bool> & new_tail_neg,
                                          unsigned & tail_idx) {
        for (unsigned i = 0, sz = r.get_positive_tail_size(); i < sz; ++i) {
            app* tail = r.get_tail(i);
            if (!is_recursive(r, *tail)) {
                ++tail_idx;
                new_tail[tail_idx] = tail;
                new_tail_neg[tail_idx] = false;
            }
        }
        for (unsigned i = r.get_positive_tail_size(),
                 sz = r.get_uninterpreted_tail_size() ; i < sz; ++i) {
            ++tail_idx;
            new_tail[tail_idx] = r.get_tail(i);
            new_tail_neg[tail_idx] = true;
        }
        for (unsigned i = r.get_uninterpreted_tail_size(),
                 sz = r.get_tail_size(); i < sz; ++i) {
            ++tail_idx;
            new_tail[tail_idx] = r.get_tail(i);
            new_tail_neg[tail_idx] = r.is_neg_tail(i);
        }
    }

    app_ref mk_synchronize::product_application(ptr_vector<app> const &apps) {
        unsigned args_num = 0;
        string_buffer<> buffer;

        // AG: factor out into mk_name
        for (auto *app : apps) {
            buffer << app->get_decl()->get_name() << "!!";
            args_num += app->get_num_args();
        }

        symbol name = symbol(buffer.c_str());
        SASSERT(m_cache.contains(name));
        func_decl * pred = m_cache[name];

        ptr_vector<expr> args;
        args.resize(args_num);
        unsigned idx = 0;
        for (auto *a : apps) {
            for (unsigned i = 0, sz = a->get_num_args(); i < sz; ++i, ++idx)
                args[idx] = a->get_arg(i);
        }

        return app_ref(m.mk_app(pred, args_num, args.c_ptr()), m);
    }

    rule_ref mk_synchronize::product_rule(rule_ref_vector const & rules) {
        unsigned n = rules.size();

        string_buffer<> buffer;
        bool first_rule = true;
        for (auto it = rules.begin(); it != rules.end(); ++it, first_rule = false) {
            if (!first_rule) {
                buffer << "+";
            }
            buffer << (*it)->name();
        }

        ptr_vector<app> heads;
        heads.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            heads[i] = rules[i]->get_head();
        }
        app_ref product_head = product_application(heads);
        unsigned product_tail_length = 0;
        bool has_recursion = false;
        vector< ptr_vector<app> > recursive_calls;
        recursive_calls.resize(n);
        for (unsigned i = 0; i < n; ++i) {
            rule& rule = *rules[i];
            product_tail_length += rule.get_tail_size();
            for (unsigned j = 0; j < rule.get_positive_tail_size(); ++j) {
                app* tail = rule.get_tail(j);
                if (is_recursive(rule, *tail)) {
                    has_recursion = true;
                    recursive_calls[i].push_back(tail);
                }
            }
            if (recursive_calls[i].empty()) {
                recursive_calls[i].push_back(rule.get_head());
            }
        }

        app_ref_vector new_tail(m);
        svector<bool> new_tail_neg;
        new_tail.resize(product_tail_length);
        new_tail_neg.resize(product_tail_length);
        unsigned tail_idx = -1;
        if (has_recursion) {
            add_rec_tail(recursive_calls, new_tail, new_tail_neg, tail_idx);
        }

        for (rule_vector::const_iterator it = rules.begin(); it != rules.end(); ++it) {
            rule& rule = **it;
            add_non_rec_tail(rule, new_tail, new_tail_neg, tail_idx);
        }

        rule_ref new_rule(rm);
        new_rule = rm.mk(product_head, tail_idx + 1,
            new_tail.c_ptr(), new_tail_neg.c_ptr(), symbol(buffer.c_str()), false);
        rm.fix_unbound_vars(new_rule, false);
        return new_rule;
    }

    void mk_synchronize::merge_rules(unsigned idx, rule_ref_vector & buf,
                                     vector<rule_ref_vector> const & merged_rules,
                                     rule_set & all_rules) {
        if (idx >= merged_rules.size()) {
            rule_ref product = product_rule(buf);
            all_rules.add_rule(product.get());
            return;
        }

        for (auto *r : merged_rules[idx]) {
            buf[idx] = r;
            merge_rules(idx + 1, buf, merged_rules, all_rules);
        }
    }

    void mk_synchronize::merge_applications(rule & r, rule_set & rules) {
        ptr_vector<app> non_recursive_preds;
        obj_hashtable<app> apps;
        for (unsigned i = 0; i < r.get_positive_tail_size(); ++i) {
            app* t = r.get_tail(i);
            if (!is_recursive(r, *t) && has_recursive_premise(t)) {
                apps.insert(t);
            }
        }
        if (apps.size() < 2) return;
        for (auto *a : apps) non_recursive_preds.push_back(a);

        item_set_vector merged_decls = add_merged_decls(non_recursive_preds);

        unsigned n = non_recursive_preds.size();
        ptr_vector<func_decl> decls_buf;
        decls_buf.resize(n);
        bool was_added = false;
        add_new_rel_symbols(0, merged_decls, decls_buf, was_added);
        if (was_added){
            rule_ref_vector rules_buf(rm);
            rules_buf.resize(n);
            vector<rule_ref_vector> renamed_rules = rename_bound_vars(merged_decls, rules);
            merge_rules(0, rules_buf, renamed_rules, rules);
        }

        replace_applications(r, rules, non_recursive_preds);
        m_deps->populate(rules);
        m_stratifier = alloc(rule_stratifier, *m_deps);
    }

    rule_set * mk_synchronize::operator()(rule_set const & source) {
        rule_set* rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);

        for (auto *r : source) { rules->add_rule(r); }

        m_deps = alloc(rule_dependencies, m_ctx);
        m_deps->populate(*rules);
        m_stratifier = alloc(rule_stratifier, *m_deps);

        unsigned current_rule = 0;
        while (current_rule < rules->get_num_rules()) {
            rule *r = rules->get_rule(current_rule);
            merge_applications(*r, *rules);
            ++current_rule;
        }

        return rules;
    }

};
