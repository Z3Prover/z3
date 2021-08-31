/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_simple_joins.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder 2010-05-20.

Revision History:

--*/

#include<utility>
#include<sstream>
#include<limits>
#include "ast/ast_pp.h"
#include "util/trace.h"
#include "muz/rel/dl_mk_simple_joins.h"
#include "muz/rel/dl_relation_manager.h"


namespace datalog {

    mk_simple_joins::mk_simple_joins(context & ctx):
        plugin(1000),
        m_context(ctx),
        rm(ctx.get_rule_manager()) {
    }

    class join_planner {
        typedef float cost;

        class pair_info {
            cost m_total_cost;
            /**
               \brief Number of rules longer than two that contain this pair.

               This number is being updated by \c add_rule and \remove rule. Even though between
               adding a rule and removing it, the length of a rule can decrease without this pair
               being notified about it, it will surely see the decrease from length 3 to 2 which
               the threshold for rule being counted in this counter.
             */
            unsigned    m_consumers { 0 };
            bool        m_stratified { true };
            unsigned    m_src_stratum { 0 };
        public:
            var_idx_set m_all_nonlocal_vars;
            rule_vector m_rules;

            pair_info() {}

            bool can_be_joined() const {
                return m_consumers > 0;
            }

            cost get_cost() const { 
                SASSERT(m_consumers > 0);
                cost amortized = m_total_cost/m_consumers;
                if (m_stratified) {
                    return amortized * ( (amortized > 0) ? (1/16.0f) : 16.0f);
                }
                else {
                    return amortized;
                }
            }

            /**
               \brief Add rule \c r among rules interested in current predicate pair.

               The \c pl.m_rule_content entry of the rule has to be properly filled in
               by the time of a call to this function
             */
            void add_rule(join_planner & pl, app * t1, app * t2, rule * r, 
                          const var_idx_set & non_local_vars_normalized,
                          const var_idx_set & non_local_vars) {
                if (m_rules.empty()) {
                    m_total_cost = pl.compute_cost(t1, t2, non_local_vars);
                    m_src_stratum = std::max(pl.get_stratum(t1->get_decl()), pl.get_stratum(t2->get_decl()));
                }
                m_rules.push_back(r);
                if (pl.m_rules_content.find(r).size() > 2) {
                    m_consumers++;
                }
                if (m_stratified) {
                    unsigned head_stratum = pl.get_stratum(r->get_decl());
                    SASSERT(head_stratum >= m_src_stratum);
                    m_stratified = (head_stratum > m_src_stratum);
                }
                idx_set_union(m_all_nonlocal_vars, non_local_vars_normalized);
                TRACE("dl", tout << "all-nonlocal: " << m_all_nonlocal_vars << "\n";);
            }

            /**
               \brief Remove rule from the pair record. Return true if no rules remain
               in the pair, and so it should be removed.
             */
            bool remove_rule(rule * r, unsigned original_length) {
                VERIFY( remove_from_vector(m_rules, r) );
                if (original_length > 2) {
                    SASSERT(m_consumers > 0);
                    m_consumers--;
                }
                SASSERT(!m_rules.empty() || m_consumers == 0);
                return m_rules.empty();
            }
        private:
            pair_info & operator=(const pair_info &); //to avoid the implicit one
        };
        typedef std::pair<app*, app*> app_pair;
        typedef pair_hash<obj_ptr_hash<app>, obj_ptr_hash<app> > app_pair_hash;
        typedef map<app_pair, pair_info *, app_pair_hash, default_eq<app_pair> > cost_map;
        typedef map<rule *, ptr_vector<app>, ptr_hash<rule>, ptr_eq<rule> > rule_pred_map;
        typedef ptr_hashtable<rule, rule_hash_proc, default_eq<rule *> > rule_hashtable;

        context &       m_context;
        ast_manager &   m;
        rule_manager &  rm;
        var_subst &     m_var_subst;
        rule_set &      m_rs_aux_copy; //reference to a rule_set that will allow to ask for stratum levels

        cost_map          m_costs;
        ptr_vector<app>   m_interpreted;
        rule_pred_map     m_rules_content;
        rule_ref_vector   m_introduced_rules;
        bool              m_modified_rules;
        
        ast_ref_vector m_pinned;
        mutable ptr_vector<sort> m_vars;

    public:
        join_planner(context & ctx, rule_set & rs_aux_copy)
            : m_context(ctx), 
              m(ctx.get_manager()), 
              rm(ctx.get_rule_manager()),
              m_var_subst(ctx.get_var_subst()),
              m_rs_aux_copy(rs_aux_copy), 
              m_introduced_rules(rm),
              m_modified_rules(false),
              m_pinned(m)
        {
        }

        ~join_planner() {
            for (auto & kv : m_costs) {
                dealloc(kv.m_value);
            }
            m_costs.reset();
        }

    private:

        void get_normalizer(app * t, unsigned & next_var, var_ref_vector & result) const {
            SASSERT(!result.empty());
            unsigned res_ofs = result.size()-1;
            for (expr* arg : *t) {
                unsigned var_idx = to_var(arg)->get_idx();
                if (!result.get(res_ofs - var_idx)) {
                    result[res_ofs - var_idx] = m.mk_var(next_var++, arg->get_sort());
                }
            }
        }

        var_ref_vector get_normalizer(app * t1, app * t2) const {
            var_ref_vector result(m);
            if (t1->get_num_args() == 0 && t2->get_num_args() == 0) {
                return result; //nothing to normalize
            }
            SASSERT(!t1->is_ground() || !t2->is_ground());

            unsigned max_var_idx = 0;

            var_idx_set& orig_var_set = rm.collect_vars(t1, t2);
            for (unsigned var_idx : orig_var_set) {
                if (var_idx>max_var_idx) {
                    max_var_idx = var_idx;
                }
            }

            if (t1->get_decl() != t2->get_decl()) {
                if (t1->get_decl()->get_id() < t2->get_decl()->get_id()) {
                    std::swap(t1, t2);
                }
            }
            else {
                int_vector norm1(max_var_idx + 1, -1);
                int_vector norm2(max_var_idx + 1, -1);
                unsigned n = t1->get_num_args();
                SASSERT(n == t2->get_num_args());
                for (unsigned i = 0; i < n; ++i) {
                    //We assume that the mk_simple_joins transformer is applied after mk_filter_rules,
                    //so the only literals which appear in pairs are the ones that contain only variables.
                    var * v1 = to_var(t1->get_arg(i));
                    var * v2 = to_var(t2->get_arg(i));
                    if (v1->get_sort() != v2->get_sort()) {
                        //different sorts mean we can distinguish the two terms
                        if (v1->get_sort()->get_id() < v2->get_sort()->get_id()) {
                            std::swap(t1, t2);
                        }
                        break;
                    }
                    unsigned v1_idx = v1->get_idx();
                    unsigned v2_idx = v2->get_idx();
                    //since the rules already went through the mk_filter_rules transformer, 
                    //variables must be linear
                    SASSERT(norm1[v1_idx] == -1);
                    SASSERT(norm2[v2_idx] == -1);

                    if (norm2[v1_idx] != norm1[v2_idx]) {
                        //now we can distinguish the two terms
                        if (norm2[v1_idx] < norm1[v2_idx]) {
                            std::swap(t1, t2);
                        }
                        break;
                    }
                    norm1[v1_idx] = i;
                    norm2[v2_idx] = i;
                }
                //if we did not exit the loop prematurely, the two terms are indistinguishable,
                //so the order should not matter
            }

            result.resize(max_var_idx + 1, static_cast<var *>(nullptr));
            unsigned next_var = 0;
            get_normalizer(t1, next_var, result);
            get_normalizer(t2, next_var, result);
            return result;
        }


        app_pair get_key(app * t1, app * t2) {
            var_ref_vector norm_subst = get_normalizer(t1, t2);
            expr_ref t1n_ref = m_var_subst(t1, norm_subst);
            expr_ref t2n_ref = m_var_subst(t2, norm_subst);
            app * t1n = to_app(t1n_ref);
            app * t2n = to_app(t2n_ref);
            if (t1n->get_id() > t2n->get_id()) {
                std::swap(t1n, t2n);
            }

            m_pinned.push_back(t1n);
            m_pinned.push_back(t2n);
            TRACE("dl_verbose", tout << mk_pp(t1, m) << " " << mk_pp(t2, m) << " |-> " << t1n_ref << " " << t2n_ref << "\n";);
            
            return app_pair(t1n, t2n);
        }

        /**
            \brief Add rule \c r among rules interested in predicate pair \c t1, \c t2.

            The \c m_rule_content entry of the rule \c r has to be properly filled in
            by the time of a call to this function
            */
        void register_pair(app * t1, app * t2, rule * r, const var_idx_set & non_local_vars) {
            SASSERT (t1 != t2);
            pair_info * & ptr_inf = m_costs.insert_if_not_there(get_key(t1, t2), nullptr);
            if (ptr_inf == nullptr) {
                ptr_inf = alloc(pair_info);
            }
            pair_info & inf = *ptr_inf;

            var_ref_vector normalizer = get_normalizer(t1, t2);
            unsigned norm_ofs = normalizer.size()-1;
            var_idx_set normalized_vars;
            for (auto idx : non_local_vars) {
                unsigned norm_var = normalizer.get(norm_ofs - idx)->get_idx();
                normalized_vars.insert(norm_var);
            }

            inf.add_rule(*this, t1, t2, r, normalized_vars, non_local_vars);
            TRACE("dl", tout << mk_pp(t1, m) << " " << mk_pp(t2, m) << " ";
                  tout << non_local_vars << "\n";
                  r->display(m_context, tout); 
                  if (inf.can_be_joined()) tout << "cost: " << inf.get_cost() << "\n";);

        }

        void remove_rule_from_pair(app_pair key, rule * r, unsigned original_len) {
            pair_info * ptr = nullptr;
            if (m_costs.find(key, ptr) && ptr && ptr->remove_rule(r, original_len)) {
                SASSERT(ptr->m_rules.empty());
                m_costs.remove(key);
                dealloc(ptr);
            }
        }

        void register_rule(rule * r) {
            rule_counter counter;
            counter.count_rule_vars(r, 1);
            TRACE("dl", tout << "counter: "; for (auto const& kv: counter) tout << kv.m_key << ": " << kv.m_value << " "; tout << "\n";);            
            ptr_vector<app> & rule_content = m_rules_content.insert_if_not_there(r, ptr_vector<app>());
            SASSERT(rule_content.empty());
            
            TRACE("dl", r->display(m_context, tout << "register ");); 
            
            unsigned pos_tail_size = r->get_positive_tail_size();
            for (unsigned i = 0; i < pos_tail_size; i++) {
                app* t = r->get_tail(i);
                if (!rule_content.contains(t))
                    rule_content.push_back(t);
                else
                    m_modified_rules = true;
            }
            pos_tail_size = rule_content.size();
            for (unsigned i = 0; i+1 < pos_tail_size; i++) {
                app * t1 = rule_content[i];
                var_idx_set t1_vars = rm.collect_vars(t1);
                counter.count_vars(t1, -1);  //temporarily remove t1 variables from counter
                for (unsigned j = i+1; j < pos_tail_size; j++) {
                    app * t2 = rule_content[j];
                    SASSERT(t1 != t2);
                    counter.count_vars(t2, -1);  //temporarily remove t2 variables from counter
                    var_idx_set t2_vars = rm.collect_vars(t2);
                    t2_vars |= t1_vars;
                    var_idx_set non_local_vars;
                    counter.collect_positive(non_local_vars);
                    counter.count_vars(t2, 1);  //restore t2 variables in counter
                    set_intersection(non_local_vars, t2_vars);
                    TRACE("dl", tout << "non-local vars: " << non_local_vars << "\n";);
                    register_pair(t1, t2, r, non_local_vars);
                }
                counter.count_vars(t1, 1);  //restore t1 variables in counter
            }
        }

        bool extract_argument_info(unsigned var_idx, app * t, expr_ref_vector & args, 
                                   ptr_vector<sort> & domain) {
            for (expr* arg : *t) {
                var * v = to_var(arg);
                if (v->get_idx() == var_idx) {
                    args.push_back(v);
                    domain.push_back(v->get_sort());
                    return true;
                }
            }
            return false;
        }

        void join_pair(app_pair pair_key) {
            app * t1 = pair_key.first;
            app * t2 = pair_key.second;
            pair_info & inf = *m_costs[pair_key];
            SASSERT(!inf.m_rules.empty());
            var_idx_set const & output_vars = inf.m_all_nonlocal_vars;
            expr_ref_vector args(m);
            ptr_vector<sort> domain;

            unsigned arity = output_vars.num_elems();
            for (unsigned var_idx : output_vars) {
                bool found = extract_argument_info(var_idx, t1, args, domain);
                if (!found) {
                    found = extract_argument_info(var_idx, t2, args, domain);
                }
                SASSERT(found);
            }
            TRACE("dl", 
                  tout << mk_pp(t1, m) << " " << mk_pp(t2, m) << " arity: " << arity << "\n";
                  tout << "output: " << output_vars << "\n";
                  tout << "args:   " << args << "\n";);

            SASSERT(args.size() == arity);
            SASSERT(domain.size() == arity);

            rule * one_parent = inf.m_rules.back();

            func_decl* parent_head = one_parent->get_decl();
            const char * one_parent_name = parent_head->get_name().bare_str();
            std::string parent_name;
            if (inf.m_rules.size() > 1) {
                parent_name = one_parent_name + std::string("_and_") + to_string(inf.m_rules.size()-1);
            }
            else {
                parent_name = one_parent_name;
            }

            func_decl * decl = m_context.mk_fresh_head_predicate(
                symbol(parent_name), symbol("split"), 
                arity, domain.data(), parent_head);

            app_ref head(m.mk_app(decl, arity, args.data()), m);

            app * tail[] = { t1, t2 };

            rule * new_rule = rm.mk(head, 2, tail, nullptr);

            //TODO: update accounting so that it can handle multiple parents
            new_rule->set_accounting_parent_object(m_context, one_parent);

            m_introduced_rules.push_back(new_rule);

            //here we copy the inf.m_rules vector because inf.m_rules will get changed 
            //in the iteration. Also we use hashtable instead of vector because we do 
            //not want to process one rule twice.

            rule_hashtable processed_rules;
            rule_vector rules(inf.m_rules);
            for (rule * r : rules) {
                if (!processed_rules.contains(r)) {
                    apply_binary_rule(r, pair_key, head);
                    processed_rules.insert(r);
                }
            }
            // SASSERT(!m_costs.contains(pair_key));
        }

        void replace_edges(rule * r, const app_ref_vector & removed_tails, 
                           const app_ref_vector & added_tails0, const ptr_vector<app> & rule_content) {
            SASSERT(removed_tails.size() >= added_tails0.size());
            unsigned len = rule_content.size();
            unsigned original_len = len+removed_tails.size()-added_tails0.size();
            app_ref_vector added_tails(added_tails0); //we need a copy since we'll be modifying it
            TRACE("dl", tout << added_tails << "\n";);

            unsigned rt_sz = removed_tails.size();
            //remove edges between removed tails
            for (unsigned i = 0; i < rt_sz; i++) {
                for (unsigned j = i+1; j < rt_sz; j++) {
                    app_pair pair_key = get_key(removed_tails[i], removed_tails[j]);
                    remove_rule_from_pair(pair_key, r, original_len);
                }
            }
            //remove edges between surviving tails and removed tails
            for (unsigned i = 0; i < len; i++) {
                if (added_tails.contains(rule_content[i])) {
                    continue;
                }
                for (unsigned ri = 0; ri < rt_sz; ri++) {
                    app_pair pair_key = get_key(rule_content[i], removed_tails[ri]);
                    remove_rule_from_pair(pair_key, r, original_len);
                }
            }

            if (len == 1) {
                return;
            }

            app * head = r->get_head();

            var_counter counter;
            counter.count_vars(head, 1);

            unsigned tail_size = r->get_tail_size();
            unsigned pos_tail_size = r->get_positive_tail_size();

            for (unsigned i = pos_tail_size; i < tail_size; i++) {
                counter.count_vars(r->get_tail(i), 1);
            }
            for (unsigned i = 0; i < len; i++) {
                counter.count_vars(rule_content[i], 1);
            }

            //add edges that contain added tails
            while (!added_tails.empty()) {
                app * a_tail = added_tails.back();  //added tail
                
                TRACE("dl", tout << "replace edges " << mk_pp(a_tail, m) << "\n";);

                var_idx_set a_tail_vars = rm.collect_vars(a_tail);
                counter.count_vars(a_tail, -1);  //temporarily remove a_tail variables from counter

                for (unsigned i = 0; i < len; i++) {
                    app * o_tail = rule_content[i]; //other tail
                    if (added_tails.contains(o_tail)) {
                        //this avoids adding edges between new tails twice
                        continue;
                    }

                    counter.count_vars(o_tail, -1);  //temporarily remove o_tail variables from counter
                    var_idx_set scope_vars = rm.collect_vars(o_tail);
                    scope_vars |= a_tail_vars;
                    var_idx_set non_local_vars;
                    counter.collect_positive(non_local_vars);
                    counter.count_vars(o_tail, 1);  //restore o_tail variables in counter
                    set_intersection(non_local_vars, scope_vars);

                    register_pair(o_tail, a_tail, r, non_local_vars);
                }
                counter.count_vars(a_tail, 1);  //restore t1 variables in counter
                added_tails.pop_back();
            }
        }

        void apply_binary_rule(rule * r, app_pair pair_key, app * t_new) {
            app * t1 = pair_key.first;
            app * t2 = pair_key.second;
            ptr_vector<app> & rule_content = m_rules_content.find(r);
            unsigned len = rule_content.size();
            if (len == 1) {
                return;
            }
            TRACE("dl", 
                  tout << "pair: " << mk_pp(t1, m) << " " << mk_pp(t2, m) << "\n";
                  tout << mk_pp(t_new, m) << "\n";
                  tout << "all-non-local: " << m_costs[pair_key]->m_all_nonlocal_vars << "\n";
                  tout << mk_pp(r->get_head(), m) << " :-\n";
                  for (app* a : rule_content) tout << " " << mk_pp(a, m) << "\n";);

            rule_counter counter;
            for (app* t : rule_content)
                counter.count_vars(t, +1);
            counter.count_vars(r->get_head(), +1);

            func_decl * t1_pred = t1->get_decl();
            func_decl * t2_pred = t2->get_decl();
            app_ref_vector removed_tails(m);
            app_ref_vector added_tails(m);
            for (unsigned i1 = 0; i1 < len; i1++) {
                app * rt1 = rule_content[i1];
                if (rt1->get_decl() != t1_pred) {
                    continue;
                }
                var_idx_set rt1_vars = rm.collect_vars(rt1);
                counter.count_vars(rt1, -1);

                var_idx_set t1_vars = rm.collect_vars(t1);
                unsigned i2start = (t1_pred == t2_pred) ? (i1+1) : 0;
                for (unsigned i2 = i2start; i2 < len; i2++) {
                    app * rt2 = rule_content[i2];
                    if (i1 == i2 || rt2->get_decl() != t2_pred) {
                        continue;
                    }
                    if (get_key(rt1, rt2) != pair_key) {
                        continue;
                    }                    

                    var_ref_vector denormalizer(m);
                    var_ref_vector normalizer = get_normalizer(rt1, rt2);
                    reverse_renaming(normalizer, denormalizer);
                    expr_ref new_transf(m);
                    new_transf = m_var_subst(t_new, denormalizer);
                    TRACE("dl", tout  << mk_pp(rt1, m) << " " << mk_pp(rt2, m) << " -> " << new_transf << "\n";);            
                    counter.count_vars(rt2, -1);
                    var_idx_set rt2_vars = rm.collect_vars(rt2);
                    var_idx_set tr_vars = rm.collect_vars(new_transf);
                    rt2_vars |= rt1_vars;
                    var_idx_set non_local_vars;
                    counter.collect_positive(non_local_vars);
                    set_intersection(non_local_vars, rt2_vars);
                    counter.count_vars(rt2, +1);
                    // require that tr_vars contains non_local_vars
                    TRACE("dl", tout << "non-local : " << non_local_vars << " tr_vars " << tr_vars << " rt12_vars " << rt2_vars << "\n";);
                    if (!non_local_vars.subset_of(tr_vars)) {                        
                        var_ref_vector normalizer2 = get_normalizer(rt2, rt1);
                        TRACE("dl", tout << normalizer << "\nnorm\n" << normalizer2 << "\n";);
                        denormalizer.reset();
                        reverse_renaming(normalizer2, denormalizer);
                        new_transf = m_var_subst(t_new, denormalizer);
                        TRACE("dl", tout  << mk_pp(rt2, m) << " " << mk_pp(rt1, m) << " -> " << new_transf << "\n";);            
                        SASSERT(non_local_vars.subset_of(rm.collect_vars(new_transf)));
                    }
                    app * new_lit = to_app(new_transf);
                    if (added_tails.contains(new_lit)) {
                        if (i1 < i2)
                            std::swap(i1, i2);
                        if (i1 < rule_content.size()) 
                            rule_content[i1] = rule_content.back();
                        rule_content.pop_back();
                        if (i2 < rule_content.size()) 
                            rule_content[i2] = rule_content.back();
                        rule_content.pop_back();
                        len -= 2;
                        removed_tails.push_back(rt1);
                        removed_tails.push_back(rt2);
                        counter.count_vars(new_lit, -1);
                    }
                    else {
                        m_pinned.push_back(new_lit);
                        rule_content[i1] = new_lit;
                        rule_content[i2] = rule_content.back();
                        rule_content.pop_back();
                        len--;                                  //here the bound of both loops changes!!!
                        removed_tails.push_back(rt1);
                        removed_tails.push_back(rt2);
                        added_tails.push_back(new_lit);
                    }
                    // this exits the inner loop, the outer one continues in case there will 
                    // be other matches
                    break;
                }
                counter.count_vars(rt1, 1);
            }
            SASSERT(!removed_tails.empty());
            SASSERT(!added_tails.empty());
            m_modified_rules = true;
            TRACE("dl", tout << "replace rule content\n";);
            replace_edges(r, removed_tails, added_tails, rule_content);
        }


        cost get_domain_size(expr* e) const {
            return get_domain_size(e->get_sort());
        }

        cost get_domain_size(sort* s) const {
            return static_cast<cost>(m_context.get_sort_size_estimate(s));            
        }

        unsigned get_stratum(func_decl * pred) const {
            return m_rs_aux_copy.get_predicate_strat(pred);
        }

        cost estimate_size(app * t) const {
            rel_context_base* rel = m_context.get_rel_context();
            if (!rel) {
                return cost(1);
            }
            relation_manager& rm = rel->get_rmanager();
            func_decl * pred = t->get_decl();
            if ( (m_context.saturation_was_run() && rm.try_get_relation(pred)) || rm.is_saturated(pred)) {
                SASSERT(rm.try_get_relation(pred)); //if it is saturated, it should exist
                unsigned rel_size_int = rel->get_relation(pred).get_size_estimate_rows();
                if (rel_size_int != 0) {
                    cost curr_size = static_cast<cost>(rel_size_int);
                    for (expr* arg : *t) {
                        if (!is_var(arg)) {
                            curr_size /= get_domain_size(arg);
                        }
                    }
                    return curr_size;
                }
            }
            cost res = 1;
            for (expr* arg : *t) {
                if (is_var(arg))
                    res *= get_domain_size(arg);
            }
            return res;
        }

        cost compute_cost(app * t1, app * t2, const var_idx_set & non_local_vars) const {
            cost inters_size = 1;
            variable_intersection vi(m_context.get_manager());
            vi.populate(t1, t2);
            unsigned n = vi.size();
            // remove contributions from joined columns.
            for (unsigned i = 0; i < n; i++) {
                unsigned arg_index1, arg_index2;
                vi.get(i, arg_index1, arg_index2);
                expr* arg = t1->get_arg(arg_index1);
                SASSERT(is_var(arg));
                if (non_local_vars.contains(to_var(arg)->get_idx())) {
                    inters_size *= get_domain_size(arg);
                }
                // joined arguments must have the same domain
                SASSERT(get_domain_size(arg) == get_domain_size(t2->get_arg(arg_index2)));
            }
            // remove contributions from projected columns.
            for (expr* arg : *t1) {
                if (is_var(arg) && !non_local_vars.contains(to_var(arg)->get_idx())) {
                    inters_size *= get_domain_size(arg);
                }
            }
            for (expr* arg : *t2) {
                if (is_var(arg) && !non_local_vars.contains(to_var(arg)->get_idx())) {
                    inters_size *= get_domain_size(arg);
                }
            }

            cost res = (estimate_size(t1) * estimate_size(t2)) / inters_size; 

            TRACE("report_costs",                  
                  display_predicate(m_context, t1, tout);
                  display_predicate(m_context, t2, tout);
                  tout << res << "\n";);
            return res;
        }


        bool pick_best_pair(app_pair & p) {
            bool found = false;
            cost best_cost;
            for (auto const& kv : m_costs) {
                app_pair key = kv.m_key;
                pair_info & inf = *kv.m_value;
                if (!inf.can_be_joined()) {
                    continue;
                }
                cost c = inf.get_cost();
                if (!found || c < best_cost) {
                    found = true;
                    best_cost = c;
                    p = key;
                }
            }
            return found;
        }


    public:
        rule_set * run(rule_set const & source) {

            for (rule * r : source) {
                register_rule(r);
            }

            app_pair selected;
            while (pick_best_pair(selected)) {
                join_pair(selected);
            }

            if (!m_modified_rules) {
                return nullptr;
            }
            scoped_ptr<rule_set> result = alloc(rule_set, m_context);       
            for (auto& kv : m_rules_content) {
                rule * orig_r = kv.m_key;
                ptr_vector<app> const& content = kv.m_value;
                SASSERT(content.size() <= 2);
                if (content.size() == orig_r->get_positive_tail_size()) {
                    //rule did not change
                    result->add_rule(orig_r);
                    continue;
                }

                ptr_vector<app> tail(content);
                bool_vector negs(tail.size(), false);
                unsigned or_len = orig_r->get_tail_size();
                for (unsigned i = orig_r->get_positive_tail_size(); i < or_len; i++) {
                    tail.push_back(orig_r->get_tail(i));
                    negs.push_back(orig_r->is_neg_tail(i));
                }

                rule * new_rule = rm.mk(orig_r->get_head(), tail.size(), tail.data(), 
                    negs.data(), orig_r->name());

                new_rule->set_accounting_parent_object(m_context, orig_r);
                rm.mk_rule_rewrite_proof(*orig_r, *new_rule);
                result->add_rule(new_rule);
            }
            for (rule* r : m_introduced_rules) {
                result->add_rule(r);
                rm.mk_rule_asserted_proof(*r);
            }
            m_introduced_rules.reset();
            result->inherit_predicates(source);
            return result.detach();
        }
    };

    rule_set * mk_simple_joins::operator()(rule_set const & source) {
        rule_set rs_aux_copy(m_context);
        rs_aux_copy.replace_rules(source);
        if (!rs_aux_copy.is_closed()) {
            rs_aux_copy.close();
        }
        join_planner planner(m_context, rs_aux_copy);
        return planner.run(source);
    }


};

