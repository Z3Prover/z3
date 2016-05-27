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
#include"dl_mk_simple_joins.h"
#include"dl_relation_manager.h"
#include"ast_pp.h"
#include"trace.h"


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
            unsigned    m_consumers;
            bool        m_stratified;
            unsigned    m_src_stratum;
        public:
            var_idx_set m_all_nonlocal_vars;
            rule_vector m_rules;

            pair_info() : m_consumers(0), m_stratified(true), m_src_stratum(0) {}

            bool can_be_joined() const {
                return m_consumers > 0;
            }

            cost get_cost() const { 
                SASSERT(m_consumers > 0);
                cost amortized = m_total_cost/m_consumers;
                if (m_stratified) {
                    return amortized * ( (amortized>0) ? (1/16.0f) : 16.0f);
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
                if (pl.m_rules_content.find(r).size()>2) {
                    m_consumers++;
                }
                if (m_stratified) {
                    unsigned head_stratum = pl.get_stratum(r->get_decl());
                    SASSERT(head_stratum>=m_src_stratum);
                    if (head_stratum==m_src_stratum) {
                        m_stratified = false;
                    }
                }
                idx_set_union(m_all_nonlocal_vars, non_local_vars_normalized);
            }
            /**
               \brief Remove rule from the pair record. Return true if no rules remain
               in the pair, and so it should be removed.
             */
            bool remove_rule(rule * r, unsigned original_length) {
                VERIFY( remove_from_vector(m_rules, r) );
                if (original_length>2) {
                    SASSERT(m_consumers>0);
                    m_consumers--;
                }
                SASSERT(!m_rules.empty() || m_consumers==0);
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
            : m_context(ctx), m(ctx.get_manager()), 
              rm(ctx.get_rule_manager()),
              m_var_subst(ctx.get_var_subst()),
              m_rs_aux_copy(rs_aux_copy), 
              m_introduced_rules(ctx.get_rule_manager()),
              m_modified_rules(false),
              m_pinned(ctx.get_manager())
        {
        }

        ~join_planner()
        {
            cost_map::iterator it  = m_costs.begin();
            cost_map::iterator end = m_costs.end();
            for (; it != end; ++it) {
                dealloc(it->m_value);
            }
            m_costs.reset();
        }
    private:

        void get_normalizer(app * t, unsigned & next_var, expr_ref_vector & result) const {
            SASSERT(result.size()>0);
            unsigned res_ofs = result.size()-1;
            unsigned n=t->get_num_args();
            for(unsigned i=0; i<n; i++) {
                SASSERT(is_var(t->get_arg(i)));
                var * v = to_var(t->get_arg(i));
                unsigned var_idx = v->get_idx();
                if (result[res_ofs-var_idx]==0) {
                    result[res_ofs-var_idx]=m.mk_var(next_var, v->get_sort());
                    next_var++;
                }
            }
        }

        void get_normalizer(app * t1, app * t2, expr_ref_vector & result) const {
            SASSERT(result.empty());
            if (t1->get_num_args()==0 && t2->get_num_args()==0) {
                return; //nothing to normalize
            }
            SASSERT(!t1->is_ground() || !t2->is_ground());

            unsigned max_var_idx = 0;
            {
                var_idx_set& orig_var_set = rm.collect_vars(t1, t2);
                var_idx_set::iterator ovit = orig_var_set.begin();
                var_idx_set::iterator ovend = orig_var_set.end();
                for(; ovit!=ovend; ++ovit) {
                    unsigned var_idx = *ovit;
                    if (var_idx>max_var_idx) {
                        max_var_idx = var_idx;
                    }
                }
            }

            if (t1->get_decl()!=t2->get_decl()) {
                if (t1->get_decl()->get_id()<t2->get_decl()->get_id()) {
                    std::swap(t1, t2);
                }
            }
            else {
                int_vector norm1(max_var_idx+1, -1);
                int_vector norm2(max_var_idx+1, -1);
                unsigned n=t1->get_num_args();
                SASSERT(n==t2->get_num_args());
                for(unsigned i=0; i<n; i++) {
                    //We assume that the mk_simple_joins transformer is applied after mk_filter_rules,
                    //so the only literals which appear in pairs are the ones that contain only variables.
                    var * v1 = to_var(t1->get_arg(i));
                    var * v2 = to_var(t2->get_arg(i));
                    if (v1->get_sort()!=v2->get_sort()) {
                        //different sorts mean we can distinguish the two terms
                        if (v1->get_sort()->get_id()<v2->get_sort()->get_id()) {
                            std::swap(t1, t2);
                        }
                        break;
                    }
                    unsigned v1_idx = v1->get_idx();
                    unsigned v2_idx = v2->get_idx();
                    //since the rules already went through the mk_filter_rules transformer, 
                    //variables must be linear
                    SASSERT(norm1[v1_idx]==-1);
                    SASSERT(norm2[v2_idx]==-1);

                    if (norm2[v1_idx]!=norm1[v2_idx]) {
                        //now we can distinguish the two terms
                        if (norm2[v1_idx]<norm1[v2_idx]) {
                            std::swap(t1, t2);
                        }
                        break;
                    }
                    norm1[v1_idx]=i;
                    norm2[v2_idx]=i;
                }
                //if we did not exit the loop prematurely, the two terms are indistinguishable,
                //so the order should not matter
            }

            result.resize(max_var_idx+1, static_cast<expr *>(0));
            unsigned next_var = 0;
            get_normalizer(t1, next_var, result);
            get_normalizer(t2, next_var, result);
        }

        app_pair get_key(app * t1, app * t2) {
            expr_ref_vector norm_subst(m);
            get_normalizer(t1, t2, norm_subst);
            expr_ref t1n_ref(m);
            expr_ref t2n_ref(m);
            m_var_subst(t1, norm_subst.size(), norm_subst.c_ptr(), t1n_ref);
            m_var_subst(t2, norm_subst.size(), norm_subst.c_ptr(), t2n_ref);
            app * t1n = to_app(t1n_ref);
            app * t2n = to_app(t2n_ref);
            if (t1n->get_id() > t2n->get_id()) {
                std::swap(t1n, t2n);
            }

            m_pinned.push_back(t1n);
            m_pinned.push_back(t2n);
            
            return app_pair(t1n, t2n);
        }

        /**
            \brief Add rule \c r among rules interested in predicate pair \c t1, \c t2.

            The \c m_rule_content entry of the rule \c r has to be properly filled in
            by the time of a call to this function
            */
        void register_pair(app * t1, app * t2, rule * r, const var_idx_set & non_local_vars) {
            SASSERT(t1!=t2);
            cost_map::entry * e = m_costs.insert_if_not_there2(get_key(t1, t2), 0);
            pair_info * & ptr_inf = e->get_data().m_value;
            if (ptr_inf==0) {
                ptr_inf = alloc(pair_info);
            }
            pair_info & inf = *ptr_inf;

            expr_ref_vector normalizer(m);
            get_normalizer(t1, t2, normalizer);
            unsigned norm_ofs = normalizer.size()-1;
            var_idx_set normalized_vars;
            var_idx_set::iterator vit  = non_local_vars.begin();
            var_idx_set::iterator vend = non_local_vars.end();
            for(; vit!=vend; ++vit) {
                unsigned norm_var = to_var(normalizer.get(norm_ofs-*vit))->get_idx();
                normalized_vars.insert(norm_var);
            }

            inf.add_rule(*this, t1, t2, r, normalized_vars, non_local_vars);
            TRACE("dl", tout << mk_pp(t1, m) << " " << mk_pp(t2, m) << " ";
                  vit = non_local_vars.begin();
                  for (; vit != vend; ++vit) tout << *vit << " ";
                  tout << "\n";
                  r->display(m_context, tout); 
                  if (inf.can_be_joined()) tout << "cost: " << inf.get_cost() << "\n";);

        }

        void remove_rule_from_pair(app_pair key, rule * r, unsigned original_len) {
            pair_info * ptr = 0;
            if (m_costs.find(key, ptr) && ptr &&
                ptr->remove_rule(r, original_len)) {
                SASSERT(ptr->m_rules.empty());
                m_costs.remove(key);
                dealloc(ptr);
            }
        }

        void register_rule(rule * r) {
            rule_counter counter;
            counter.count_rule_vars(r, 1);

            ptr_vector<app> & rule_content = 
                m_rules_content.insert_if_not_there2(r, ptr_vector<app>())->get_data().m_value;
            SASSERT(rule_content.empty());

            unsigned pos_tail_size=r->get_positive_tail_size();
            for(unsigned i=0; i<pos_tail_size; i++) {
                rule_content.push_back(r->get_tail(i));
            }
            for(unsigned i=0; i+1 < pos_tail_size; i++) {
                app * t1 = r->get_tail(i);
                var_idx_set t1_vars = rm.collect_vars(t1);
                counter.count_vars(t1, -1);  //temporarily remove t1 variables from counter
                for(unsigned j=i+1; j<pos_tail_size; j++) {
                    app * t2 = r->get_tail(j);
                    counter.count_vars(t2, -1);  //temporarily remove t2 variables from counter
                    var_idx_set scope_vars = rm.collect_vars(t2);
                    scope_vars |= t1_vars;
                    var_idx_set non_local_vars;
                    counter.collect_positive(non_local_vars);
                    counter.count_vars(t2, 1);  //restore t2 variables in counter
                    set_intersection(non_local_vars, scope_vars);
                    register_pair(t1, t2, r, non_local_vars);
                }
                counter.count_vars(t1, 1);  //restore t1 variables in counter
            }
        }

        bool extract_argument_info(unsigned var_idx, app * t, expr_ref_vector & args, 
                ptr_vector<sort> & domain) {
            unsigned n=t->get_num_args();
            for(unsigned i=0; i<n; i++) {
                var * v=to_var(t->get_arg(i));
                if (v->get_idx()==var_idx) {
                    args.push_back(v);
                    domain.push_back(m.get_sort(v));
                    return true;
                }
            }
            return false;
        }

        void join_pair(app_pair pair_key) {
            app * t1 = pair_key.first;
            app * t2 = pair_key.second;
            pair_info* infp = 0;
            if (!m_costs.find(pair_key, infp) || !infp) {
                UNREACHABLE();
                return;
            }            
            pair_info & inf = *infp;
            SASSERT(!inf.m_rules.empty());
            var_idx_set & output_vars = inf.m_all_nonlocal_vars;
            expr_ref_vector args(m);
            ptr_vector<sort> domain;

            unsigned arity = output_vars.num_elems();
            idx_set::iterator ovit=output_vars.begin();
            idx_set::iterator ovend=output_vars.end();
            //TODO: improve quadratic complexity
            for(;ovit!=ovend;++ovit) {
                unsigned var_idx=*ovit;

                bool found=extract_argument_info(var_idx, t1, args, domain);
                if (!found) {
                    found=extract_argument_info(var_idx, t2, args, domain);
                }
                SASSERT(found);
            }

            SASSERT(args.size()==arity);
            SASSERT(domain.size()==arity);

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
                symbol(parent_name.c_str()), symbol("split"), 
                arity, domain.c_ptr(), parent_head);

            app_ref head(m.mk_app(decl, arity, args.c_ptr()), m);

            app * tail[] = {t1, t2};

            rule * new_rule = m_context.get_rule_manager().mk(head, 2, tail, 0);

            //TODO: update accounting so that it can handle multiple parents
            new_rule->set_accounting_parent_object(m_context, one_parent);

            m_introduced_rules.push_back(new_rule);

            //here we copy the inf.m_rules vector because inf.m_rules will get changed 
            //in the iteration. Also we use hashtable instead of vector because we do 
            //not want to process one rule twice.

            rule_hashtable processed_rules;
            rule_vector rules(inf.m_rules);
            for (unsigned i = 0; i < rules.size(); ++i) {
                rule* r = rules[i];
                if (!processed_rules.contains(r)) {
                    apply_binary_rule(r, pair_key, head);
                    processed_rules.insert(r);
                }
            }
            // SASSERT(!m_costs.contains(pair_key));
        }

        void replace_edges(rule * r, const ptr_vector<app> & removed_tails, 
                const ptr_vector<app> & added_tails0, const ptr_vector<app> & rule_content) {
            SASSERT(removed_tails.size()>=added_tails0.size());
            unsigned len = rule_content.size();
            unsigned original_len = len+removed_tails.size()-added_tails0.size();
            ptr_vector<app> added_tails(added_tails0); //we need a copy since we'll be modifying it

            unsigned rt_sz = removed_tails.size();
            //remove edges between removed tails
            for(unsigned i=0; i<rt_sz; i++) {
                for(unsigned j=i+1; j<rt_sz; j++) {
                    app_pair pair_key = get_key(removed_tails[i], removed_tails[j]);
                    remove_rule_from_pair(pair_key, r, original_len);
                }
            }
            //remove edges between surviving tails and removed tails
            for(unsigned i=0; i<len; i++) {
                if (added_tails.contains(rule_content[i])) {
                    continue;
                }
                for(unsigned ri=0; ri<rt_sz; ri++) {
                    app_pair pair_key = get_key(rule_content[i], removed_tails[ri]);
                    remove_rule_from_pair(pair_key, r, original_len);
                }
            }

            if (len==1) {
                return;
            }

            app * head = r->get_head();

            var_counter counter;
            counter.count_vars(head, 1);

            unsigned tail_size=r->get_tail_size();
            unsigned pos_tail_size=r->get_positive_tail_size();

            for(unsigned i=pos_tail_size; i<tail_size; i++) {
                counter.count_vars(r->get_tail(i), 1);
            }
            for(unsigned i=0; i<len; i++) {
                counter.count_vars(rule_content[i], 1);
            }

            //add edges that contain added tails
            while(!added_tails.empty()) {
                app * a_tail = added_tails.back();  //added tail

                var_idx_set a_tail_vars = rm.collect_vars(a_tail);
                counter.count_vars(a_tail, -1);  //temporarily remove a_tail variables from counter

                for(unsigned i=0; i<len; i++) {
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
            if (len==1) {
                return;
            }

            func_decl * t1_pred = t1->get_decl();
            func_decl * t2_pred = t2->get_decl();
            ptr_vector<app> removed_tails;
            ptr_vector<app> added_tails;
            for(unsigned i1=0; i1<len; i1++) {
                app * rt1 = rule_content[i1];
                if (rt1->get_decl()!=t1_pred) {
                    continue;
                }
                unsigned i2start = (t1_pred==t2_pred) ? (i1+1) : 0;
                for(unsigned i2=i2start; i2<len; i2++) {
                    app * rt2 = rule_content[i2];
                    if (i1==i2 || rt2->get_decl()!=t2_pred) {
                        continue;
                    }
                    if (get_key(rt1, rt2)!=pair_key) {
                        continue;
                    }
                    expr_ref_vector normalizer(m);
                    get_normalizer(rt1, rt2, normalizer);
                    expr_ref_vector denormalizer(m);
                    reverse_renaming(m, normalizer, denormalizer);
                    expr_ref new_transf(m);
                    m_var_subst(t_new, denormalizer.size(), denormalizer.c_ptr(), new_transf);
                    app * new_lit = to_app(new_transf);

                    m_pinned.push_back(new_lit);
                    rule_content[i1]=new_lit;
                    rule_content[i2]=rule_content.back();
                    rule_content.pop_back();
                    len--;                                  //here the bound of both loops changes!!!
                    removed_tails.push_back(rt1);
                    removed_tails.push_back(rt2);
                    added_tails.push_back(new_lit);
                    //this exits the inner loop, the outer one continues in case there will 
                    //be other matches
                    break;
                }
            }
            SASSERT(!removed_tails.empty());
            SASSERT(!added_tails.empty());
            m_modified_rules = true;
            replace_edges(r, removed_tails, added_tails, rule_content);
        }

        cost get_domain_size(func_decl * pred, unsigned arg_index) const {
            relation_sort sort = pred->get_domain(arg_index);
            return static_cast<cost>(m_context.get_sort_size_estimate(sort));
            //unsigned sz;
            //if (!m_context.get_sort_size(sort, sz)) {
            //    sz=UINT_MAX;
            //}
            //return static_cast<cost>(sz);
        }

        unsigned get_stratum(func_decl * pred) const {
            return m_rs_aux_copy.get_predicate_strat(pred);
        }

        cost estimate_size(app * t) const {
            func_decl * pred = t->get_decl();
            unsigned n=pred->get_arity();
            rel_context_base* rel = m_context.get_rel_context();
            if (!rel) {
                return cost(1);
            }
            relation_manager& rm = rel->get_rmanager();
            if ( (m_context.saturation_was_run() && rm.try_get_relation(pred))
                || rm.is_saturated(pred)) {
                SASSERT(rm.try_get_relation(pred)); //if it is saturated, it should exist
                unsigned rel_size_int = rel->get_relation(pred).get_size_estimate_rows();
                if (rel_size_int!=0) {
                    cost rel_size = static_cast<cost>(rel_size_int);
                    cost curr_size = rel_size;
                    for(unsigned i=0; i<n; i++) {
                        if (!is_var(t->get_arg(i))) {
                            curr_size /= get_domain_size(pred, i);
                        }
                    }
                    return curr_size;
                }
            }
            cost res = 1;
            for(unsigned i=0; i<n; i++) {
                if (is_var(t->get_arg(i))) {
                    res *= get_domain_size(pred, i);
                }
            }
            return res;
        }

        cost compute_cost(app * t1, app * t2, const var_idx_set & non_local_vars) const {
            func_decl * t1_pred = t1->get_decl();
            func_decl * t2_pred = t2->get_decl();
            cost inters_size = 1;
            variable_intersection vi(m_context.get_manager());
            vi.populate(t1, t2);
            unsigned n = vi.size();
            // remove contributions from joined columns.
            for(unsigned i=0; i<n; i++) {
                unsigned arg_index1, arg_index2;
                vi.get(i, arg_index1, arg_index2);
                SASSERT(is_var(t1->get_arg(arg_index1)));
                if (non_local_vars.contains(to_var(t1->get_arg(arg_index1))->get_idx())) {
                    inters_size *= get_domain_size(t1_pred, arg_index1);
                }
                //joined arguments must have the same domain
                SASSERT(get_domain_size(t1_pred, arg_index1)==get_domain_size(t2_pred, arg_index2));
            }
            // remove contributions from projected columns.
            for (unsigned i = 0; i < t1->get_num_args(); ++i) {
                if (is_var(t1->get_arg(i)) && 
                    !non_local_vars.contains(to_var(t1->get_arg(i))->get_idx())) {
                    inters_size *= get_domain_size(t1_pred, i);
                }
            }
            for (unsigned i = 0; i < t2->get_num_args(); ++i) {
                if (is_var(t2->get_arg(i)) && 
                    !non_local_vars.contains(to_var(t2->get_arg(i))->get_idx())) {
                    inters_size *= get_domain_size(t2_pred, i);
                }
            }

            cost res = estimate_size(t1)*estimate_size(t2)/ inters_size; // (inters_size*inters_size);
            //cost res = -inters_size;

            /*unsigned t1_strat = get_stratum(t1_pred);
            SASSERT(t1_strat<=m_head_stratum);
            if (t1_strat<m_head_stratum) {
                unsigned t2_strat = get_stratum(t2_pred);
                SASSERT(t2_strat<=m_head_stratum);
                if (t2_strat<m_head_stratum) {
                    //the rule of this predicates would depend on predicates 
                    //in lower stratum than the head, which is a good thing, since
                    //then the rule code will not need to appear in a loop
                    if (res>0) {
                        res /= 2;
                    }
                    else {
                        res *= 2;
                    }
                }
            }*/

            TRACE("report_costs",                  
                  display_predicate(m_context, t1, tout);
                  display_predicate(m_context, t2, tout);
                  tout << res << "\n";);
            return res;
        }


        bool pick_best_pair(app_pair & p) {
            app_pair best;
            bool found = false;
            cost best_cost;

            cost_map::iterator it = m_costs.begin();
            cost_map::iterator end = m_costs.end();
            for(; it!=end; ++it) {
                app_pair key = it->m_key;
                pair_info & inf = *it->m_value;
                if (!inf.can_be_joined()) {
                    continue;
                }
                cost c = inf.get_cost();
                if (!found || c<best_cost) {
                    found = true;
                    best_cost = c;
                    best = key;
                }
            }
            if (!found) {
                return false;
            }
            p=best;
            return true;
        }


    public:
        rule_set * run(rule_set const & source) {

            unsigned num_rules = source.get_num_rules();
            for (unsigned i = 0; i < num_rules; i++) {
                register_rule(source.get_rule(i));
            }

            app_pair selected;
            while(pick_best_pair(selected)) {
                join_pair(selected);
            }

            if (!m_modified_rules) {
                return 0;
            }
            rule_set * result = alloc(rule_set, m_context);
            rule_pred_map::iterator rcit = m_rules_content.begin();
            rule_pred_map::iterator rcend = m_rules_content.end();
            for(; rcit!=rcend; ++rcit) {
                rule * orig_r = rcit->m_key;
                ptr_vector<app> content = rcit->m_value;
                SASSERT(content.size()<=2);
                if (content.size()==orig_r->get_positive_tail_size()) {
                    //rule did not change
                    result->add_rule(orig_r);
                    continue;
                }

                ptr_vector<app> tail(content);
                svector<bool> negs(tail.size(), false);
                unsigned or_len = orig_r->get_tail_size();
                for(unsigned i=orig_r->get_positive_tail_size(); i<or_len; i++) {
                    tail.push_back(orig_r->get_tail(i));
                    negs.push_back(orig_r->is_neg_tail(i));
                }

                rule * new_rule = m_context.get_rule_manager().mk(orig_r->get_head(), tail.size(), tail.c_ptr(), 
                    negs.c_ptr());

                new_rule->set_accounting_parent_object(m_context, orig_r);
                m_context.get_rule_manager().mk_rule_rewrite_proof(*orig_r, *new_rule);
                result->add_rule(new_rule);
            }
            while (!m_introduced_rules.empty()) {
                result->add_rule(m_introduced_rules.back());
                m_context.get_rule_manager().mk_rule_asserted_proof(*m_introduced_rules.back());
                m_introduced_rules.pop_back();
            }
            result->inherit_predicates(source);
            return result;
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

