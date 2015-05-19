/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_similarity_compressor.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-10-22.

Revision History:

--*/

#include<utility>
#include<sstream>
#include"dl_mk_similarity_compressor.h"
#include"dl_relation_manager.h"

namespace datalog {

    mk_similarity_compressor::mk_similarity_compressor(context & ctx) :
        plugin(5000),
        m_context(ctx),
        m_manager(ctx.get_manager()),
        m_threshold_count(ctx.similarity_compressor_threshold()),
        m_result_rules(ctx.get_rule_manager()),
        m_modified(false),
        m_pinned(m_manager) {
        SASSERT(m_threshold_count>1);
    }
    
    void mk_similarity_compressor::reset() {
        m_rules.reset();
        m_result_rules.reset();
        m_pinned.reset();
    }

    /**
       Allows to traverse head and positive tails in a single for loop starting from -1
     */
    static app * get_by_tail_index(rule * r, int idx) {
        if (idx < 0) {
            return r->get_head();
        }
        SASSERT(idx < static_cast<int>(r->get_positive_tail_size()));
        return r->get_tail(idx);
    }

    template<typename T>
    static int aux_compare(T a, T b) {
        return (a>b) ? 1 : ( (a==b) ? 0 : -1);
    }

    template<typename T>
    static int aux_compare(T* a, T* b);

    static int compare_var_args(app* t1, app* t2) {
        SASSERT(t1->get_num_args()==t2->get_num_args());
        int res;
        unsigned n = t1->get_num_args();
        for (unsigned i = 0; i < n; i++) {
            expr * a1 = t1->get_arg(i);
            expr * a2 = t2->get_arg(i);
            res = aux_compare(is_var(a1), is_var(a2));
            if (res != 0) { 
                return res; 
            }
            if (is_var(a1)) {
                res = aux_compare(to_var(a1)->get_idx(), to_var(a2)->get_idx());
                if (res != 0) { 
                    return res; 
                }
            }
        }
        return 0;
    }

    static int compare_args(app* t1, app* t2, int & skip_countdown) {
        SASSERT(t1->get_num_args()==t2->get_num_args());
        int res;
        unsigned n = t1->get_num_args();
        for (unsigned i=0; i<n; i++) {
            if (is_var(t1->get_arg(i))) {
                SASSERT(t1->get_arg(i) == t2->get_arg(i));
                continue;
            }
            if ((skip_countdown--) == 0) {
                continue;
            }
            res = aux_compare(t1->get_arg(i)->get_id(), t2->get_arg(i)->get_id());
            if (res!=0) { return res; }
        }
        return 0;
    }

    /**
       \brief Return 0 if r1 and r2 could be similar. If the rough similarity
       equaivelance class of r1 is greater than the one of r2, return 1; otherwise return -1.

       Two rules are in the same rough similarity class if they differ only in constant arguments
       of positive uninterpreted predicates.
     */
    static int rough_compare(rule * r1, rule * r2) {
        int res = aux_compare(r1->get_tail_size(), r2->get_tail_size());
        if (res!=0) { return res; }
        res = aux_compare(r1->get_uninterpreted_tail_size(), r2->get_uninterpreted_tail_size());
        if (res!=0) { return res; }
        res = aux_compare(r1->get_positive_tail_size(), r2->get_positive_tail_size());
        if (res!=0) { return res; }

        int pos_tail_sz = r1->get_positive_tail_size();
        for (int i=-1; i<pos_tail_sz; i++) {
            app * t1 = get_by_tail_index(r1, i);
            app * t2 = get_by_tail_index(r2, i);
            res = aux_compare(t1->get_decl()->get_id(), t2->get_decl()->get_id());
            if (res!=0) { return res; }
            res = compare_var_args(t1, t2);
            if (res!=0) { return res; }
        }

        unsigned tail_sz = r1->get_tail_size();
        for (unsigned i=pos_tail_sz; i<tail_sz; i++) {
            res = aux_compare(r1->get_tail(i)->get_id(), r2->get_tail(i)->get_id());
            if (res!=0) { return res; }
        }
        
        return 0;
    }

    /**
       \c r1 and \c r2 must be equal according to the \c rough_compare function for this function
       to be called.
     */
    static int total_compare(rule * r1, rule * r2, int skipped_arg_index = INT_MAX) {
        SASSERT(rough_compare(r1, r2)==0);
        int pos_tail_sz = r1->get_positive_tail_size();
        for (int i=-1; i<pos_tail_sz; i++) {
            int res = compare_args(get_by_tail_index(r1, i), get_by_tail_index(r2, i), skipped_arg_index);
            if (res!=0) { return res; }
        }
        return 0;
    }

    class const_info {
        int m_tail_index;
        unsigned m_arg_index;
        bool m_has_parent;
        /** Parent is a constant that appears earlier in the rule and has always the same value
            as this constant. */
        unsigned m_parent_index;
    public:

        const_info(int tail_index, unsigned arg_index) 
            : m_tail_index(tail_index), m_arg_index(arg_index), m_has_parent(false) {}

        int tail_index() const { return m_tail_index; }
        unsigned arg_index() const { return m_arg_index; }
        bool has_parent() const { return m_has_parent; }
        unsigned parent_index() const { SASSERT(has_parent()); return m_parent_index; }

        void set_parent_index(unsigned idx) { 
            SASSERT(!m_has_parent);
            m_has_parent = true;
            m_parent_index = idx;
        }
    };

    typedef svector<const_info> info_vector;

    static void collect_const_indexes(app * t, int tail_index, info_vector & res) {
        unsigned n = t->get_num_args();
        for (unsigned i=0; i<n; i++) {
            if (is_var(t->get_arg(i))) {
                continue;
            }
            res.push_back(const_info(tail_index, i));
        }
    }

    static void collect_const_indexes(rule * r, info_vector & res) {
        collect_const_indexes(r->get_head(), -1, res);
        unsigned pos_tail_sz = r->get_positive_tail_size();
        for (unsigned i=0; i<pos_tail_sz; i++) {
            collect_const_indexes(r->get_tail(i), i, res);
        }
    }

    template<class T>
    static void collect_orphan_consts(rule * r, const info_vector & const_infos, T & tgt) {
        unsigned const_cnt = const_infos.size();
        tgt.reset();
        for (unsigned i=0; i<const_cnt; i++) {
            const_info inf = const_infos[i];
            if (inf.has_parent()) {
                continue;
            }
            app * pred = get_by_tail_index(r, inf.tail_index());
            tgt.push_back(to_app(pred->get_arg(inf.arg_index())));
            SASSERT(tgt.back()->get_num_args()==0);
        }
    }
    template<class T>
    static void collect_orphan_sorts(rule * r, const info_vector & const_infos, T & tgt) {
        unsigned const_cnt = const_infos.size();
        tgt.reset();
        for (unsigned i=0; i<const_cnt; i++) {
            const_info inf = const_infos[i];
            if (inf.has_parent()) {
                continue;
            }
            app * pred = get_by_tail_index(r, inf.tail_index());
            tgt.push_back(pred->get_decl()->get_domain(inf.arg_index()));
        }
    }

    /**
       \brief From the \c tail_indexes and \c arg_indexes remove elements corresponding to constants
       that are the same in rules \c *first ... \c *(after_last-1).
     */
    static void remove_stable_constants(rule_vector::iterator first, rule_vector::iterator after_last, 
            info_vector & const_infos) {
        SASSERT(after_last-first>1);
        unsigned const_cnt = const_infos.size();
        ptr_vector<app> vals;
        rule * r = *(first++);
        collect_orphan_consts(r, const_infos, vals);
        SASSERT(vals.size()==const_cnt);
        rule_vector::iterator it = first;
        for (; it!=after_last; ++it) {
            for (unsigned i=0; i<const_cnt; i++) {
                app * pred = get_by_tail_index(*it, const_infos[i].tail_index());
                app * val = to_app(pred->get_arg(const_infos[i].arg_index()));
                if (vals[i]!=val) {
                    vals[i] = 0;
                }
            }
        }
        unsigned removed_cnt = 0;
        for (unsigned i=0; i<const_cnt; i++) {
            if (vals[i]!=0) {
                removed_cnt++;
            }
            else if (removed_cnt!=0) {
                const_infos[i-removed_cnt] = const_infos[i];
            }
        }
        if (removed_cnt!=0) {
            const_infos.shrink(const_cnt-removed_cnt);
        }
    }

    /**
       \brief When function returns, \c parents will contain for each constant the index of the
       first constant that is equal to it in all the rules. If there is no such, it will contain
       its own index.
     */
    static void detect_equal_constants(rule_vector::iterator first, rule_vector::iterator after_last, 
            info_vector & const_infos) {
        SASSERT(first!=after_last);
        unsigned const_cnt = const_infos.size();
        ptr_vector<app> vals;
        ptr_vector<sort> sorts;
        rule * r = *(first++);
        collect_orphan_consts(r, const_infos, vals);
        collect_orphan_sorts(r, const_infos, sorts);
        SASSERT(vals.size()==const_cnt);
        vector<unsigned_vector> possible_parents(const_cnt);
        for (unsigned i=1; i<const_cnt; i++) {
            for (unsigned j=0; j<i; j++) {
                if (vals[i]==vals[j] && sorts[i]==sorts[j]) {
                    possible_parents[i].push_back(j);
                }
            }
        }
        rule_vector::iterator it = first;
        for (; it!=after_last; ++it) {
            collect_orphan_consts(*it, const_infos, vals);
            for (unsigned i=1; i<const_cnt; i++) {
                unsigned_vector & ppars = possible_parents[i];
                unsigned j=0;
                while(j<ppars.size()) {
                    if (vals[i]!=vals[ppars[j]]) {
                        ppars[j] = ppars.back();
                        ppars.pop_back();
                    }
                    else {
                        j++;
                    }
                }
            }
        }
        for (unsigned i=0; i<const_cnt; i++) {
            unsigned parent = i;
            unsigned_vector & ppars = possible_parents[i];
            unsigned ppars_sz = ppars.size();
            for (unsigned j=0; j<ppars_sz; j++) {
                if (ppars[j]<parent) {
                    parent = ppars[j];
                }
            }
            if (parent!=i) {
                const_infos[i].set_parent_index(parent);
            }
        }
    }

    static unsigned get_constant_count(rule * r) {
        unsigned res = r->get_head()->get_num_args() - count_variable_arguments(r->get_head());
        unsigned pos_tail_sz = r->get_positive_tail_size();
        for (unsigned i=0; i<pos_tail_sz; i++) {
            res+= r->get_tail(i)->get_num_args() - count_variable_arguments(r->get_tail(i));
        }
        return res;
    }

    static bool initial_comparator(rule * r1, rule * r2) {
        int res = rough_compare(r1, r2);
        if (res!=0) { return res>0; }
        return total_compare(r1, r2)>0;
    }

    class arg_ignoring_comparator {
        unsigned m_ignored_index;
    public:
        arg_ignoring_comparator(unsigned ignored_index) : m_ignored_index(ignored_index) {}
        bool operator()(rule * r1, rule * r2) const {
            return total_compare(r1, r2, m_ignored_index)>0;
        }
        bool eq(rule * r1, rule * r2) const {
            return total_compare(r1, r2, m_ignored_index)==0;
        }
    };

    void mk_similarity_compressor::merge_class(rule_vector::iterator first, 
            rule_vector::iterator after_last) {
        SASSERT(after_last-first>1);
        info_vector const_infos;
        rule * r = *first; //an arbitrary representative of the class
        collect_const_indexes(r, const_infos);
        remove_stable_constants(first, after_last, const_infos);

        unsigned const_cnt = const_infos.size();
        SASSERT(const_cnt>0);

        detect_equal_constants(first, after_last, const_infos);


        //The aux relation contains column for each constant which does not have an earlier constant
        //that it is equal to (i.e. only has no parent)
        ptr_vector<sort> aux_domain;
        collect_orphan_sorts(r, const_infos, aux_domain);

        func_decl* head_pred = r->get_decl();
        symbol const& name_prefix = head_pred->get_name();
        std::string name_suffix = "sc_" + to_string(const_cnt);
        func_decl * aux_pred = m_context.mk_fresh_head_predicate(name_prefix, symbol(name_suffix.c_str()), 
            aux_domain.size(), aux_domain.c_ptr(), head_pred);
        m_pinned.push_back(aux_pred);

        relation_fact val_fact(m_manager, const_cnt);
        rule_vector::iterator it = first;
        for (; it!=after_last; ++it) {
            collect_orphan_consts(*it, const_infos, val_fact);
            m_context.add_fact(aux_pred, val_fact);
        }
        m_context.get_rel_context()->get_rmanager().mark_saturated(aux_pred);

        app * new_head = r->get_head();
        ptr_vector<app> new_tail;
        svector<bool> new_negs;
        unsigned tail_sz = r->get_tail_size();
        for (unsigned i=0; i<tail_sz; i++) {
            new_tail.push_back(r->get_tail(i));
            new_negs.push_back(r->is_neg_tail(i));
        }

        rule_counter ctr;
        ctr.count_rule_vars(r);
        unsigned max_var_idx, new_var_idx_base;
        if (ctr.get_max_positive(max_var_idx)) {
            new_var_idx_base = max_var_idx+1;
        }
        else {
            new_var_idx_base = 0;
        }

        ptr_vector<var> const_vars; //variables at indexes of their corresponding constants
        expr_ref_vector aux_vars(m_manager); //variables as arguments for the auxiliary predicate

        unsigned aux_column_index = 0;

        for (unsigned i=0; i<const_cnt; ) {
            int tail_idx = const_infos[i].tail_index();
            app * & mod_tail = (tail_idx==-1) ? new_head : new_tail[tail_idx];
            ptr_vector<expr> mod_args(mod_tail->get_num_args(), mod_tail->get_args());

            for (; i<const_cnt && const_infos[i].tail_index()==tail_idx; i++) { //here the outer loop counter is modified
                const_info & inf = const_infos[i];
                var * mod_var;
                if (!inf.has_parent()) {
                    mod_var = m_manager.mk_var(new_var_idx_base+aux_column_index, 
                        aux_domain[aux_column_index]);
                    aux_column_index++;
                    aux_vars.push_back(mod_var);
                }
                else {
                    mod_var = const_vars[inf.parent_index()];
                }
                const_vars.push_back(mod_var);
                mod_args[inf.arg_index()] = mod_var;
            }

            app * upd_tail = m_manager.mk_app(mod_tail->get_decl(), mod_args.c_ptr());
            m_pinned.push_back(upd_tail);
            mod_tail = upd_tail;
        }

        app_ref aux_tail(m_manager.mk_app(aux_pred, aux_vars.c_ptr()), m_manager);
        new_tail.push_back(aux_tail);
        new_negs.push_back(false);

        rule * new_rule = m_context.get_rule_manager().mk(new_head, new_tail.size(), new_tail.c_ptr(), 
            new_negs.c_ptr());
        m_result_rules.push_back(new_rule);

        //TODO: allow for a rule to have multiple parent objects
        new_rule->set_accounting_parent_object(m_context, r);
        m_modified = true;
    }

    void mk_similarity_compressor::process_class(rule_set const& source, rule_vector::iterator first, 
            rule_vector::iterator after_last) {
        SASSERT(first!=after_last);
        //remove duplicates
        {
            rule_vector::iterator it = first;
            rule_vector::iterator prev = it;
            ++it;
            while(it!=after_last) {
                if (it!=after_last && total_compare(*prev, *it)==0) {
                    --after_last;
                    std::swap(*it, *after_last);
                    m_modified = true;
                }
                else {
                    prev = it;
                    ++it;
                }
            }
        }
        SASSERT(first!=after_last);

        unsigned const_cnt = get_constant_count(*first);
#if 0
        for (unsigned ignored_index=0; ignored_index<const_cnt; ignored_index++) {
            arg_ignoring_comparator comparator(ignored_index);
            std::sort(first, after_last, comparator);

            rule_vector::iterator it = first;
            rule_vector::iterator grp_begin = it;
            unsigned grp_size=0;
            while(it!=after_last) {
                rule_vector::iterator prev = it;
                ++it;
                grp_size++;
                if (it==after_last || !comparator.eq(*prev, *it)) {
                    if (grp_size>m_threshold_count) {
                        merge_class(grp_begin, it);
                        //group was processed, so we remove it from the class
                        if (it==after_last) {
                            after_last=grp_begin;
                            it=after_last;
                        }
                        else {
                            while(it!=grp_begin) {
                                std::swap(*--it, *--after_last);
                            }
                        }
                    }
                    grp_begin = it;
                    grp_size = 0;
                }
            }
        }
#endif
        //TODO: compress also rules with pairs (or tuples) of equal constants

#if 1
        if (const_cnt>0 && !source.is_output_predicate((*first)->get_decl())) {
            unsigned rule_cnt = static_cast<unsigned>(after_last-first);
            if (rule_cnt>m_threshold_count) {
                merge_class(first, after_last);
                return;
            }
        }
#endif

        //put rules which weren't merged into result
        rule_vector::iterator it = first;
        for (; it!=after_last; ++it) {
            m_result_rules.push_back(*it);
        }
    }

    rule_set * mk_similarity_compressor::operator()(rule_set const & source) {
        // TODO mc
        m_modified = false;
        unsigned init_rule_cnt = source.get_num_rules();
        SASSERT(m_rules.empty());
        for (unsigned i=0; i<init_rule_cnt; i++) {
            m_rules.push_back(source.get_rule(i));
        }

        std::sort(m_rules.begin(), m_rules.end(), initial_comparator);

        rule_vector::iterator it = m_rules.begin();
        rule_vector::iterator end = m_rules.end();
        rule_vector::iterator cl_begin = it;
        while(it!=end) {
            rule_vector::iterator prev = it;
            ++it;
            if (it==end || rough_compare(*prev, *it)!=0) {
                process_class(source, cl_begin, it);
                cl_begin = it;
            }
        }

        rule_set * result = static_cast<rule_set *>(0);
        if (m_modified) {
            result = alloc(rule_set, m_context);
            unsigned fin_rule_cnt = m_result_rules.size();
            for (unsigned i=0; i<fin_rule_cnt; i++) {
                result->add_rule(m_result_rules.get(i));
            }
            result->inherit_predicates(source);
        }
        reset();
        return result;
    }
};
