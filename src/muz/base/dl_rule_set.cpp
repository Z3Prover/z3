/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_rule_set.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-17.

Revision History:

--*/

#include<algorithm>
#include<functional>
#include"dl_context.h"
#include"dl_rule_set.h"
#include"ast_pp.h"

namespace datalog {

    rule_dependencies::rule_dependencies(context& ctx): m_context(ctx) {
    }

    rule_dependencies::rule_dependencies(const rule_dependencies & o, bool reversed):
        m_context(o.m_context) {
        if (reversed) {
            iterator oit = o.begin();
            iterator oend = o.end();
            for (; oit!=oend; ++oit) {
                func_decl * pred = oit->m_key;
                item_set & orig_items = *oit->get_value();

                ensure_key(pred);
                item_set::iterator dit = orig_items.begin();
                item_set::iterator dend = orig_items.end();
                for (; dit!=dend; ++dit) {
                    func_decl * master_pred = *dit;
                    insert(master_pred, pred);
                }
            }
        }
        else {
            iterator oit = o.begin();
            iterator oend = o.end();
            for (; oit!=oend; ++oit) {
                func_decl * pred = oit->m_key;
                item_set & orig_items = *oit->get_value();
                m_data.insert(pred, alloc(item_set, orig_items));
            }
        }
    }

    rule_dependencies::~rule_dependencies() {
        reset();
    }
    void rule_dependencies::reset() {
        reset_dealloc_values(m_data);
    }

    void rule_dependencies::remove_m_data_entry(func_decl * key) {
        item_set * itm_set = m_data.find(key);
        dealloc(itm_set);
        m_data.remove(key);
    }

    rule_dependencies::item_set & rule_dependencies::ensure_key(func_decl * pred) {
        deps_type::obj_map_entry * e = m_data.insert_if_not_there2(pred, 0);
        if (!e->get_data().m_value) {
            e->get_data().m_value = alloc(item_set);
        }
        return *e->get_data().m_value;
    }

    void rule_dependencies::insert(func_decl * depending, func_decl * master) {
        SASSERT(m_data.contains(master)); //see m_data documentation
        item_set & s = ensure_key(depending);
        s.insert(master);
    }

    void rule_dependencies::populate(const rule_set & rules) {
        SASSERT(m_data.empty());
        rule_set::decl2rules::iterator it  = rules.m_head2rules.begin();
        rule_set::decl2rules::iterator end = rules.m_head2rules.end();
        for (; it != end; ++it) {
            ptr_vector<rule> * rules = it->m_value;
            ptr_vector<rule>::iterator it2  = rules->begin();
            ptr_vector<rule>::iterator end2 = rules->end();
            for (; it2 != end2; ++it2) {
                populate(*it2);
            }
        }
    }

    void rule_dependencies::populate(unsigned n, rule * const * rules) {
        SASSERT(m_data.empty());
        for (unsigned i=0; i<n; i++) {
            populate(rules[i]);
        }
    }

    void rule_dependencies::populate(rule const* r) {
        TRACE("dl_verbose", tout << r->get_decl()->get_name() << "\n";);
        m_visited.reset();
        func_decl * d = r->get_decl();
        func_decl_set & s = ensure_key(d);

        for (unsigned i = 0; i < r->get_tail_size(); ++i) {
            m_todo.push_back(r->get_tail(i));
        }
        while (!m_todo.empty()) {
            expr* e = m_todo.back();
            m_todo.pop_back();
            if (m_visited.is_marked(e)) {
                continue;
            }
            m_visited.mark(e, true);
            if (is_app(e)) {
                app* a = to_app(e);
                d = a->get_decl();
                if (m_context.is_predicate(d)) {
                    // insert d and ensure the invariant 
                    // that every predicate is present as 
                    // a key in m_data
                    s.insert(d);
                    ensure_key(d);
                }
                m_todo.append(a->get_num_args(), a->get_args());
            }
            else if (is_quantifier(e)) {
                m_todo.push_back(to_quantifier(e)->get_expr());
            }
        }
    }

    const rule_dependencies::item_set & rule_dependencies::get_deps(func_decl * f) const {
        deps_type::obj_map_entry * e = m_data.find_core(f);
        if (!e) {
            return m_empty_item_set;
        }
        SASSERT(e->get_data().get_value());
        return *e->get_data().get_value();
    }

    void rule_dependencies::restrict(const item_set & allowed) {
        ptr_vector<func_decl> to_remove;
        iterator pit = begin();
        iterator pend = end();
        for (; pit!=pend; ++pit) {
            func_decl * pred = pit->m_key;
            if (!allowed.contains(pred)) {
                to_remove.insert(pred);
                continue;
            }
            item_set& itms = *pit->get_value();
            set_intersection(itms, allowed);
        }
        ptr_vector<func_decl>::iterator rit = to_remove.begin();
        ptr_vector<func_decl>::iterator rend = to_remove.end();
        for (; rit != rend; ++rit) {
            remove_m_data_entry(*rit);
        }
    }

    void rule_dependencies::remove(func_decl * itm) {
        remove_m_data_entry(itm);
        iterator pit = begin();
        iterator pend = end();
        for (; pit != pend; ++pit) {
            item_set & itms = *pit->get_value();
            itms.remove(itm);
        }
    }

    void rule_dependencies::remove(const item_set & to_remove) {
        item_set::iterator rit = to_remove.begin();
        item_set::iterator rend = to_remove.end();
        for (; rit!=rend; ++rit) {
            remove_m_data_entry(*rit);
        }
        iterator pit = begin();
        iterator pend = end();
        for (; pit!=pend; ++pit) {
            item_set * itms = pit->get_value();
            set_difference(*itms, to_remove);
        }
    }

    unsigned rule_dependencies::out_degree(func_decl * f) const {
        unsigned res = 0;
        iterator pit = begin();
        iterator pend = end();
        for (; pit!=pend; ++pit) {
            item_set & itms = *pit->get_value();
            if (itms.contains(f)) {
                res++;
            }
        }
        return res;
    }

    bool rule_dependencies::sort_deps(ptr_vector<func_decl> & res) {
        typedef obj_map<func_decl, unsigned> deg_map;
        unsigned init_len = res.size();
        deg_map degs;
        unsigned curr_index = init_len;
        rule_dependencies reversed(*this, true);

        iterator pit = begin();
        iterator pend = end();
        for (; pit!=pend; ++pit) {
            func_decl * pred = pit->m_key;
            unsigned deg = in_degree(pred);
            if (deg==0) {
                res.push_back(pred);
            }
            else {
                degs.insert(pred, deg);
            }
        }

        while (curr_index<res.size()) { //res.size() can change in the loop iteration
            func_decl * curr = res[curr_index];
            const item_set & children = reversed.get_deps(curr);
            item_set::iterator cit = children.begin();
            item_set::iterator cend = children.end();
            for (; cit!=cend; ++cit) {
                func_decl * child = *cit;
                deg_map::obj_map_entry * e = degs.find_core(child);
                SASSERT(e);
                unsigned & child_deg = e->get_data().m_value;
                SASSERT(child_deg>0);
                child_deg--;
                if (child_deg==0) {
                    res.push_back(child);
                }
            }
            curr_index++;
        }
        if (res.size() < init_len + m_data.size()) {
            res.shrink(init_len);
            return false;
        }
        SASSERT(res.size()==init_len+m_data.size());
        return true;
    }

    void rule_dependencies::display(std::ostream & out ) const
    {
        iterator pit = begin();
        iterator pend = end();
        for (; pit != pend; ++pit) {
            func_decl * pred = pit->m_key;
            const item_set & deps = *pit->m_value;
            item_set::iterator dit=deps.begin();
            item_set::iterator dend=deps.end();
            if (dit == dend) {
                out<<pred->get_name()<<" - <none>\n";
            }
            for (; dit != dend; ++dit) {
                func_decl * dep = *dit;
                out << pred->get_name() << " -> " << dep->get_name() << "\n";
            }
        }
    }


    // -----------------------------------
    //
    // rule_set
    //
    // -----------------------------------

    rule_set::rule_set(context & ctx) 
          : m_context(ctx), 
            m_rule_manager(ctx.get_rule_manager()), 
            m_rules(m_rule_manager), 
            m_deps(ctx),
            m_stratifier(0), 
            m_refs(ctx.get_manager()) {
    }

    rule_set::rule_set(const rule_set & other) 
        : m_context(other.m_context), 
          m_rule_manager(other.m_rule_manager), 
          m_rules(m_rule_manager),
          m_deps(other.m_context),
          m_stratifier(0),
          m_refs(m_context.get_manager()) {
        add_rules(other);
        if (other.m_stratifier) {
            VERIFY(close());
        }
    }

    rule_set::~rule_set() {
        reset();
    }

    void rule_set::reset() {
        m_rules.reset();
        reset_dealloc_values(m_head2rules);
        m_deps.reset();
        m_stratifier = 0;
        m_output_preds.reset();
        m_orig2pred.reset();
        m_pred2orig.reset();
        m_refs.reset();
    }

    ast_manager & rule_set::get_manager() const {
        return m_context.get_manager();
    }

    func_decl* rule_set::get_orig(func_decl* pred) const {
        func_decl* orig = pred;
        m_pred2orig.find(pred, orig);
        return orig;
    }

    func_decl* rule_set::get_pred(func_decl* orig) const {
        func_decl* pred = orig;
        m_orig2pred.find(orig, pred);
        return pred;
    }

    void rule_set::inherit_predicates(rule_set const& other) {
        m_refs.append(other.m_refs);
        set_union(m_output_preds, other.m_output_preds);
        {
            obj_map<func_decl, func_decl*>::iterator it = other.m_orig2pred.begin();
            obj_map<func_decl, func_decl*>::iterator end = other.m_orig2pred.end();
            for (; it != end; ++it) {
                m_orig2pred.insert(it->m_key, it->m_value);
            }
        }
        {
            obj_map<func_decl, func_decl*>::iterator it = other.m_pred2orig.begin();
            obj_map<func_decl, func_decl*>::iterator end = other.m_pred2orig.end();
            for (; it != end; ++it) {
                m_pred2orig.insert(it->m_key, it->m_value);
            }
        }
    }

    void rule_set::inherit_predicate(rule_set const& other, func_decl* orig, func_decl* pred) {
        if (other.is_output_predicate(orig)) {
            set_output_predicate(pred);
        }
        orig = other.get_orig(orig);
        m_refs.push_back(pred);
        m_refs.push_back(orig);
        m_orig2pred.insert(orig, pred);
        m_pred2orig.insert(pred, orig);
    }

    void rule_set::add_rule(rule * r) {
        TRACE("dl_verbose", r->display(m_context, tout << "add:"););
        SASSERT(!is_closed());
        m_rules.push_back(r);
        app * head = r->get_head();
        SASSERT(head != 0);
        func_decl * d = head->get_decl();
        decl2rules::obj_map_entry* e = m_head2rules.insert_if_not_there2(d, 0);
        if (!e->get_data().m_value) e->get_data().m_value = alloc(ptr_vector<rule>);
        e->get_data().m_value->push_back(r);
    }

    void rule_set::del_rule(rule * r) {
        TRACE("dl", r->display(m_context, tout << "del:"););
        func_decl* d = r->get_decl();
        rule_vector* rules = m_head2rules.find(d);
#define DEL_VECTOR(_v)                                  \
        for (unsigned i = (_v).size(); i > 0; ) {       \
            --i;                                        \
            if ((_v)[i] == r) {                         \
                (_v)[i] = (_v).back();                  \
                (_v).pop_back();                        \
                break;                                  \
            }                                           \
        }                                               \
        
        DEL_VECTOR(*rules);
        DEL_VECTOR(m_rules);
    }    

    void rule_set::ensure_closed() {
        if (!is_closed()) {
            VERIFY(close());
        }
    }

    bool rule_set::close() {
        SASSERT(!is_closed()); //the rule_set is not already closed        
        m_deps.populate(*this);
        m_stratifier = alloc(rule_stratifier, m_deps);
        if (!stratified_negation() || !check_min()) {
            m_stratifier = 0;
            m_deps.reset();
            return false;
        }
        return true;
    }

    void rule_set::reopen() {
        if (is_closed()) {
            m_stratifier = 0;
            m_deps.reset();
        }
    }

    /**
       \brief Return true if the negation is indeed stratified.
    */
    bool rule_set::stratified_negation() {
        ptr_vector<rule>::const_iterator it  = m_rules.c_ptr();
        ptr_vector<rule>::const_iterator end = m_rules.c_ptr()+m_rules.size();
        for (; it != end; it++) {
            rule * r = *it;
            app * head = r->get_head();
            func_decl * head_decl = head->get_decl();
            unsigned n = r->get_uninterpreted_tail_size();
            for (unsigned i = r->get_positive_tail_size(); i < n; i++) {
                SASSERT(r->is_neg_tail(i));
                func_decl * tail_decl = r->get_tail(i)->get_decl();
                unsigned neg_strat = get_predicate_strat(tail_decl);
                unsigned head_strat = get_predicate_strat(head_decl);

                SASSERT(head_strat>=neg_strat); //head strat can never be lower than that of a tail
                if (head_strat == neg_strat) {
                    return false;
                }
            }
        }
        return true;
    }

    bool rule_set::check_min() {
        // For now, we check the following:
        //
        // if a min aggregation function occurs in an SCC, is this SCC
        // free of any other non-monotonic functions, e.g. negation?
        const unsigned NEG_BIT = 1U << 0;
        const unsigned MIN_BIT = 1U << 1;

        ptr_vector<rule>::const_iterator it = m_rules.c_ptr();
        ptr_vector<rule>::const_iterator end = m_rules.c_ptr() + m_rules.size();
        unsigned_vector component_status(m_stratifier->get_strats().size());

        for (; it != end; it++) {
            rule * r = *it;
            // app * head = r->get_head();
            // func_decl * head_decl = head->get_decl();
            // unsigned head_strat = get_predicate_strat(head_decl);
            unsigned n = r->get_tail_size();
            for (unsigned i = 0; i < n; i++) {
                func_decl * tail_decl = r->get_tail(i)->get_decl();
                unsigned strat = get_predicate_strat(tail_decl);

                if (r->is_neg_tail(i)) {
                    SASSERT(strat < component_status.size());
                    component_status[strat] |= NEG_BIT;
                }

                if (r->is_min_tail(i)) {
                    SASSERT(strat < component_status.size());
                    component_status[strat] |= MIN_BIT;
                }
            }
        }

        const unsigned CONFLICT = NEG_BIT | MIN_BIT;
        for (unsigned k = 0; k < component_status.size(); ++k) {
            if (component_status[k] == CONFLICT)
                return false;
        }

        return true;
    }

    void rule_set::replace_rules(const rule_set & src) {
        if (this != &src) {
            reset();
            add_rules(src);
        }
    }

    void rule_set::add_rules(const rule_set & src) {
        SASSERT(!is_closed());
        unsigned n = src.get_num_rules();
        for (unsigned i = 0; i < n; i++) {
            add_rule(src.get_rule(i));
        }
        inherit_predicates(src);
    }

    const rule_vector & rule_set::get_predicate_rules(func_decl * pred) const { 
        decl2rules::obj_map_entry * e = m_head2rules.find_core(pred);
        if (!e) {
            return m_empty_rule_vector;
        }
        return *e->get_data().m_value;
    }

    const rule_set::pred_set_vector & rule_set::get_strats() const {
        SASSERT(m_stratifier);
        return m_stratifier->get_strats();
    }

    unsigned rule_set::get_predicate_strat(func_decl * pred) const {
        SASSERT(m_stratifier);
        return m_stratifier->get_predicate_strat(pred);
    }

    void rule_set::split_founded_rules(func_decl_set& founded, func_decl_set& non_founded) {
        founded.reset();
        non_founded.reset();
        {
            decl2rules::iterator it = begin_grouped_rules(), end = end_grouped_rules();
            for (; it != end; ++it) {
                non_founded.insert(it->m_key);
            }
        }
        bool change = true;
        while (change) {
            change = false;
            func_decl_set::iterator it = non_founded.begin(), end = non_founded.end();
            for (; it != end; ++it) {
                rule_vector const& rv = get_predicate_rules(*it);
                bool found = false;
                for (unsigned i = 0; !found && i < rv.size(); ++i) {
                    rule const& r = *rv[i];
                    bool is_founded = true;
                    for (unsigned j = 0; is_founded && j < r.get_uninterpreted_tail_size(); ++j) {
                        is_founded = founded.contains(r.get_decl(j));
                    }
                    if (is_founded) {
                        founded.insert(*it);
                        non_founded.remove(*it);
                        change = true;
                        found  = true;
                    }
                }
            }
        }
    }

    void rule_set::display(std::ostream & out) const {
        out << "; rule count: " << get_num_rules() << "\n";
        out << "; predicate count: " << m_head2rules.size() << "\n";
        func_decl_set::iterator pit = m_output_preds.begin();
        func_decl_set::iterator pend = m_output_preds.end();
        for (; pit != pend; ++pit) {
            out << "; output: " << (*pit)->get_name() << '\n';
        }
        decl2rules::iterator it  = m_head2rules.begin();
        decl2rules::iterator end = m_head2rules.end();
        for (; it != end; ++it) {
            ptr_vector<rule> * rules = it->m_value;
            ptr_vector<rule>::iterator it2  = rules->begin();
            ptr_vector<rule>::iterator end2 = rules->end();
            for (; it2 != end2; ++it2) {
                rule * r = *it2;
                if (!r->passes_output_thresholds(m_context)) {
                    continue;
                }
                r->display(m_context, out);
            }
        }
    }


    void rule_set::display_deps( std::ostream & out ) const
    {
        const pred_set_vector & strats = get_strats();
        pred_set_vector::const_iterator sit = strats.begin();
        pred_set_vector::const_iterator send = strats.end();
        for (; sit!=send; ++sit) {
            func_decl_set & strat = **sit;
            func_decl_set::iterator fit=strat.begin();
            func_decl_set::iterator fend=strat.end();
            bool non_empty = false;
            for (; fit!=fend; ++fit) {
                func_decl * first = *fit;
                const func_decl_set & deps = m_deps.get_deps(first);
                func_decl_set::iterator dit=deps.begin();
                func_decl_set::iterator dend=deps.end();
                for (; dit!=dend; ++dit) {
                    non_empty = true;
                    func_decl * dep = *dit;
                    out<<first->get_name()<<" -> "<<dep->get_name()<<"\n";
                }
            }
            if (non_empty && sit!=send) {
                out << "\n";
            }
        }
    }

    // -----------------------------------
    //
    // rule_stratifier
    //
    // -----------------------------------

    rule_stratifier::~rule_stratifier() {
        comp_vector::iterator it = m_strats.begin();
        comp_vector::iterator end = m_strats.end();
        for (; it!=end; ++it) {
            SASSERT(*it);
            dealloc(*it);
        }
    }

    unsigned rule_stratifier::get_predicate_strat(func_decl * pred) const {
        unsigned num;
        if (!m_pred_strat_nums.find(pred, num)) {
            //the number of the predicate is not stored, therefore it did not appear 
            //in the algorithm and therefore it does not depend on anything and nothing 
            //depends on it. So it is safe to assign zero strate to it, although it is
            //not strictly true.
            num = 0;
        }
        return num;
    }


    void rule_stratifier::traverse(T* el) {
        unsigned p_num;
        if (m_preorder_nums.find(el, p_num)) {
            if (p_num < m_first_preorder) {
                //traversed in a previous sweep
                return;
            }
            if (m_component_nums.contains(el)) {
                //we already assigned a component for el
                return;
            }
            while (!m_stack_P.empty()) {
                unsigned on_stack_num;
                VERIFY( m_preorder_nums.find(m_stack_P.back(), on_stack_num) );
                if (on_stack_num <= p_num) {
                    break;
                }
                m_stack_P.pop_back();
            }
        }
        else {
            p_num=m_next_preorder++;
            m_preorder_nums.insert(el, p_num);

            m_stack_S.push_back(el);
            m_stack_P.push_back(el);

            const item_set & children = m_deps.get_deps(el);
            item_set::iterator cit=children.begin();
            item_set::iterator cend=children.end();
            for (; cit!=cend; ++cit) {
                traverse(*cit);
            }

            if (el == m_stack_P.back()) {
                unsigned comp_num = m_components.size();
                item_set * new_comp = alloc(item_set);
                m_components.push_back(new_comp);

                T* s_el;
                do {
                    s_el=m_stack_S.back();
                    m_stack_S.pop_back();
                    new_comp->insert(s_el);
                    m_component_nums.insert(s_el, comp_num);
                } while (s_el!=el);
                m_stack_P.pop_back();
            }
        }
    }

    void rule_stratifier::process() {
        if (m_deps.empty()) {
            return;
        }

        //detect strong components
        rule_dependencies::iterator it = m_deps.begin();
        rule_dependencies::iterator end = m_deps.end();
        for (; it!=end; ++it) {
            T * el = it->m_key;
            //we take a note of the preorder number with which this sweep started
            m_first_preorder = m_next_preorder;
            traverse(el);
        }

        //do topological sorting

        //degres of components (number of inter-component edges ending up in the component)
        svector<unsigned> in_degrees;
        in_degrees.resize(m_components.size());

        //init in_degrees
        it = m_deps.begin();
        end = m_deps.end();
        for (; it != end; ++it) {
            T * el = it->m_key;
            item_set * out_edges = it->m_value;

            unsigned el_comp;
            VERIFY( m_component_nums.find(el, el_comp) );

            item_set::iterator eit = out_edges->begin();
            item_set::iterator eend = out_edges->end();
            for (; eit!=eend; ++eit) {
                T * tgt = *eit;

                unsigned tgt_comp = m_component_nums.find(tgt);

                if (el_comp != tgt_comp) {
                    in_degrees[tgt_comp]++;
                }
            }
        }


        // We put components whose indegree is zero to m_strats and assign its 
        // m_components entry to zero.
        unsigned comp_cnt = m_components.size();
        for (unsigned i = 0; i < comp_cnt; i++) {
            if (in_degrees[i] == 0) {
                m_strats.push_back(m_components[i]);
                m_components[i] = 0;
            }
        }

        SASSERT(!m_strats.empty()); //the component graph is acyclic and non-empty

        //we remove edges from components with zero indegre building the topological ordering
        unsigned strats_index = 0;
        while (strats_index < m_strats.size()) { //m_strats.size() changes inside the loop!
            item_set * comp = m_strats[strats_index];
            item_set::iterator cit=comp->begin();
            item_set::iterator cend=comp->end();
            for (; cit!=cend; ++cit) {
                T * el = *cit;
                const item_set & deps = m_deps.get_deps(el);
                item_set::iterator eit=deps.begin();
                item_set::iterator eend=deps.end();
                for (; eit!=eend; ++eit) {
                    T * tgt = *eit;
                    unsigned tgt_comp;
                    VERIFY( m_component_nums.find(tgt, tgt_comp) );

                    //m_components[tgt_comp]==0 means the edge is intra-component.
                    //Otherwise it would go to another component, but it is not possible, since
                    //as m_components[tgt_comp]==0, its indegree has already reached zero.
                    if (m_components[tgt_comp]) {
                        SASSERT(in_degrees[tgt_comp]>0);
                        in_degrees[tgt_comp]--;
                        if (in_degrees[tgt_comp]==0) {
                            m_strats.push_back(m_components[tgt_comp]);
                            m_components[tgt_comp] = 0;
                        }
                    }
                    traverse(*cit);
                }
            }
            strats_index++;
        }
        //we have managed to topologicaly order all the components
        SASSERT(std::find_if(m_components.begin(), m_components.end(), 
            std::bind1st(std::not_equal_to<item_set*>(), (item_set*)0)) == m_components.end());

        //reverse the strats array, so that the only the later components would depend on earlier ones
        std::reverse(m_strats.begin(), m_strats.end());

        SASSERT(m_pred_strat_nums.empty());
        unsigned strat_cnt = m_strats.size();
        for (unsigned strat_index=0; strat_index<strat_cnt; strat_index++) {
            item_set * comp = m_strats[strat_index];
            item_set::iterator cit=comp->begin();
            item_set::iterator cend=comp->end();
            for (; cit != cend; ++cit) {
                T * el = *cit;
                m_pred_strat_nums.insert(el, strat_index);
            }
        }

        //finalize structures that are not needed anymore
        m_preorder_nums.finalize();
        m_stack_S.finalize();
        m_stack_P.finalize();
        m_component_nums.finalize();
        m_components.finalize();

    }

    void rule_stratifier::display(std::ostream& out) const {
        m_deps.display(out << "dependencies\n");
        out << "strata\n";
        for (unsigned i = 0; i < m_strats.size(); ++i) {
            item_set::iterator it  = m_strats[i]->begin();
            item_set::iterator end = m_strats[i]->end();            
            for (; it != end; ++it) {
                out << (*it)->get_name() << " ";
            }
            out << "\n";
        }
        
    }

};
