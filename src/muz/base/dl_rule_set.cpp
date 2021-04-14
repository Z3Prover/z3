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
#include "muz/base/dl_context.h"
#include "muz/base/dl_rule_set.h"
#include "ast/ast_pp.h"

namespace datalog {

    rule_dependencies::rule_dependencies(context& ctx): m_context(ctx) {
    }

    rule_dependencies::rule_dependencies(const rule_dependencies & o, bool reversed):
        m_context(o.m_context) {
        if (reversed) {
            for (auto & kv : o) {
                func_decl * pred = kv.m_key;
                item_set & orig_items = *kv.get_value();

                ensure_key(pred);
                for (func_decl * master_pred : orig_items) {
                    insert(master_pred, pred);
                }
            }
        }
        else {
            for (auto & kv : o) {
                func_decl * pred = kv.m_key;
                item_set & orig_items = *kv.get_value();
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
        auto& value = m_data.insert_if_not_there(pred, 0);
        if (!value) {
            value = alloc(item_set);
        }
        return *value;
    }

    void rule_dependencies::insert(func_decl * depending, func_decl * master) {
        SASSERT(m_data.contains(master)); //see m_data documentation
        item_set & s = ensure_key(depending);
        s.insert(master);
    }

    void rule_dependencies::populate(const rule_set & rules) {
        SASSERT(m_data.empty());
        for (auto & kv : rules.m_head2rules) {
            ptr_vector<rule> * rules = kv.m_value;
            for (rule* r : *rules) {
                populate(r);
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

    void rule_dependencies::restrict_dependencies(const item_set & allowed) {
        ptr_vector<func_decl> to_remove;
        for (auto const& kv : *this) {
            func_decl * pred = kv.m_key;
            if (!allowed.contains(pred)) {
                to_remove.insert(pred);
                continue;
            }
            item_set& itms = *kv.get_value();
            set_intersection(itms, allowed);
        }
        for (func_decl* f : to_remove)
            remove_m_data_entry(f);
    }

    void rule_dependencies::remove(func_decl * itm) {
        remove_m_data_entry(itm);
        for (auto const& kv : *this) 
            kv.get_value()->remove(itm);        
    }

    void rule_dependencies::remove(const item_set & to_remove) {
        for (auto * item : to_remove) {
            remove_m_data_entry(item);
        }
        for (auto & kv : *this) {
            item_set * itms = kv.get_value();
            set_difference(*itms, to_remove);
        }
    }

    unsigned rule_dependencies::out_degree(func_decl * f) const {
        unsigned res = 0;
        for (auto & kv : *this) {
            item_set & itms = *kv.get_value();
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

        for (auto& kv : *this) {
            func_decl * pred = kv.m_key;
            unsigned deg = in_degree(pred);
            if (deg == 0) {
                res.push_back(pred);
            }
            else {
                degs.insert(pred, deg);
            }
        }

        while (curr_index < res.size()) { //res.size() can change in the loop iteration
            func_decl * curr = res[curr_index];
            const item_set & children = reversed.get_deps(curr);
            for (func_decl * child : children) {
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

    void rule_dependencies::display(std::ostream & out ) const {
        for (auto const& kv : *this) {
            func_decl * pred = kv.m_key;
            const item_set & deps = *kv.m_value;
            if (deps.empty()) {
                out << pred->get_name()<<" - <none>\n";
            }
            for (func_decl* dep : deps) {
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
            m_stratifier(nullptr),
            m_refs(ctx.get_manager()) {
    }

    rule_set::rule_set(const rule_set & other)
        : m_context(other.m_context),
          m_rule_manager(other.m_rule_manager),
          m_rules(m_rule_manager),
          m_deps(other.m_context),
          m_stratifier(nullptr),
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
        m_stratifier = nullptr;
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
        for (auto & kv : other.m_orig2pred) {
            m_orig2pred.insert(kv.m_key, kv.m_value);
        }
        for (auto & kv : other.m_pred2orig) {
            m_pred2orig.insert(kv.m_key, kv.m_value);
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
        auto& value = m_head2rules.insert_if_not_there(d, 0);
        if (!value) value = alloc(ptr_vector<rule>);
        value->push_back(r);
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

    void rule_set::replace_rule(rule * r, rule * other) {
        TRACE("dl", r->display(m_context, tout << "replace:"););
        func_decl* d = r->get_decl();
        rule_vector* rules = m_head2rules.find(d);
#define REPLACE_VECTOR(_v)                              \
        for (unsigned i = (_v).size(); i > 0; ) {       \
            --i;                                        \
            if ((_v)[i] == r) {                         \
                (_v)[i] = other;                        \
                break;                                  \
            }                                           \
        }                                               \

        REPLACE_VECTOR(*rules);
        REPLACE_VECTOR(m_rules);
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
        if (!stratified_negation()) {
            m_stratifier = nullptr;
            m_deps.reset();
            return false;
        }
        return true;
    }

    void rule_set::reopen() {
        if (is_closed()) {
            m_stratifier = nullptr;
            m_deps.reset();
        }
    }

    /**
       \brief Return true if the negation is indeed stratified.
    */
    bool rule_set::stratified_negation() {
        ptr_vector<rule>::const_iterator it  = m_rules.data();
        ptr_vector<rule>::const_iterator end = m_rules.data() + m_rules.size();
        for (; it != end; it++) {
            rule * r = *it;
            func_decl * head_decl = r->get_decl();
            unsigned n = r->get_uninterpreted_tail_size();
            for (unsigned i = r->get_positive_tail_size(); i < n; i++) {
                SASSERT(r->is_neg_tail(i));
                func_decl * tail_decl = r->get_decl(i);
                unsigned neg_strat = get_predicate_strat(tail_decl);
                unsigned head_strat = get_predicate_strat(head_decl);

                SASSERT(head_strat >= neg_strat); // head strat can never be lower than that of a tail
                if (head_strat == neg_strat) {
                    return false;
                }
            }
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
            for (func_decl * f : non_founded) {
                rule_vector const& rv = get_predicate_rules(f);
                bool found = false;
                for (unsigned i = 0; !found && i < rv.size(); ++i) {
                    rule const& r = *rv[i];
                    bool is_founded = true;
                    for (unsigned j = 0; is_founded && j < r.get_uninterpreted_tail_size(); ++j) {
                        is_founded = founded.contains(r.get_decl(j));
                    }
                    if (is_founded) {
                        founded.insert(f);
                        non_founded.remove(f);
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
        for (func_decl * f : m_output_preds) {
            out << "; output: " << f->get_name() << '\n';
        }
        for (auto const& kv : m_head2rules) {
            ptr_vector<rule> * rules = kv.m_value;
            for (rule* r : *rules) {
                if (!r->passes_output_thresholds(m_context)) {
                    continue;
                }
                r->display(m_context, out);
            }
        }
    }

    bool rule_set::is_finite_domain() const {
        for (rule * r : *this) {
            if (!get_rule_manager().is_finite_domain(*r)) 
                return false;
        }
        return true;
    }


    void rule_set::display_deps( std::ostream & out ) const
    {
        const pred_set_vector & strats = get_strats();
        bool non_empty = false;
        for (func_decl_set* strat : strats) {
            if (non_empty) {
                out << "\n";
                non_empty = false;
            }

            for (func_decl * first : *strat) {
                const func_decl_set & deps = m_deps.get_deps(first);
                for (func_decl * dep : deps) {
                    non_empty = true;
                    out<<first->get_name()<<" -> " <<dep->get_name()<<"\n";
                }
            }
        }
    }

    // -----------------------------------
    //
    // rule_stratifier
    //
    // -----------------------------------

    rule_stratifier::~rule_stratifier() {
        for (auto * t : m_strats) {
            dealloc(t);
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
                unsigned on_stack_num = 0;
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
            for (T* ch : children) {
                traverse(ch);
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
        for (auto const& kv : m_deps) {
            T * el = kv.m_key;
            //we take a note of the preorder number with which this sweep started
            m_first_preorder = m_next_preorder;
            traverse(el);
        }

        //do topological sorting

        //degres of components (number of inter-component edges ending up in the component)
        svector<unsigned> in_degrees;
        in_degrees.resize(m_components.size());

        //init in_degrees
        for (auto const& kv : m_deps) {
            T * el = kv.m_key;
            item_set * out_edges = kv.m_value;

            unsigned el_comp = m_component_nums[el];

            for (T * tgt : *out_edges) {

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
            for (T * el : *comp) {
                const item_set & deps = m_deps.get_deps(el);
                for (T * tgt : deps) {
                    unsigned tgt_comp = 0;
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
                    traverse(el);
                }
            }
            strats_index++;
        }
        //we have managed to topologicaly order all the components

        //reverse the strats array, so that the only the later components would depend on earlier ones
        std::reverse(m_strats.begin(), m_strats.end());

        SASSERT(m_pred_strat_nums.empty());
        unsigned strat_cnt = m_strats.size();
        for (unsigned strat_index=0; strat_index < strat_cnt; strat_index++) {
            item_set * comp = m_strats[strat_index];
            for (T * el : *comp) {
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
        for (auto * s : m_strats) {
            for (auto * item : *s) {
                out << item->get_name() << " ";
            }
            out << "\n";
        }

    }

};
