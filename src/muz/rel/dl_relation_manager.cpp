/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_relation_manager.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-14.

Revision History:

--*/


#include <sstream>
#include"ast_pp.h"
#include"dl_check_table.h"
#include"dl_context.h"
#include"dl_finite_product_relation.h"
#include"dl_product_relation.h"
#include"dl_sieve_relation.h"
#include"dl_table_relation.h"
#include"dl_relation_manager.h"

namespace datalog {

    relation_manager::~relation_manager() {
        reset();
    }


    void relation_manager::reset_relations() {
        relation_map::iterator it=m_relations.begin();
        relation_map::iterator end=m_relations.end();
        for(;it!=end;++it) {
            func_decl * pred = it->m_key;
            get_context().get_manager().dec_ref(pred); //inc_ref in get_relation
            relation_base * r=(*it).m_value;
            r->deallocate();
        }
        m_relations.reset();
    }

    void relation_manager::reset() {
        reset_relations();

        m_favourite_table_plugin   = static_cast<table_plugin *>(0);
        m_favourite_relation_plugin = static_cast<relation_plugin *>(0);
        dealloc_ptr_vector_content(m_table_plugins);
        m_table_plugins.reset();
        dealloc_ptr_vector_content(m_relation_plugins);
        m_relation_plugins.reset();
        m_next_table_fid = 0;
        m_next_relation_fid = 0;
    }

    dl_decl_util & relation_manager::get_decl_util() const {
        return get_context().get_decl_util();
    }

    family_id relation_manager::get_next_relation_fid(relation_plugin & claimer) { 
        unsigned res = m_next_relation_fid++;
        m_kind2plugin.insert(res, &claimer);
        return res;
    }

    void relation_manager::set_predicate_kind(func_decl * pred, family_id kind) {
        SASSERT(!m_relations.contains(pred));
        m_pred_kinds.insert(pred, kind);
    }

    family_id relation_manager::get_requested_predicate_kind(func_decl * pred) {
        family_id res;
        if(m_pred_kinds.find(pred, res)) {
            return res;
        }
        else {
            return null_family_id;
        }
    }

    relation_base & relation_manager::get_relation(func_decl * pred) {
        relation_base * res = try_get_relation(pred);
        if(!res) {
            relation_signature sig;
            from_predicate(pred, sig);
            family_id rel_kind = get_requested_predicate_kind(pred);
            res = mk_empty_relation(sig, rel_kind);
            store_relation(pred, res);
        }
        return *res;
    }

    relation_base * relation_manager::try_get_relation(func_decl * pred) const {
        relation_base * res = 0;
        if(!m_relations.find(pred, res)) {
            return 0;
        }
        SASSERT(res);
        return res;
    }

    void relation_manager::store_relation(func_decl * pred, relation_base * rel) {
        SASSERT(rel);
        relation_map::obj_map_entry * e = m_relations.insert_if_not_there2(pred, 0);
        if (e->get_data().m_value) {
            e->get_data().m_value->deallocate();
        }
        else {
            get_context().get_manager().inc_ref(pred); //dec_ref in reset
        }
        e->get_data().m_value = rel;
    }

    void relation_manager::collect_non_empty_predicates(decl_set & res) const {
        relation_map::iterator it = m_relations.begin();
        relation_map::iterator end = m_relations.end();
        for(; it!=end; ++it) {
            if(!it->m_value->fast_empty()) {
                res.insert(it->m_key);
            }
        }
    }

    void relation_manager::restrict_predicates(const decl_set & preds) {
        typedef ptr_vector<func_decl> fd_vector;
        fd_vector to_remove;

        relation_map::iterator rit = m_relations.begin();
        relation_map::iterator rend = m_relations.end();
        for(; rit!=rend; ++rit) {
            func_decl * pred = rit->m_key;
            if (!preds.contains(pred)) {
                to_remove.insert(pred);
            }
        }

        fd_vector::iterator pit = to_remove.begin();
        fd_vector::iterator pend = to_remove.end();
        for(; pit!=pend; ++pit) {
            func_decl * pred = *pit;
            relation_base * rel;
            VERIFY( m_relations.find(pred, rel) );
            rel->deallocate();
            m_relations.remove(pred);
            get_context().get_manager().dec_ref(pred);
        }

        set_intersection(m_saturated_rels, preds);
    }

    void relation_manager::register_plugin(table_plugin * plugin) {
        plugin->initialize(get_next_table_fid());
        m_table_plugins.push_back(plugin);

        if(plugin->get_name()==get_context().default_table()) {
            m_favourite_table_plugin = plugin;
        }

        table_relation_plugin * tr_plugin = alloc(table_relation_plugin, *plugin, *this);
        register_relation_plugin_impl(tr_plugin);
        m_table_relation_plugins.insert(plugin, tr_plugin);

        if (plugin->get_name()==get_context().default_table()) {
            m_favourite_table_plugin    = plugin;
            m_favourite_relation_plugin = tr_plugin;
        }

        symbol checker_name = get_context().default_table_checker();
        if (get_context().default_table_checked() && get_table_plugin(checker_name)) {
            if( m_favourite_table_plugin &&
                (plugin==m_favourite_table_plugin || plugin->get_name()==checker_name) ) {
                symbol checked_name = get_context().default_table();
                //the plugins we need to create the checking plugin were just added
                SASSERT(m_favourite_table_plugin->get_name()==get_context().default_table());
                table_plugin * checking_plugin = alloc(check_table_plugin, *this, checker_name, checked_name);
                register_plugin(checking_plugin);
                m_favourite_table_plugin = checking_plugin;
            }
            if (m_favourite_relation_plugin && m_favourite_relation_plugin->from_table()) {
                table_relation_plugin * fav_rel_plugin = 
                    static_cast<table_relation_plugin *>(m_favourite_relation_plugin);
                if(&fav_rel_plugin->get_table_plugin()==plugin || plugin->get_name()==checker_name) {
                    //the plugins we need to create the checking table_relation_plugin were just added
                    SASSERT(m_favourite_relation_plugin->get_name() == 
                        get_context().default_relation());
                    symbol checked_name = fav_rel_plugin->get_table_plugin().get_name();
                    table_plugin * checking_plugin = alloc(check_table_plugin, *this, checker_name, checked_name);
                    register_plugin(checking_plugin);

                    table_relation_plugin * checking_tr_plugin = 
                        alloc(table_relation_plugin, *checking_plugin, *this);
                    register_relation_plugin_impl(checking_tr_plugin);
                    m_table_relation_plugins.insert(checking_plugin, checking_tr_plugin);
                    m_favourite_relation_plugin = checking_tr_plugin;
                }
            }
        }

    }

    void relation_manager::register_relation_plugin_impl(relation_plugin * plugin) {
        TRACE("dl", tout << "register: " << plugin->get_name() << "\n";);
        m_relation_plugins.push_back(plugin);
        plugin->initialize(get_next_relation_fid(*plugin));
        if (plugin->get_name() == get_context().default_relation()) {
            m_favourite_relation_plugin = plugin;
        }
        if(plugin->is_finite_product_relation()) {
            finite_product_relation_plugin * fprp = static_cast<finite_product_relation_plugin *>(plugin);
            relation_plugin * inner = &fprp->get_inner_plugin();
            m_finite_product_relation_plugins.insert(inner, fprp);
        }
    }

    relation_plugin * relation_manager::try_get_appropriate_plugin(const relation_signature & s) {
        if(m_favourite_relation_plugin && m_favourite_relation_plugin->can_handle_signature(s)) {
            return m_favourite_relation_plugin;
        }
        relation_plugin_vector::iterator rpit = m_relation_plugins.begin();
        relation_plugin_vector::iterator rpend = m_relation_plugins.end();
        for(; rpit!=rpend; ++rpit) {
            if((*rpit)->can_handle_signature(s)) {
                return *rpit;
            }
        }
        return 0;
    }

    relation_plugin & relation_manager::get_appropriate_plugin(const relation_signature & s) {
        relation_plugin * res = try_get_appropriate_plugin(s);
        if (!res) {
            throw default_exception("no suitable plugin found for given relation signature");
        }
        return *res;
    }

    table_plugin * relation_manager::try_get_appropriate_plugin(const table_signature & t) {
        if (m_favourite_table_plugin && m_favourite_table_plugin->can_handle_signature(t)) {
            return m_favourite_table_plugin;
        }
        table_plugin_vector::iterator tpit = m_table_plugins.begin();
        table_plugin_vector::iterator tpend = m_table_plugins.end();
        for(; tpit!=tpend; ++tpit) {
            if((*tpit)->can_handle_signature(t)) {
                return *tpit;
            }
        }
        return 0;
    }

    table_plugin & relation_manager::get_appropriate_plugin(const table_signature & t) {
        table_plugin * res = try_get_appropriate_plugin(t);
        if(!res) {
            throw default_exception("no suitable plugin found for given table signature");
        }
        return *res;
    }

    relation_plugin * relation_manager::get_relation_plugin(symbol const& s) {
        relation_plugin_vector::iterator rpit = m_relation_plugins.begin();
        relation_plugin_vector::iterator rpend = m_relation_plugins.end();
        for(; rpit!=rpend; ++rpit) {
            if((*rpit)->get_name()==s) {
                return *rpit;
            }
        }
        return 0;
    }

    relation_plugin & relation_manager::get_relation_plugin(family_id kind) {
        SASSERT(kind>=0);
        SASSERT(kind<m_next_relation_fid);
        relation_plugin * res = 0;
        VERIFY(m_kind2plugin.find(kind, res));
        return *res;
    }

    table_plugin * relation_manager::get_table_plugin(symbol const& k) {
        table_plugin_vector::iterator tpit = m_table_plugins.begin();
        table_plugin_vector::iterator tpend = m_table_plugins.end();
        for(; tpit!=tpend; ++tpit) {
            if((*tpit)->get_name()==k) {
                return *tpit;
            }
        }
        return 0;
    }

    table_relation_plugin & relation_manager::get_table_relation_plugin(table_plugin & tp) {
        table_relation_plugin * res;
        VERIFY( m_table_relation_plugins.find(&tp, res) );
        return *res;
    }

    bool relation_manager::try_get_finite_product_relation_plugin(const relation_plugin & inner, 
            finite_product_relation_plugin * & res) {
        return m_finite_product_relation_plugins.find(&inner, res);
    }

    table_base * relation_manager::mk_empty_table(const table_signature & s) {
        return get_appropriate_plugin(s).mk_empty(s);
    }


    bool relation_manager::is_non_explanation(relation_signature const& s) const {
        dl_decl_util & decl_util = get_context().get_decl_util();
        unsigned n = s.size();
        for(unsigned i = 0; i < n; i++) {
            if(decl_util.is_rule_sort(s[i])) {
                return false;
            }
        }
        return true;
    }

    relation_base * relation_manager::mk_empty_relation(const relation_signature & s, func_decl* pred) {        
        return mk_empty_relation(s, get_requested_predicate_kind(pred));
    }

    relation_base * relation_manager::mk_empty_relation(const relation_signature & s, family_id kind) {
        if (kind != null_family_id) {
            relation_plugin & plugin = get_relation_plugin(kind);
            if (plugin.can_handle_signature(s, kind))
                return plugin.mk_empty(s, kind);
        }
        relation_base * res;
        relation_plugin* p = m_favourite_relation_plugin;

        if (p && p->can_handle_signature(s)) {
            return p->mk_empty(s);
        }

        if (mk_empty_table_relation(s, res)) {
            return res;
        }

        for (unsigned i = 0; i < m_relation_plugins.size(); ++i) {
            p = m_relation_plugins[i];
            if (p->can_handle_signature(s)) {
                return p->mk_empty(s);
            }
        }

        //If there is no plugin to handle the signature, we just create an empty product relation and
        //stuff will be added to it by later operations.
        TRACE("dl", s.output(get_context().get_manager(), tout << "empty product relation"); tout << "\n";);
        return product_relation_plugin::get_plugin(*this).mk_empty(s);
    }

    /**
      The newly created object takes ownership of the \c table object.
    */
    relation_base * relation_manager::mk_table_relation(const relation_signature & s, table_base * table) {
        SASSERT(s.size()==table->get_signature().size());
        return get_table_relation_plugin(table->get_plugin()).mk_from_table(s, table);
    }

    bool relation_manager::mk_empty_table_relation(const relation_signature & s, relation_base * & result) {
        table_signature tsig;
        if(!relation_signature_to_table(s, tsig)) {
            return false;
        }
        table_base * table = mk_empty_table(tsig);
        result = mk_table_relation(s, table);
        return true;
    }


    relation_base * relation_manager::mk_full_relation(const relation_signature & s, func_decl* p, family_id kind) {
        if (kind != null_family_id) {
            relation_plugin & plugin = get_relation_plugin(kind);
            if (plugin.can_handle_signature(s, kind)) {
                return plugin.mk_full(p, s, kind);
            }
        }
        return get_appropriate_plugin(s).mk_full(p, s, null_family_id);
    }

    relation_base * relation_manager::mk_full_relation(const relation_signature & s, func_decl* pred) {
        family_id kind = get_requested_predicate_kind(pred);
        return mk_full_relation(s, pred, kind);
    }

    void relation_manager::relation_to_table(const relation_sort & sort, const relation_element & from, 
            table_element & to) {
        SASSERT(from->get_num_args()==0);
        VERIFY(get_context().get_decl_util().is_numeral_ext(from, to));
    }

    void relation_manager::table_to_relation(const relation_sort & sort, const table_element & from, 
            relation_element & to) {
        to = get_decl_util().mk_numeral(from, sort);
    }

    void relation_manager::table_to_relation(const relation_sort & sort, const table_element & from, 
            relation_element_ref & to) {
        relation_element rel_el;
        table_to_relation(sort, from, rel_el);
        to = rel_el;
    }

    void relation_manager::table_to_relation(const relation_sort & sort, const table_element & from, 
            const relation_fact::el_proxy & to) {
        relation_element rel_el;
        table_to_relation(sort, from, rel_el);
        to = rel_el;
    }

    bool relation_manager::relation_sort_to_table(const relation_sort & from, table_sort & to) {
        return get_context().get_decl_util().try_get_size(from, to);
    }

    void relation_manager::from_predicate(func_decl * pred, unsigned arg_index, relation_sort & result) {
        result = pred->get_domain(arg_index);
    }

    void relation_manager::from_predicate(func_decl * pred, relation_signature & result) {
        result.reset();
        unsigned arg_num=pred->get_arity();
        for(unsigned i=0;i<arg_num; i++) {
            relation_sort rel_srt;
            from_predicate(pred, i, rel_srt);
            result.push_back(rel_srt);
        }
    }


    bool relation_manager::relation_signature_to_table(const relation_signature & from, table_signature & to) {
        unsigned n=from.size();
        to.resize(n);
        for(unsigned i=0; i<n; i++) {
            if(!relation_sort_to_table(from[i], to[i])) {
                return false;
            }
        }
        return true;
    }

    void relation_manager::relation_fact_to_table(const relation_signature & s, const relation_fact & from, 
            table_fact & to) {
        SASSERT(s.size()==from.size());
        unsigned n=from.size();
        to.resize(n);
        for(unsigned i=0;i<n;i++) {
            relation_to_table(s[i], from[i], to[i]);
        }
    }

    void relation_manager::table_fact_to_relation(const relation_signature & s, const table_fact & from, 
        relation_fact & to) {
            SASSERT(s.size()==from.size());
            unsigned n=from.size();
            to.resize(n);
            for(unsigned i=0;i<n;i++) {
                table_to_relation(s[i], from[i], to[i]);
            }
    }

    std::string relation_manager::to_nice_string(const relation_element & el) const {
        uint64 val;
        std::stringstream stm;
        if(get_context().get_decl_util().is_numeral_ext(el, val)) {
            stm << val;
        }
        else {
            stm << mk_pp(el, get_context().get_manager());
        }
        return stm.str();
    }

    std::string relation_manager::to_nice_string(const relation_sort & s, const relation_element & el) const {
        std::stringstream stm;
        uint64 val;
        if(get_context().get_decl_util().is_numeral_ext(el, val)) {
            get_context().print_constant_name(s, val, stm);
        }
        else {
            stm << mk_pp(el, get_context().get_manager());
        }
        return stm.str();
    }

    std::string relation_manager::to_nice_string(const relation_sort & s) const {
        std::ostringstream strm;
        strm << mk_pp(s, get_context().get_manager());
        return strm.str();
    }

    std::string relation_manager::to_nice_string(const relation_signature & s) const {
        std::string res("[");
        bool first = true;
        relation_signature::const_iterator it = s.begin();
        relation_signature::const_iterator end = s.end();
        for(; it!=end; ++it) {
            if(first) {
                first = false;
            }
            else {
                res+=',';
            }
            res+=to_nice_string(*it);
        }
        res+=']';

        return res;
    }

    void relation_manager::display(std::ostream & out) const {
        relation_map::iterator it=m_relations.begin();
        relation_map::iterator end=m_relations.end();
        for(;it!=end;++it) {
            out << "Table " << it->m_key->get_name() << "\n";
            it->m_value->display(out);
        }
    }

    void relation_manager::display_relation_sizes(std::ostream & out) const {
        relation_map::iterator it=m_relations.begin();
        relation_map::iterator end=m_relations.end();
        for(;it!=end;++it) {
            out << "Relation " << it->m_key->get_name() << " has size " 
                << it->m_value->get_size_estimate_rows() << "\n";
        }
    }

    void relation_manager::display_output_tables(rule_set const& rules, std::ostream & out) const {
        const decl_set & output_preds = rules.get_output_predicates();
        decl_set::iterator it=output_preds.begin();
        decl_set::iterator end=output_preds.end();
        for(; it!=end; ++it) {
            func_decl * pred = *it;
            relation_base * rel = try_get_relation(pred);
            if (!rel) {
                out << "Tuples in " << pred->get_name() << ": \n";
                continue;
            }
            rel->display_tuples(*pred, out);
        }
    }


    // -----------------------------------
    //
    // relation operations
    //
    // -----------------------------------

    class relation_manager::empty_signature_relation_join_fn : public relation_join_fn {
    public:
        virtual relation_base * operator()(const relation_base & r1, const relation_base & r2) {
            TRACE("dl", tout << r1.get_plugin().get_name() << " " << r2.get_plugin().get_name() << "\n";);
            if(r1.get_signature().empty()) {
                if(r1.empty()) {
                    return r2.get_manager().mk_empty_relation(r2.get_signature(), r2.get_kind());
                }
                else {
                    return r2.clone();
                }
            }
            else {
                SASSERT(r2.get_signature().empty());
                if(r2.empty()) {
                    return r1.get_manager().mk_empty_relation(r1.get_signature(), r1.get_kind());
                }
                else {
                    return r1.clone();
                }
            }
        }
    };

    relation_join_fn * relation_manager::mk_join_fn(const relation_base & t1, const relation_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2, bool allow_product_relation) {
        relation_plugin * p1 = &t1.get_plugin();
        relation_plugin * p2 = &t2.get_plugin();

        relation_join_fn * res = p1->mk_join_fn(t1, t2, col_cnt, cols1, cols2);
        
        if(!res && p1!=p2) {
            res = p2->mk_join_fn(t1, t2, col_cnt, cols1, cols2);
        }

        if(!res && (t1.get_signature().empty() || t2.get_signature().empty())) {
            res = alloc(empty_signature_relation_join_fn);
        }

        finite_product_relation_plugin * fprp;
        if(!res && p1->from_table() && try_get_finite_product_relation_plugin(*p2, fprp)) {
            //we downcast here to relation_plugin so that we don't have to declare 
            //relation_manager as a friend class of finite_product_relation_plugin
            res = static_cast<relation_plugin *>(fprp)->mk_join_fn(t1, t2, col_cnt, cols1, cols2);
        }
        if(!res && p2->from_table() && try_get_finite_product_relation_plugin(*p1, fprp)) {
            res = static_cast<relation_plugin *>(fprp)->mk_join_fn(t1, t2, col_cnt, cols1, cols2);
        }

        if(!res && allow_product_relation) {
            relation_plugin & product_plugin = product_relation_plugin::get_plugin(*this);
            res = product_plugin.mk_join_fn(t1, t2, col_cnt, cols1, cols2);
        }

        return res;
    }

    relation_transformer_fn * relation_manager::mk_project_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * removed_cols) {
        return t.get_plugin().mk_project_fn(t, col_cnt, removed_cols);
    }

    class relation_manager::default_relation_filter_interpreted_and_project_fn : public relation_transformer_fn {
        scoped_ptr<relation_mutator_fn>     m_filter;
        scoped_ptr<relation_transformer_fn> m_project;
        unsigned_vector                     m_removed_cols;
    public:
        /**
            This constructor should be used only if we know that the projection operation
            exists for the result of the join.
        */
        default_relation_filter_interpreted_and_project_fn(
            relation_mutator_fn* filter,
            unsigned removed_col_cnt,
            const unsigned * removed_cols)
            : m_filter(filter), 
              m_project(0), 
              m_removed_cols(removed_col_cnt, removed_cols) {}

        virtual relation_base * operator()(const relation_base & t) {
            scoped_rel<relation_base> t1 = t.clone();
            (*m_filter)(*t1);
            if( !m_project) {
                relation_manager & rmgr = t1->get_plugin().get_manager();
                m_project = rmgr.mk_project_fn(*t1, m_removed_cols.size(), m_removed_cols.c_ptr());
                if (!m_project) {
                    throw default_exception("projection does not exist");
                }
            }
            return (*m_project)(*t1);
        }
    };

    relation_transformer_fn * relation_manager::mk_filter_interpreted_and_project_fn(
        const relation_base & t, app * condition,
        unsigned removed_col_cnt, const unsigned * removed_cols) {

        relation_transformer_fn* res = 
            t.get_plugin().mk_filter_interpreted_and_project_fn(
                t, 
                condition,
                removed_col_cnt,
                removed_cols);

        if (!res) {
            relation_mutator_fn* filter_fn = mk_filter_interpreted_fn(t, condition);
            if (filter_fn) {
                res = alloc(default_relation_filter_interpreted_and_project_fn, 
                            filter_fn,
                            removed_col_cnt,
                            removed_cols);
            }
        }
        return res;
    }

    class relation_manager::default_relation_apply_sequential_fn : public relation_mutator_fn {
        ptr_vector<relation_mutator_fn> m_mutators;
    public:
        default_relation_apply_sequential_fn(unsigned n, relation_mutator_fn ** mutators):
            m_mutators(n, mutators) {            
        }
        virtual ~default_relation_apply_sequential_fn() {
            std::for_each(m_mutators.begin(), m_mutators.end(), delete_proc<relation_mutator_fn>());
        }
        
        virtual void operator()(relation_base& t) {
            for (unsigned i = 0; i < m_mutators.size(); ++i) {
                if (t.empty()) return;
                (*(m_mutators[i]))(t);
            }
        }
    };

    relation_mutator_fn * relation_manager::mk_apply_sequential_fn(unsigned n, relation_mutator_fn ** mutators) {
        return alloc(default_relation_apply_sequential_fn, n, mutators);
    }

    class relation_manager::default_relation_join_project_fn : public relation_join_fn {
        scoped_ptr<relation_join_fn> m_join;
        scoped_ptr<relation_transformer_fn> m_project;

        unsigned_vector m_removed_cols;
    public:
        /**
            This constructor should be used only if we know that the projection operation
            exists for the result of the join.
            */
        default_relation_join_project_fn(join_fn * join, unsigned removed_col_cnt,
            const unsigned * removed_cols)
            : m_join(join), m_project(0), m_removed_cols(removed_col_cnt, removed_cols) {}

        virtual relation_base * operator()(const relation_base & t1, const relation_base & t2) {
            scoped_rel<relation_base> aux = (*m_join)(t1, t2);
            if(!m_project) {
                relation_manager & rmgr = aux->get_plugin().get_manager();
                m_project = rmgr.mk_project_fn(*aux, m_removed_cols.size(), m_removed_cols.c_ptr());
                if(!m_project) {
                    throw default_exception("projection does not exist");
                }
            }
            relation_base * res = (*m_project)(*aux);
            return res;
        }
    };


    relation_join_fn * relation_manager::mk_join_project_fn(const relation_base & t1, const relation_base & t2,
            unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, 
            unsigned removed_col_cnt, const unsigned * removed_cols, bool allow_product_relation_join) { 
        relation_join_fn * res = t1.get_plugin().mk_join_project_fn(t1, t2, joined_col_cnt, cols1, cols2, 
            removed_col_cnt, removed_cols);
        if(!res && &t1.get_plugin()!=&t2.get_plugin()) {
            res = t2.get_plugin().mk_join_project_fn(t1, t2, joined_col_cnt, cols1, cols2, removed_col_cnt, 
                removed_cols);
        }
        if(!res) {
            relation_join_fn * join = mk_join_fn(t1, t2, joined_col_cnt, cols1, cols2, allow_product_relation_join);
            if(join) {
                res = alloc(default_relation_join_project_fn, join, removed_col_cnt, removed_cols);
            }
        }
        return res;
                
    }

    relation_transformer_fn * relation_manager::mk_rename_fn(const relation_base & t, unsigned permutation_cycle_len, 
            const unsigned * permutation_cycle) {
        return t.get_plugin().mk_rename_fn(t, permutation_cycle_len, permutation_cycle);
    }

    relation_transformer_fn * relation_manager::mk_permutation_rename_fn(const relation_base & t, 
            const unsigned * permutation) {
        relation_transformer_fn * res = t.get_plugin().mk_permutation_rename_fn(t, permutation);
        if(!res) {
            res = alloc(default_relation_permutation_rename_fn, t, permutation);
        }
        return res;
    }


    relation_union_fn * relation_manager::mk_union_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta) {         
        relation_union_fn * res = tgt.get_plugin().mk_union_fn(tgt, src, delta);
        if(!res && &tgt.get_plugin()!=&src.get_plugin()) {
            res = src.get_plugin().mk_union_fn(tgt, src, delta);
        }
        if(!res && delta && &tgt.get_plugin()!=&delta->get_plugin() && &src.get_plugin()!=&delta->get_plugin()) {
            res = delta->get_plugin().mk_union_fn(tgt, src, delta);
        }
        // TRACE("dl", tout << src.get_plugin().get_name() << " " << tgt.get_plugin().get_name() << " " << (res?"created":"not created") << "\n";); 
        return res;
    }

    relation_union_fn * relation_manager::mk_widen_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta) { 
        relation_union_fn * res = tgt.get_plugin().mk_widen_fn(tgt, src, delta);
        if(!res && &tgt.get_plugin()!=&src.get_plugin()) {
            res = src.get_plugin().mk_widen_fn(tgt, src, delta);
        }
        if(!res && delta && &tgt.get_plugin()!=&delta->get_plugin() && &src.get_plugin()!=&delta->get_plugin()) {
            res = delta->get_plugin().mk_widen_fn(tgt, src, delta);
        }
        if(!res) {
            res = mk_union_fn(tgt, src, delta);
        }
        return res;
    }

    relation_mutator_fn * relation_manager::mk_filter_identical_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * identical_cols) { 
        return t.get_plugin().mk_filter_identical_fn(t, col_cnt, identical_cols);
    }

    relation_mutator_fn * relation_manager::mk_filter_equal_fn(const relation_base & t, 
            const relation_element & value, unsigned col) { 

        return t.get_plugin().mk_filter_equal_fn(t, value, col);
    }

    relation_mutator_fn * relation_manager::mk_filter_interpreted_fn(const relation_base & t, app * condition) {
        return t.get_plugin().mk_filter_interpreted_fn(t, condition);
    }

    class relation_manager::default_relation_select_equal_and_project_fn : public relation_transformer_fn {
        scoped_ptr<relation_mutator_fn> m_filter;
        scoped_ptr<relation_transformer_fn> m_project;
    public:
        default_relation_select_equal_and_project_fn(relation_mutator_fn * filter, relation_transformer_fn * project)
            : m_filter(filter), m_project(project) {}

        virtual relation_base * operator()(const relation_base & t1) {
            TRACE("dl", tout << t1.get_plugin().get_name() << "\n";);
            scoped_rel<relation_base> aux = t1.clone();
            (*m_filter)(*aux);
            relation_base * res = (*m_project)(*aux);
            return res;
        }
    };

    relation_transformer_fn * relation_manager::mk_select_equal_and_project_fn(const relation_base & t, 
            const relation_element & value, unsigned col) { 
        relation_transformer_fn * res = t.get_plugin().mk_select_equal_and_project_fn(t, value, col);
        if(!res) {
            relation_mutator_fn * selector = mk_filter_equal_fn(t, value, col);
            if(selector) {
                relation_transformer_fn * projector = mk_project_fn(t, 1, &col);
                if(projector) {
                    res = alloc(default_relation_select_equal_and_project_fn, selector, projector); 
                }
                else {
                    dealloc(selector);
                }
            }
        }
        return res;
    }


    class relation_manager::default_relation_intersection_filter_fn : public relation_intersection_filter_fn {
        scoped_ptr<relation_join_fn> m_join_fun;
        scoped_ptr<relation_union_fn> m_union_fun;
    public:

        default_relation_intersection_filter_fn(relation_join_fn * join_fun, relation_union_fn * union_fun) 
            : m_join_fun(join_fun), m_union_fun(union_fun) {}

        virtual void operator()(relation_base & tgt, const relation_base & intersected_obj) {
            scoped_rel<relation_base> filtered_rel = (*m_join_fun)(tgt, intersected_obj);
            TRACE("dl", 
                  tgt.display(tout << "tgt:\n"); 
                  intersected_obj.display(tout << "intersected:\n");
                  filtered_rel->display(tout << "filtered:\n");
                  );
            if(!m_union_fun) {
                SASSERT(tgt.can_swap(*filtered_rel));
                tgt.swap(*filtered_rel);
            }
            tgt.reset();
            TRACE("dl", tgt.display(tout << "target reset:\n"); );
            (*m_union_fun)(tgt, *filtered_rel);
            TRACE("dl", tgt.display(tout << "intersected target:\n"); );
        }

    };

    relation_intersection_filter_fn * relation_manager::try_mk_default_filter_by_intersection_fn(
            const relation_base & tgt, const relation_base & src, unsigned joined_col_cnt, 
            const unsigned * tgt_cols, const unsigned * src_cols) {
        TRACE("dl_verbose", tout << tgt.get_plugin().get_name() << "\n";);
        unsigned_vector join_removed_cols;
        add_sequence(tgt.get_signature().size(), src.get_signature().size(), join_removed_cols);
        scoped_rel<relation_join_fn> join_fun = mk_join_project_fn(tgt, src, joined_col_cnt, tgt_cols, src_cols,
            join_removed_cols.size(), join_removed_cols.c_ptr(), false);
        if(!join_fun) {
            return 0;
        }
        //we perform the join operation here to see what the result is
        scoped_rel<relation_base> join_res = (*join_fun)(tgt, src);
        if(tgt.can_swap(*join_res)) {
            return alloc(default_relation_intersection_filter_fn, join_fun.release(), 0);
        }
        if(join_res->get_plugin().is_product_relation()) {
            //we cannot have the product relation here, since it uses the intersection operation
            //for unions and therefore we would get into an infinite recursion
            return 0;
        }
        scoped_rel<relation_union_fn> union_fun = mk_union_fn(tgt, *join_res);
        if(!union_fun) {
            return 0;
        }
        return alloc(default_relation_intersection_filter_fn, join_fun.release(), union_fun.release());
    }


    relation_intersection_filter_fn * relation_manager::mk_filter_by_intersection_fn(const relation_base & t, 
            const relation_base & src, unsigned joined_col_cnt, const unsigned * t_cols, const unsigned * src_cols) {
        TRACE("dl_verbose", tout << t.get_plugin().get_name() << "\n";);
        relation_intersection_filter_fn * res = t.get_plugin().mk_filter_by_intersection_fn(t, src, joined_col_cnt, 
            t_cols, src_cols);
        if(!res && &t.get_plugin()!=&src.get_plugin()) {
            res = src.get_plugin().mk_filter_by_intersection_fn(t, src, joined_col_cnt, t_cols, src_cols);
        }
        if(!res) {
            res = try_mk_default_filter_by_intersection_fn(t, src, joined_col_cnt, t_cols, src_cols);
        }
        return res;
    }

    relation_intersection_filter_fn * relation_manager::mk_filter_by_intersection_fn(const relation_base & tgt, 
            const relation_base & src) {
        TRACE("dl_verbose", tout << tgt.get_plugin().get_name() << "\n";);
        SASSERT(tgt.get_signature()==src.get_signature());
        unsigned sz = tgt.get_signature().size();
        unsigned_vector cols;
        add_sequence(0, sz, cols);
        return mk_filter_by_intersection_fn(tgt, src, cols, cols);
    }


    relation_intersection_filter_fn * relation_manager::mk_filter_by_negation_fn(const relation_base & t, 
            const relation_base & negated_obj, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * negated_cols) { 
        TRACE("dl", tout << t.get_plugin().get_name() << "\n";);
        relation_intersection_filter_fn * res = t.get_plugin().mk_filter_by_negation_fn(t, negated_obj, joined_col_cnt, 
            t_cols, negated_cols);
        if(!res && &t.get_plugin()!=&negated_obj.get_plugin()) {
            res = negated_obj.get_plugin().mk_filter_by_negation_fn(t, negated_obj, joined_col_cnt, t_cols, 
                negated_cols);
        }
        return res;
    }





    // -----------------------------------
    //
    // table operations
    //
    // -----------------------------------

    class relation_manager::default_table_join_fn : public convenient_table_join_fn {
        unsigned m_col_cnt;
    public:
        default_table_join_fn(const table_signature & t1_sig, const table_signature & t2_sig, unsigned col_cnt, 
            const unsigned * cols1, const unsigned * cols2) 
            : convenient_table_join_fn(t1_sig, t2_sig, col_cnt, cols1, cols2), m_col_cnt(col_cnt) {}

        virtual table_base * operator()(const table_base & t1, const table_base & t2) {
            table_plugin * plugin = &t1.get_plugin();

            const table_signature & res_sign = get_result_signature();
            if (!plugin->can_handle_signature(res_sign)) {
                plugin = &t2.get_plugin();
                if (!plugin->can_handle_signature(res_sign)) {
                    plugin = &t1.get_manager().get_appropriate_plugin(res_sign);
                }
            }
            SASSERT(plugin->can_handle_signature(res_sign));
            table_base * res = plugin->mk_empty(res_sign);

            unsigned t1cols = t1.get_signature().size();
            unsigned t2cols = t2.get_signature().size();
            unsigned t1first_func = t1.get_signature().first_functional();
            unsigned t2first_func = t2.get_signature().first_functional();

            table_base::iterator els1it = t1.begin();
            table_base::iterator els1end = t1.end();
            table_base::iterator els2end = t2.end();

            table_fact acc;

            for(; els1it!=els1end; ++els1it) {
                const table_base::row_interface & row1 = *els1it;

                table_base::iterator els2it = t2.begin();
                for(; els2it!=els2end; ++els2it) {
                    const table_base::row_interface & row2 = *els2it;

                    bool match=true;
                    for(unsigned i=0; i<m_col_cnt; i++) {
                        if(row1[m_cols1[i]]!=row2[m_cols2[i]]) {
                            match=false;
                            break;
                        }
                    }
                    if(!match) {
                        continue;
                    }

                    acc.reset();
                    for(unsigned i=0; i<t1first_func; i++) {
                        acc.push_back(row1[i]);
                    }
                    for(unsigned i=0; i<t2first_func; i++) {
                        acc.push_back(row2[i]);
                    }
                    for(unsigned i=t1first_func; i<t1cols; i++) {
                        acc.push_back(row1[i]);
                    }
                    for(unsigned i=t2first_func; i<t2cols; i++) {
                        acc.push_back(row2[i]);
                    }
                    res->add_fact(acc);
                }
            }
            return res;
        }
    };

    table_join_fn * relation_manager::mk_join_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        table_join_fn * res = t1.get_plugin().mk_join_fn(t1, t2, col_cnt, cols1, cols2);
        if(!res && &t1.get_plugin()!=&t2.get_plugin()) {
            res = t2.get_plugin().mk_join_fn(t1, t2, col_cnt, cols1, cols2);
        }
        if(!res) {
            table_signature sig;
            table_signature::from_join(t1.get_signature(), t2.get_signature(), 
                col_cnt, cols1, cols2, sig);
            res = alloc(default_table_join_fn, t1.get_signature(), t2.get_signature(), col_cnt, cols1, cols2);
        }
        return res;
    }

    class relation_manager::auxiliary_table_transformer_fn {
        table_fact m_row;
    public:
        virtual ~auxiliary_table_transformer_fn() {}
        virtual const table_signature & get_result_signature() const = 0;
        virtual void modify_fact(table_fact & f) const = 0;

        table_base * operator()(const table_base & t) {
            table_plugin & plugin = t.get_plugin();
            const table_signature & res_sign = get_result_signature();
            SASSERT(plugin.can_handle_signature(res_sign));
            table_base * res = plugin.mk_empty(res_sign);

            table_base::iterator it = t.begin();
            table_base::iterator end = t.end();

            for(; it!=end; ++it) {
                it->get_fact(m_row);
                modify_fact(m_row);
                res->add_fact(m_row);
            }
            return res;
        }
    };

    class relation_manager::default_table_project_fn 
            : public convenient_table_project_fn, auxiliary_table_transformer_fn {
    public:
        default_table_project_fn(const table_signature & orig_sig, unsigned removed_col_cnt, 
                const unsigned * removed_cols) 
            : convenient_table_project_fn(orig_sig, removed_col_cnt, removed_cols) {
                SASSERT(removed_col_cnt>0);
        }

        virtual const table_signature & get_result_signature() const {
            return convenient_table_project_fn::get_result_signature();
        }

        virtual void modify_fact(table_fact & f) const {
            project_out_vector_columns(f, m_removed_cols);
        }

        virtual table_base * operator()(const table_base & t) {
            return auxiliary_table_transformer_fn::operator()(t);
        }
    };

    class relation_manager::null_signature_table_project_fn : public table_transformer_fn {
        const table_signature m_empty_sig;
    public:
        null_signature_table_project_fn() : m_empty_sig() {}
        virtual table_base * operator()(const table_base & t) {
            relation_manager & m = t.get_plugin().get_manager();
            table_base * res = m.mk_empty_table(m_empty_sig);
            if(!t.empty()) {
                table_fact el;
                res->add_fact(el);
            }
            return res;
        }
    };



    table_transformer_fn * relation_manager::mk_project_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * removed_cols) {
        table_transformer_fn * res = t.get_plugin().mk_project_fn(t, col_cnt, removed_cols);
        if(!res && col_cnt==t.get_signature().size()) {
            //all columns are projected out
            res = alloc(null_signature_table_project_fn);
        }
        if(!res) {
            res = alloc(default_table_project_fn, t.get_signature(), col_cnt, removed_cols);
        }
        return res;
    }


    class relation_manager::default_table_join_project_fn : public convenient_table_join_project_fn {
        scoped_ptr<table_join_fn> m_join;
        scoped_ptr<table_transformer_fn> m_project;

        unsigned_vector m_removed_cols;
    public:
        default_table_join_project_fn(join_fn * join, const table_base & t1, const table_base & t2, 
                unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
                const unsigned * removed_cols)
            : convenient_table_join_project_fn(t1.get_signature(), t2.get_signature(), joined_col_cnt, cols1, 
                cols2, removed_col_cnt, removed_cols), 
            m_join(join), 
            m_removed_cols(removed_col_cnt, removed_cols) {}

        class unreachable_reducer : public table_row_pair_reduce_fn {
            virtual void operator()(table_element * func_columns, const table_element * merged_func_columns) {
                //we do project_with_reduce only if we are sure there will be no reductions
                //(see code of the table_signature::from_join_project function)
                UNREACHABLE();
            }
        };

        virtual table_base * operator()(const table_base & t1, const table_base & t2) {
            table_base * aux = (*m_join)(t1, t2);
            if(m_project==0) {
                relation_manager & rmgr = aux->get_plugin().get_manager();
                if(get_result_signature().functional_columns()!=0) {
                    //to preserve functional columns we need to do the project_with_reduction
                    unreachable_reducer * reducer = alloc(unreachable_reducer);
                    m_project = rmgr.mk_project_with_reduce_fn(*aux, m_removed_cols.size(), m_removed_cols.c_ptr(), reducer);
                }
                else {
                    m_project = rmgr.mk_project_fn(*aux, m_removed_cols);
                }
                if(!m_project) {
                    throw default_exception("projection for table does not exist");
                }
            }
            table_base * res = (*m_project)(*aux);
            aux->deallocate();
            return res;
        }
    };

    table_join_fn * relation_manager::mk_join_project_fn(const table_base & t1, const table_base & t2,
            unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, 
            unsigned removed_col_cnt, const unsigned * removed_cols) { 
        table_join_fn * res = t1.get_plugin().mk_join_project_fn(t1, t2, joined_col_cnt, cols1, cols2, 
            removed_col_cnt, removed_cols);
        if(!res && &t1.get_plugin()!=&t2.get_plugin()) {
            res = t2.get_plugin().mk_join_project_fn(t1, t2, joined_col_cnt, cols1, cols2, removed_col_cnt, 
                removed_cols);
        }
        if(!res) {
            table_join_fn * join = mk_join_fn(t1, t2, joined_col_cnt, cols1, cols2);
            if(join) {
                res = alloc(default_table_join_project_fn, join, t1, t2, joined_col_cnt, cols1, cols2, 
                    removed_col_cnt, removed_cols);
            }
        }
        return res;
                
    }

    class relation_manager::default_table_rename_fn 
            : public convenient_table_rename_fn, auxiliary_table_transformer_fn {
    public:
        default_table_rename_fn(const table_signature & orig_sig, unsigned permutation_cycle_len, 
                    const unsigned * permutation_cycle) 
                : convenient_table_rename_fn(orig_sig, permutation_cycle_len, permutation_cycle) {
            SASSERT(permutation_cycle_len>=2);
        }

        virtual const table_signature & get_result_signature() const {
            return convenient_table_rename_fn::get_result_signature();
        }

        virtual void modify_fact(table_fact & f) const {
            permutate_by_cycle(f, m_cycle);
        }

        virtual table_base * operator()(const table_base & t) {
            return auxiliary_table_transformer_fn::operator()(t);
        }

    };

    table_transformer_fn * relation_manager::mk_rename_fn(const table_base & t, unsigned permutation_cycle_len, 
            const unsigned * permutation_cycle) {
        table_transformer_fn * res = t.get_plugin().mk_rename_fn(t, permutation_cycle_len, permutation_cycle);
        if(!res) {
            res = alloc(default_table_rename_fn, t.get_signature(), permutation_cycle_len, permutation_cycle);
        }
        return res;
    }

    table_transformer_fn * relation_manager::mk_permutation_rename_fn(const table_base & t, 
            const unsigned * permutation) {
        table_transformer_fn * res = t.get_plugin().mk_permutation_rename_fn(t, permutation);
        if(!res) {
            res = alloc(default_table_permutation_rename_fn, t, permutation);
        }
        return res;
    }


    class relation_manager::default_table_union_fn : public table_union_fn {
        table_fact m_row;
    public:
        virtual void operator()(table_base & tgt, const table_base & src, table_base * delta) {
            table_base::iterator it = src.begin();
            table_base::iterator iend = src.end();

            for(; it!=iend; ++it) {
                it->get_fact(m_row);

                if(delta) {
                    if(!tgt.contains_fact(m_row)) {
                        tgt.add_new_fact(m_row);
                        delta->add_fact(m_row);
                    }
                }
                else {
                    //if there's no delta, we don't need to know whether we are actually adding a new fact
                    tgt.add_fact(m_row);
                }
            }
        }
    };

    table_union_fn * relation_manager::mk_union_fn(const table_base & tgt, const table_base & src, 
            const table_base * delta) { 
        table_union_fn * res = tgt.get_plugin().mk_union_fn(tgt, src, delta);
        if(!res && &tgt.get_plugin()!=&src.get_plugin()) {
            res = src.get_plugin().mk_union_fn(tgt, src, delta);
        }
        if(!res && delta && &tgt.get_plugin()!=&delta->get_plugin() && &src.get_plugin()!=&delta->get_plugin()) {
            res = delta->get_plugin().mk_union_fn(tgt, src, delta);
        }
        if(!res) {
            res = alloc(default_table_union_fn);
        }
        return res;
    }

    table_union_fn * relation_manager::mk_widen_fn(const table_base & tgt, const table_base & src, 
            const table_base * delta) { 
        table_union_fn * res = tgt.get_plugin().mk_widen_fn(tgt, src, delta);
        if(!res && &tgt.get_plugin()!=&src.get_plugin()) {
            res = src.get_plugin().mk_widen_fn(tgt, src, delta);
        }
        if(!res && delta && &tgt.get_plugin()!=&delta->get_plugin() && &src.get_plugin()!=&delta->get_plugin()) {
            res = delta->get_plugin().mk_widen_fn(tgt, src, delta);
        }
        if(!res) {
            res = mk_union_fn(tgt, src, delta);
        }
        return res;
    }


    /**
       An auixiliary class for functors that perform filtering. It performs the table traversal
       and only asks for each individual row whether it should be removed.

       When using this class in multiple inheritance, this class should not be inherited publicly
       and should be mentioned as last. This should ensure that deteletion of the object will
       go well when initiated from a pointer to the first ancestor.
    */
    class relation_manager::auxiliary_table_filter_fn {
        table_fact m_row;
        svector<table_element> m_to_remove;
    public:
        virtual ~auxiliary_table_filter_fn() {}
        virtual bool should_remove(const table_fact & f) const = 0;

        void operator()(table_base & r) {
            m_to_remove.reset();
            unsigned sz = 0;
            table_base::iterator it = r.begin();
            table_base::iterator iend = r.end();
            for(; it!=iend; ++it) {
                it->get_fact(m_row);
                if(should_remove(m_row)) {
                    m_to_remove.append(m_row.size(), m_row.c_ptr());
                    ++sz;
                }
            }
            r.remove_facts(sz, m_to_remove.c_ptr());
        }
    };

    class relation_manager::default_table_filter_identical_fn : public table_mutator_fn, auxiliary_table_filter_fn {
        const unsigned m_col_cnt;
        const unsigned_vector m_identical_cols;
    public:
        default_table_filter_identical_fn(unsigned col_cnt, const unsigned * identical_cols) 
                : m_col_cnt(col_cnt),
                m_identical_cols(col_cnt, identical_cols) {
            SASSERT(col_cnt>=2);
        }

        virtual bool should_remove(const table_fact & f) const {
            table_element val=f[m_identical_cols[0]];
            for(unsigned i=1; i<m_col_cnt; i++) {
                if(f[m_identical_cols[i]]!=val) {
                    return true;
                }
            }
            return false;
        }

        virtual void operator()(table_base & t) {
            auxiliary_table_filter_fn::operator()(t);
        }

    };

    table_mutator_fn * relation_manager::mk_filter_identical_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * identical_cols) { 
        table_mutator_fn * res = t.get_plugin().mk_filter_identical_fn(t, col_cnt, identical_cols);
        if(!res) {
            res = alloc(default_table_filter_identical_fn, col_cnt, identical_cols);
        }
        return res;
    }



    class relation_manager::default_table_filter_equal_fn : public table_mutator_fn, auxiliary_table_filter_fn {
        const table_element m_value;
        const unsigned m_col;
    public:
        default_table_filter_equal_fn(const table_element & value, unsigned col) 
                : m_value(value),
                m_col(col) {}

        virtual bool should_remove(const table_fact & f) const {
            return f[m_col]!=m_value;
        }

        virtual void operator()(table_base & t) {
            auxiliary_table_filter_fn::operator()(t);
        }
    };

    table_mutator_fn * relation_manager::mk_filter_equal_fn(const table_base & t, 
            const table_element & value, unsigned col) { 
        table_mutator_fn * res = t.get_plugin().mk_filter_equal_fn(t, value, col);
        if(!res) {
            res = alloc(default_table_filter_equal_fn, value, col);
        }
        return res;
    }

    class relation_manager::default_table_filter_not_equal_fn 
            : public table_mutator_fn, auxiliary_table_filter_fn {
        unsigned      m_column;
        uint64        m_value;
    public:
        default_table_filter_not_equal_fn(context & ctx, unsigned column, uint64 value)
            : m_column(column), 
              m_value(value) {
        }

        virtual bool should_remove(const table_fact & f) const {
            return f[m_column] == m_value;
        }

        virtual void operator()(table_base & t) {
            auxiliary_table_filter_fn::operator()(t);
        }

        static table_mutator_fn* mk(context& ctx, expr* condition) {
            ast_manager& m = ctx.get_manager();
            if (!m.is_not(condition)) {
                return 0;
            }
            condition = to_app(condition)->get_arg(0);
            if (!m.is_eq(condition)) {
                return 0;
            }
            expr* x = to_app(condition)->get_arg(0);
            expr* y = to_app(condition)->get_arg(1);
            if (!is_var(x)) {
                std::swap(x, y);
            }
            if (!is_var(x)) {
                return 0;
            }
            dl_decl_util decl_util(m);
            uint64 value = 0;
            if (!decl_util.is_numeral_ext(y, value)) {
                return 0;
            }
            return alloc(default_table_filter_not_equal_fn, ctx, to_var(x)->get_idx(), value);
        }
    };



    class relation_manager::default_table_filter_interpreted_fn 
            : public table_mutator_fn, auxiliary_table_filter_fn {
        ast_manager & m_ast_manager;
        var_subst & m_vs;
        dl_decl_util & m_decl_util;
        th_rewriter & m_simp;
        app_ref m_condition;
        expr_free_vars m_free_vars;
        expr_ref_vector m_args;
    public:
        default_table_filter_interpreted_fn(context & ctx, unsigned col_cnt,  app* condition) 
                : m_ast_manager(ctx.get_manager()),
                  m_vs(ctx.get_var_subst()),
                  m_decl_util(ctx.get_decl_util()),
                  m_simp(ctx.get_rewriter()),
                  m_condition(condition, ctx.get_manager()),
                  m_args(ctx.get_manager()) {
            m_free_vars(m_condition);
        }

        virtual bool should_remove(const table_fact & f) const {
            expr_ref_vector& args = const_cast<expr_ref_vector&>(m_args);

            args.reset();
            //arguments need to be in reverse order for the substitution
            unsigned col_cnt = f.size();
            for(int i=col_cnt-1;i>=0;i--) {
                if(!m_free_vars.contains(i)) {
                    args.push_back(0);
                    continue; //this variable does not occur in the condition;
                }

                table_element el = f[i];
                args.push_back(m_decl_util.mk_numeral(el, m_free_vars[i]));
            }

            expr_ref ground(m_ast_manager);
            m_vs(m_condition.get(), args.size(), args.c_ptr(), ground);
            m_simp(ground);

            return m_ast_manager.is_false(ground);
        }

        virtual void operator()(table_base & t) {
            auxiliary_table_filter_fn::operator()(t);
        }
    };

    table_mutator_fn * relation_manager::mk_filter_interpreted_fn(const table_base & t, app * condition) {
        context & ctx = get_context();
        table_mutator_fn * res = t.get_plugin().mk_filter_interpreted_fn(t, condition);
        if (!res) {
            res = default_table_filter_not_equal_fn::mk(ctx, condition);
        }
        if(!res) {
            res = alloc(default_table_filter_interpreted_fn, ctx, t.get_signature().size(), condition);
        }
        return res;
    }


    class relation_manager::default_table_filter_interpreted_and_project_fn 
            : public table_transformer_fn {
        scoped_ptr<table_mutator_fn> m_filter;
        scoped_ptr<table_transformer_fn> m_project;
        app_ref m_condition;
        unsigned_vector m_removed_cols;
    public:
        default_table_filter_interpreted_and_project_fn(context & ctx, table_mutator_fn * filter,
            app * condition, unsigned removed_col_cnt, const unsigned * removed_cols) 
                : m_filter(filter), m_condition(condition, ctx.get_manager()),
                m_removed_cols(removed_col_cnt, removed_cols) {}

        virtual table_base* operator()(const table_base & tb) {
            table_base *t2 = tb.clone();
            (*m_filter)(*t2);
            if (!m_project) {
                relation_manager & rmgr = t2->get_plugin().get_manager();
                m_project = rmgr.mk_project_fn(*t2, m_removed_cols.size(), m_removed_cols.c_ptr());
                if (!m_project) {
                    throw default_exception("projection does not exist");
                }
            }
            return (*m_project)(*t2);
        }
    };

    table_transformer_fn * relation_manager::mk_filter_interpreted_and_project_fn(const table_base & t,
        app * condition, unsigned removed_col_cnt, const unsigned * removed_cols) {
        table_transformer_fn * res = t.get_plugin().mk_filter_interpreted_and_project_fn(t, condition, removed_col_cnt, removed_cols);
        if (res)
            return res;

        table_mutator_fn * filter = mk_filter_interpreted_fn(t, condition);
        SASSERT(filter);
        res = alloc(default_table_filter_interpreted_and_project_fn, get_context(), filter, condition, removed_col_cnt, removed_cols);
        return res;
    }


    table_intersection_filter_fn * relation_manager::mk_filter_by_intersection_fn(const table_base & t, 
        const table_base & src, unsigned joined_col_cnt, const unsigned * t_cols, const unsigned * src_cols) {
        table_intersection_filter_fn * res = t.get_plugin().mk_filter_by_negation_fn(t, src, joined_col_cnt, 
            t_cols, src_cols);
        if(!res && &t.get_plugin()!=&src.get_plugin()) {
            res = src.get_plugin().mk_filter_by_negation_fn(t, src, joined_col_cnt, t_cols, src_cols);
        }
        return res;
    }
    


    class relation_manager::default_table_negation_filter_fn : public convenient_table_negation_filter_fn, 
                                             auxiliary_table_filter_fn {
        const table_base * m_negated_table;
        mutable table_fact m_aux_fact;
    public:
        default_table_negation_filter_fn(const table_base & tgt, const table_base & neg_t, 
                    unsigned joined_col_cnt, const unsigned * t_cols, const unsigned * negated_cols) 
                : convenient_table_negation_filter_fn(tgt, neg_t, joined_col_cnt, t_cols, negated_cols),
                m_negated_table(0) {
            m_aux_fact.resize(neg_t.get_signature().size());
        }

        virtual bool should_remove(const table_fact & f) const {
            if(!m_all_neg_bound || m_overlap) {
                table_base::iterator nit = m_negated_table->begin();
                table_base::iterator nend = m_negated_table->end();
                for(; nit!=nend; ++nit) {
                    const table_base::row_interface & nrow = *nit;
                    if(bindings_match(nrow, f)) {
                        return true;
                    }
                }
                return false;
            }
            else {
                make_neg_bindings<datalog::table_fact>(m_aux_fact, f);
                return m_negated_table->contains_fact(m_aux_fact);
            }
        }

        virtual void operator()(table_base & tgt, const table_base & negated_table) {
            SASSERT(m_negated_table==0);
            flet<const table_base *> flet_neg_table(m_negated_table, &negated_table);
            auxiliary_table_filter_fn::operator()(tgt);
        }

    };

    table_intersection_filter_fn * relation_manager::mk_filter_by_negation_fn(const table_base & t, 
            const table_base & negated_obj, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * negated_cols) { 
        table_intersection_filter_fn * res = t.get_plugin().mk_filter_by_negation_fn(t, negated_obj, joined_col_cnt, 
            t_cols, negated_cols);
        if(!res && &t.get_plugin()!=&negated_obj.get_plugin()) {
            res = negated_obj.get_plugin().mk_filter_by_negation_fn(t, negated_obj, joined_col_cnt, t_cols, 
                negated_cols);
        }
        if(!res) {
            res = alloc(default_table_negation_filter_fn, t, negated_obj, joined_col_cnt, t_cols, negated_cols);
        }
        return res;
    }

    
    table_intersection_join_filter_fn* relation_manager::mk_filter_by_negated_join_fn(
        const table_base & t, 
        const table_base & src1, 
        const table_base & src2, 
        unsigned_vector const& t_cols,
        unsigned_vector const& src_cols,
        unsigned_vector const& src1_cols,
        unsigned_vector const& src2_cols) {
        return t.get_plugin().mk_filter_by_negated_join_fn(t, src1, src2, t_cols, src_cols, src1_cols, src2_cols);
    }



    class relation_manager::default_table_select_equal_and_project_fn : public table_transformer_fn {
        scoped_ptr<table_mutator_fn> m_filter;
        scoped_ptr<table_transformer_fn> m_project;
    public:
        default_table_select_equal_and_project_fn(table_mutator_fn * filter, table_transformer_fn * project)
            : m_filter(filter), m_project(project) {}

        virtual table_base * operator()(const table_base & t1) {
            TRACE("dl", tout << t1.get_plugin().get_name() << "\n";);
            scoped_rel<table_base> aux = t1.clone();
            (*m_filter)(*aux);
            table_base * res = (*m_project)(*aux);
            return res;
        }
    };

    table_transformer_fn * relation_manager::mk_select_equal_and_project_fn(const table_base & t, 
            const table_element & value, unsigned col) { 
        table_transformer_fn * res = t.get_plugin().mk_select_equal_and_project_fn(t, value, col);
        if(!res) {
            table_mutator_fn * selector = mk_filter_equal_fn(t, value, col);
            SASSERT(selector);
            table_transformer_fn * projector = mk_project_fn(t, 1, &col);
            SASSERT(projector);
            res = alloc(default_table_select_equal_and_project_fn, selector, projector); 
        }
        return res;
    }


    class relation_manager::default_table_map_fn : public table_mutator_fn {
        scoped_ptr<table_row_mutator_fn> m_mapper;
        unsigned m_first_functional;
        scoped_rel<table_base> m_aux_table;
        scoped_ptr<table_union_fn> m_union_fn;
        table_fact m_curr_fact;
    public:
        default_table_map_fn(const table_base & t, table_row_mutator_fn * mapper) 
                : m_mapper(mapper), m_first_functional(t.get_signature().first_functional()) {
            SASSERT(t.get_signature().functional_columns()>0);
            table_plugin & plugin = t.get_plugin();
            m_aux_table = plugin.mk_empty(t.get_signature());
            m_union_fn = plugin.mk_union_fn(t, *m_aux_table, static_cast<table_base *>(0));
        }

        virtual ~default_table_map_fn() {}

        virtual void operator()(table_base & t) {
            SASSERT(t.get_signature()==m_aux_table->get_signature());
            if(!m_aux_table->empty()) {
                m_aux_table->reset();
            }


            table_base::iterator it = t.begin();
            table_base::iterator iend = t.end();
            for(; it!=iend; ++it) {
                it->get_fact(m_curr_fact);
                if((*m_mapper)(m_curr_fact.c_ptr()+m_first_functional)) {
                    m_aux_table->add_fact(m_curr_fact);
                }
            }
            
            t.reset();
            (*m_union_fn)(t, *m_aux_table, static_cast<table_base *>(0));
        }
    };

    table_mutator_fn * relation_manager::mk_map_fn(const table_base & t, table_row_mutator_fn * mapper) {
        SASSERT(t.get_signature().functional_columns()>0);
        table_mutator_fn * res = t.get_plugin().mk_map_fn(t, mapper);
        if(!res) {
            res = alloc(default_table_map_fn, t, mapper);
        }
        return res;
    }


    class relation_manager::default_table_project_with_reduce_fn : public convenient_table_transformer_fn {
        unsigned_vector m_removed_cols;
        const unsigned m_inp_col_cnt;
        const unsigned m_removed_col_cnt;
        const unsigned m_result_col_cnt;
        scoped_ptr<table_row_pair_reduce_fn> m_reducer;
        unsigned m_res_first_functional;
        table_fact m_row;
        table_fact m_former_row;
    public:
        default_table_project_with_reduce_fn(const table_signature & orig_sig, unsigned removed_col_cnt, 
                    const unsigned * removed_cols, table_row_pair_reduce_fn * reducer) 
                : m_removed_cols(removed_col_cnt, removed_cols),
                m_inp_col_cnt(orig_sig.size()),
                m_removed_col_cnt(removed_col_cnt),
                m_result_col_cnt(orig_sig.size()-removed_col_cnt), 
                m_reducer(reducer) {
            SASSERT(removed_col_cnt>0);
            table_signature::from_project_with_reduce(orig_sig, removed_col_cnt, removed_cols, 
                get_result_signature());
            m_res_first_functional = get_result_signature().first_functional();
            m_row.resize(get_result_signature().size());
            m_former_row.resize(get_result_signature().size());
        }

        virtual ~default_table_project_with_reduce_fn() {}

        virtual void modify_fact(table_fact & f) const {
            unsigned ofs=1;
            unsigned r_i=1;
            for(unsigned i=m_removed_cols[0]+1; i<m_inp_col_cnt; i++) {
                if(r_i!=m_removed_col_cnt && m_removed_cols[r_i]==i) {
                    r_i++;
                    ofs++;
                    continue;
                }
                f[i-ofs]=f[i];
            }
            SASSERT(r_i==m_removed_col_cnt);
            f.resize(m_result_col_cnt);
        }

        void mk_project(table_base::iterator& it)  {
            for (unsigned i = 0, j = 0, r_i = 0; i < m_inp_col_cnt; ++i) {
                if (r_i < m_removed_col_cnt && m_removed_cols[r_i] == i) {
                    ++r_i;
                }
                else {
                    m_row[j] = m_former_row[j] = (*it)[i];
                    ++j;
                }
            }
        }

        virtual table_base * operator()(const table_base & t) {
            table_plugin & plugin = t.get_plugin();
            const table_signature & res_sign = get_result_signature();
            SASSERT(plugin.can_handle_signature(res_sign));
            table_base * res = plugin.mk_empty(res_sign);

            table_base::iterator it = t.begin();
            table_base::iterator end = t.end();


            for(; it!=end; ++it) {
                mk_project(it);
                if(!res->suggest_fact(m_former_row)) {
                    (*m_reducer)(m_former_row.c_ptr()+m_res_first_functional, m_row.c_ptr()+m_res_first_functional);
                    res->ensure_fact(m_former_row);
                }
            }
            return res;
        }
    };

    table_transformer_fn * relation_manager::mk_project_with_reduce_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * removed_cols, table_row_pair_reduce_fn * reducer) {
        SASSERT(t.get_signature().functional_columns()>0);
        table_transformer_fn * res = t.get_plugin().mk_project_with_reduce_fn(t, col_cnt, removed_cols, reducer);
        if(!res) {
            res = alloc(default_table_project_with_reduce_fn, t.get_signature(), col_cnt, removed_cols, reducer);
        }
        return res;
    }

};

