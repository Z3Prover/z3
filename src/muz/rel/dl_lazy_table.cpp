/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_lazy_table.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2013-09-04

Revision History:

--*/

#include "muz/rel/dl_lazy_table.h"
#include "muz/rel/dl_relation_manager.h"
#include <sstream>

namespace datalog {

    // ------------------
    // lazy_table_plugin:

    symbol lazy_table_plugin::mk_name(table_plugin& p) {
        std::ostringstream strm;
        strm << "lazy_" << p.get_name();
        return symbol(strm.str().c_str());
    }

    table_base * lazy_table_plugin::mk_empty(const table_signature & s) {
        return alloc(lazy_table, alloc(lazy_table_base, *this, m_plugin.mk_empty(s)));
    }

    lazy_table const& lazy_table_plugin::get(table_base const& tb) { return dynamic_cast<lazy_table const&>(tb); }
    lazy_table& lazy_table_plugin::get(table_base& tb) { return dynamic_cast<lazy_table&>(tb); }
    lazy_table const* lazy_table_plugin::get(table_base const* tb) { return dynamic_cast<lazy_table const*>(tb); }
    lazy_table* lazy_table_plugin::get(table_base* tb) { return dynamic_cast<lazy_table*>(tb); }

    // --------------------------
    // lazy_table_plugin::join_fn

    class lazy_table_plugin::join_fn : public convenient_table_join_fn {
    public:
        join_fn(table_signature const& s1, table_signature const& s2, unsigned col_cnt, 
                unsigned const* cols1, unsigned const* cols2):
            convenient_table_join_fn(s1, s2, col_cnt, cols1, cols2) {}
                                  
        table_base* operator()(const table_base& _t1, const table_base& _t2) override {
            lazy_table const& t1 = get(_t1);
            lazy_table const& t2 = get(_t2);
            lazy_table_ref* tr = alloc(lazy_table_join, m_cols1.size(), m_cols1.c_ptr(), m_cols2.c_ptr(), t1, t2, get_result_signature());
            return alloc(lazy_table, tr);
        }
    };

    table_join_fn * lazy_table_plugin::mk_join_fn(
        const table_base & t1, const table_base & t2,
        unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (check_kind(t1) && check_kind(t2)) {
            return alloc(join_fn, t1.get_signature(), t2.get_signature(), col_cnt, cols1, cols2);
        }
        else {
            return nullptr;
        }
    }

    // ------------------------
    // lazy_table_plugin::union

    class lazy_table_plugin::union_fn : public table_union_fn {
    public:
        void operator()(table_base & _tgt, const table_base & _src, 
                        table_base * _delta) override {
            lazy_table& tgt = get(_tgt);
            lazy_table const& src = get(_src);
            lazy_table* delta = get(_delta);  
            table_base const* t_src = src.eval();
            table_base * t_tgt = tgt.eval();
            table_base * t_delta = delta?delta->eval():nullptr;
            verbose_action _t("union");
            table_union_fn* m = tgt.get_lplugin().get_manager().mk_union_fn(*t_tgt, *t_src, t_delta);
            SASSERT(m);
            (*m)(*t_tgt, *t_src, t_delta);
            dealloc(m);                
        }
    };


    table_union_fn* lazy_table_plugin::mk_union_fn(
        const table_base & tgt, const table_base & src, 
        const table_base * delta) {
        if (check_kind(tgt) && check_kind(src) && (!delta || check_kind(*delta))) {
            return alloc(union_fn);
        }
        else {
            return nullptr;
        }
    }        

    // --------------------------
    // lazy_table_plugin::project

    class lazy_table_plugin::project_fn : public convenient_table_project_fn {
    public:
        project_fn(table_signature const& orig_sig, unsigned cnt, unsigned const* cols): 
            convenient_table_project_fn(orig_sig, cnt, cols)
        {}

        table_base* operator()(table_base const& _t) override {
            lazy_table const& t = get(_t);
            return alloc(lazy_table, alloc(lazy_table_project, m_removed_cols.size(), m_removed_cols.c_ptr(), t, get_result_signature()));
        }
    };

    table_transformer_fn * lazy_table_plugin::mk_project_fn(
        const table_base & t, unsigned col_cnt, 
        const unsigned * removed_cols) {
        if (check_kind(t)) {
            return alloc(project_fn, t.get_signature(), col_cnt, removed_cols);
        }
        else {
            return nullptr;
        }
    }

    // -------------------------
    // lazy_table_plugin::rename

    class lazy_table_plugin::rename_fn : public convenient_table_rename_fn {
    public:
        rename_fn(table_signature const& orig_sig, unsigned cnt, unsigned const* cols): 
            convenient_table_rename_fn(orig_sig, cnt, cols)
        {}

        table_base* operator()(table_base const& _t) override {
            lazy_table const& t = get(_t);
            return alloc(lazy_table, alloc(lazy_table_rename, m_cycle.size(), m_cycle.c_ptr(), t, get_result_signature()));
        }
    };
    
    table_transformer_fn * lazy_table_plugin::mk_rename_fn(
        const table_base & t, unsigned col_cnt, 
        const unsigned * removed_cols) {
        if (check_kind(t)) {
            return alloc(rename_fn, t.get_signature(), col_cnt, removed_cols);
        }
        else {
            return nullptr;
        }
    }


    // -----------------------------------
    // lazy_table_plugin::filter_identical

    class lazy_table_plugin::filter_identical_fn : public table_mutator_fn {
        unsigned_vector          m_cols;
    public:
        filter_identical_fn(unsigned cnt, unsigned const* cols): m_cols(cnt, cols) {}
        
        void operator()(table_base& _t) override {
            lazy_table& t = get(_t);
            t.set(alloc(lazy_table_filter_identical, m_cols.size(), m_cols.c_ptr(), t));
        }
    };
    
    table_mutator_fn * lazy_table_plugin::mk_filter_identical_fn(
        const table_base & t, unsigned col_cnt, const unsigned * identical_cols) {
        if (check_kind(t)) {
            return alloc(filter_identical_fn, col_cnt, identical_cols);
        }
        else {
            return nullptr;
        }
    }


    // -------------------------------------
    // lazy_table_plugin::filter_interpreted

    class lazy_table_plugin::filter_interpreted_fn : public table_mutator_fn {
        app_ref  m_condition;
    public:
        filter_interpreted_fn(app_ref& p): m_condition(p) {}

        void operator()(table_base& _t) override {
            lazy_table& t = get(_t);
            t.set(alloc(lazy_table_filter_interpreted, t, m_condition));
        }
    };
    
    table_mutator_fn * lazy_table_plugin::mk_filter_interpreted_fn(
        const table_base & t, app* condition) {
        if (check_kind(t)) {
            app_ref cond(condition, get_ast_manager());
            return alloc(filter_interpreted_fn, cond);
        }
        else {
            return nullptr;
        }
    }
    
    // -------------------------------------
    // lazy_table_plugin::filter_by_negation

    class lazy_table_plugin::filter_by_negation_fn : public table_intersection_filter_fn {
        unsigned_vector m_cols1;
        unsigned_vector m_cols2;
    public:
        filter_by_negation_fn(unsigned cnt, unsigned const* cols1, unsigned const* cols2):
            m_cols1(cnt, cols1), m_cols2(cnt, cols2) {}
        void operator()(table_base & _t, const table_base & _intersected_obj) override {
            lazy_table& t = get(_t);
            lazy_table const& it = get(_intersected_obj);
            t.set(alloc(lazy_table_filter_by_negation, t, it, m_cols1, m_cols2));
        }
    };

    table_intersection_filter_fn * lazy_table_plugin::mk_filter_by_negation_fn(
        const table_base & t, 
        const table_base & negated_obj, unsigned joined_col_cnt, 
        const unsigned * t_cols, const unsigned * negated_cols) {
        if (check_kind(t) && check_kind(negated_obj)) {
            return alloc(filter_by_negation_fn, joined_col_cnt, t_cols, negated_cols);
        }
        else {
            return nullptr;
        }
    }


    // -------------------------------
    // lazy_table_plugin::filter_equal

    class lazy_table_plugin::filter_equal_fn : public table_mutator_fn {
        table_element m_value;
        unsigned m_col;
    public:
        filter_equal_fn(const table_element & value, unsigned col): 
            m_value(value),
            m_col(col)
        { }

        void operator()(table_base& _t) override {
            lazy_table& t = get(_t);
            t.set(alloc(lazy_table_filter_equal, m_col, m_value, t));
        }
    };
    
    table_mutator_fn * lazy_table_plugin::mk_filter_equal_fn(
        const table_base & t, const table_element & value, unsigned col) {
        if (check_kind(t)) {
            return alloc(filter_equal_fn, value, col);
        }
        else {
            return nullptr;
        }
    }

    table_plugin* lazy_table_plugin::mk_sparse(relation_manager& rm) {
        table_plugin* sp = rm.get_table_plugin(symbol("sparse"));
        SASSERT(sp);
        if (sp) {
            return alloc(lazy_table_plugin, *sp);
        }
        else {
            return nullptr;
        }
    }


    // ----------
    // lazy_table
    
    table_base * lazy_table::clone() const {
        table_base* t = eval();
        verbose_action _t("clone");
        return alloc(lazy_table, alloc(lazy_table_base, get_lplugin(), t->clone()));
    }
    table_base * lazy_table::complement(func_decl* p, const table_element * func_columns) const {
        table_base* t = eval()->complement(p, func_columns);
        return alloc(lazy_table, alloc(lazy_table_base, get_lplugin(), t));
    }
    bool lazy_table::empty() const {
        return m_ref->eval()->empty();
    }
    bool lazy_table::contains_fact(const table_fact & f) const {
        return m_ref->eval()->contains_fact(f);
    }
    void lazy_table::remove_fact(table_element const* fact) {
        m_ref->eval()->remove_fact(fact);
    }
    void lazy_table::remove_facts(unsigned fact_cnt, const table_fact * facts) {
        m_ref->eval()->remove_facts(fact_cnt, facts);
    }
    void lazy_table::remove_facts(unsigned fact_cnt, const table_element * facts) {
        m_ref->eval()->remove_facts(fact_cnt, facts);
    }
    void lazy_table::reset() {
        m_ref = alloc(lazy_table_base, get_lplugin(), get_lplugin().m_plugin.mk_empty(get_signature()));
    }
    void lazy_table::add_fact(table_fact const& f) {
        m_ref->eval()->add_fact(f);
    }
    table_base::iterator lazy_table::begin() const {
        return eval()->begin();
    }
    table_base::iterator lazy_table::end() const {
        return eval()->end();
    }
    table_base* lazy_table::eval() const {
        return m_ref->eval();
    }

    // -------------------------
    // eval


    table_base* lazy_table_join::force() {
        SASSERT(!m_table);
        table_base* t1 = m_t1->eval();
        table_base* t2 = m_t2->eval();
        verbose_action _t("join");
        table_join_fn* join = rm().mk_join_fn(*t1, *t2, m_cols1.size(), m_cols1.c_ptr(), m_cols2.c_ptr());
        m_table = (*join)(*t1, *t2);
        dealloc(join);        
        return m_table.get();
    }

    table_base* lazy_table_project::force() {
        SASSERT(!m_table);
        switch(m_src->kind()) {
        case LAZY_TABLE_JOIN: {
            lazy_table_join& src = dynamic_cast<lazy_table_join&>(*m_src);
            table_base* t1 = src.t1()->eval();
            table_base* t2 = src.t2()->eval();
            table_join_fn* j_fn = rm().mk_join_project_fn(*t1, *t2, src.cols1(), src.cols2(), m_cols);
            if (j_fn) {
                verbose_action _t("join_project");
                m_table = (*j_fn)(*t1, *t2);
                dealloc(j_fn);
            }
            break;
        }
        case LAZY_TABLE_FILTER_INTERPRETED: {
            lazy_table_filter_interpreted& src = dynamic_cast<lazy_table_filter_interpreted&>(*m_src);
            table_transformer_fn* tr = rm().mk_filter_interpreted_and_project_fn(*src.eval(), src.condition(), m_cols.size(), m_cols.c_ptr());
            if (tr) {
                verbose_action _t("filter_interpreted_project");
                m_table = (*tr)(*src.eval());
                dealloc(tr);
            }
            break;
        }
        case LAZY_TABLE_FILTER_EQUAL: {
            lazy_table_filter_equal& src = dynamic_cast<lazy_table_filter_equal&>(*m_src);
            table_base* t = src.eval();
            table_transformer_fn* tr = rm().mk_select_equal_and_project_fn(*t, src.value(), src.col());
            if (tr) {
                verbose_action _t("select_equal_project");
                m_table = (*tr)(*t);
                dealloc(tr);
            }
            break;
        }
        default:
            break;
        }
        if (m_table) {
            return m_table.get();
        }
        table_base* src = m_src->eval();
        verbose_action _t("project");
        table_transformer_fn* project = rm().mk_project_fn(*src, m_cols.size(), m_cols.c_ptr());
        SASSERT(project);
        m_table = (*project)(*src);
        dealloc(project);            
        return m_table.get();
    }

    table_base* lazy_table_rename::force() {
        SASSERT(!m_table);
        table_base* src = m_src->eval();
        verbose_action _t("rename");
        table_transformer_fn* rename = rm().mk_rename_fn(*src, m_cols.size(), m_cols.c_ptr());
        m_table = (*rename)(*src);
        dealloc(rename);                    
        return m_table.get();
    }
    
    table_base* lazy_table_filter_identical::force() {
        SASSERT(!m_table);
        m_table = m_src->eval();
        m_src->release_table();
        m_src = nullptr;
        verbose_action _t("filter_identical");
        table_mutator_fn* m = rm().mk_filter_identical_fn(*m_table, m_cols.size(), m_cols.c_ptr());
        SASSERT(m);
        (*m)(*m_table);
        dealloc(m);                    
        return m_table.get();
    }

    table_base* lazy_table_filter_equal::force() {
        SASSERT(!m_table);
        m_table = m_src->eval();
        m_src->release_table();
        m_src = nullptr;
        verbose_action _t("filter_equal");
        table_mutator_fn* m = rm().mk_filter_equal_fn(*m_table, m_value, m_col);
        SASSERT(m);
        (*m)(*m_table);
        dealloc(m);                
        return m_table.get();
    }

    table_base* lazy_table_filter_interpreted::force() {
        SASSERT(!m_table);
        m_table = m_src->eval();
        m_src->release_table();
        m_src = nullptr;
        verbose_action _t("filter_interpreted");
        table_mutator_fn* m = rm().mk_filter_interpreted_fn(*m_table, m_condition);
        SASSERT(m);
        (*m)(*m_table);
        dealloc(m);                
        return m_table.get();
    }

    table_base* lazy_table_filter_by_negation::force() {
        SASSERT(!m_table);
        m_table = m_tgt->eval();
        m_tgt->release_table();
        m_tgt = nullptr;

        switch(m_src->kind()) {

        case LAZY_TABLE_JOIN: {
            lazy_table_join& src = dynamic_cast<lazy_table_join&>(*m_src);
            table_base* t1 = src.t1()->eval();
            table_base* t2 = src.t2()->eval();
            verbose_action _t("filter_by_negation_join");
            table_intersection_join_filter_fn* jn = rm().mk_filter_by_negated_join_fn(*m_table, *t1, *t2, cols1(), cols2(), src.cols1(), src.cols2());
            if (jn) {
                (*jn)(*m_table, *t1, *t2);
                dealloc(jn);                
                return m_table.get();
            }
            break;
        }
        default:
            break;
        }
        table_base* src = m_src->eval();
        verbose_action _t("filter_by_negation");
        table_intersection_filter_fn* m = rm().mk_filter_by_negation_fn(*m_table, *src, m_cols1, m_cols2);
        SASSERT(m);
        (*m)(*m_table, *src);
        dealloc(m);                    
        return m_table.get();
    }
}
