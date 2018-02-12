/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_check_table.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2010-11-15
    

Revision History:

--*/


#include "muz/rel/dl_check_table.h"
#include "muz/rel/dl_table.h"


namespace datalog {
    
    bool check_table_plugin::can_handle_signature(table_signature const& s) {
        return m_tocheck.can_handle_signature(s) && m_checker.can_handle_signature(s);
    }


    check_table & check_table_plugin::get(table_base& r) {
        return static_cast<check_table&>(r);
    }
    
    check_table const & check_table_plugin::get(table_base const& r) {
        return static_cast<check_table const &>(r);
    }

     table_base& check_table_plugin::checker(table_base& r) { return *get(r).m_checker; }
     table_base const& check_table_plugin::checker(table_base const& r) { return *get(r).m_checker; }
     table_base* check_table_plugin::checker(table_base* r) { return r?(get(*r).m_checker):nullptr; }
     table_base const* check_table_plugin::checker(table_base const* r) { return r?(get(*r).m_checker):nullptr; }
     table_base& check_table_plugin::tocheck(table_base& r) { return *get(r).m_tocheck; }
     table_base const& check_table_plugin::tocheck(table_base const& r) { return *get(r).m_tocheck; }
     table_base* check_table_plugin::tocheck(table_base* r) { return r?(get(*r).m_tocheck):nullptr; }
     table_base const* check_table_plugin::tocheck(table_base const* r) { return r?(get(*r).m_tocheck):nullptr; }

    table_base * check_table_plugin::mk_empty(const table_signature & s) {
        IF_VERBOSE(1, verbose_stream() << __FUNCTION__ << "\n";);
        table_base* checker = m_checker.mk_empty(s);
        table_base* tocheck = m_tocheck.mk_empty(s);
        return alloc(check_table, *this, s, tocheck, checker);
    }
    
    class check_table_plugin::join_fn : public table_join_fn {
        scoped_ptr<table_join_fn> m_tocheck;
        scoped_ptr<table_join_fn> m_checker;
    public:
        join_fn(check_table_plugin& p, 
                const table_base & t1, const table_base & t2,
                unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
            m_tocheck = p.get_manager().mk_join_fn(tocheck(t1), tocheck(t2), col_cnt, cols1, cols2);
            m_checker = p.get_manager().mk_join_fn(checker(t1), checker(t2), col_cnt, cols1, cols2);
        }

        table_base* operator()(const table_base & t1, const table_base & t2) override {
            IF_VERBOSE(1, verbose_stream() << __FUNCTION__ << "\n";);
            table_base* ttocheck = (*m_tocheck)(tocheck(t1), tocheck(t2));
            table_base* tchecker = (*m_checker)(checker(t1), checker(t2));
            check_table* result = alloc(check_table, get(t1).get_plugin(), ttocheck->get_signature(), ttocheck, tchecker);
            return result;
        }
    };

    table_join_fn * check_table_plugin::mk_join_fn(const table_base & t1, const table_base & t2,
                                                  unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (!check_kind(t1) || !check_kind(t2)) {
            return nullptr;
        }
        return alloc(join_fn, *this, t1, t2, col_cnt, cols1, cols2);    
    }

    class check_table_plugin::join_project_fn : public table_join_fn {
        scoped_ptr<table_join_fn> m_tocheck;
        scoped_ptr<table_join_fn> m_checker;
    public:
        join_project_fn(check_table_plugin& p, const table_base & t1, const table_base & t2,
                        unsigned col_cnt, const unsigned * cols1, const unsigned * cols2,
                        unsigned removed_col_cnt, const unsigned * removed_cols) {
            m_tocheck = p.get_manager().mk_join_project_fn(tocheck(t1), tocheck(t2), col_cnt, cols1, cols2, removed_col_cnt, removed_cols);
            m_checker = p.get_manager().mk_join_project_fn(checker(t1), checker(t2), col_cnt, cols1, cols2, removed_col_cnt, removed_cols);
        }

        table_base* operator()(const table_base & t1, const table_base & t2) override {
            table_base* ttocheck = (*m_tocheck)(tocheck(t1), tocheck(t2));
            table_base* tchecker = (*m_checker)(checker(t1), checker(t2));
            check_table* result = alloc(check_table, get(t1).get_plugin(), ttocheck->get_signature(), ttocheck, tchecker);
            return result;
        }
    };

    table_join_fn * check_table_plugin::mk_join_project_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
            const unsigned * removed_cols) {
        if (!check_kind(t1) || !check_kind(t2)) {
            return nullptr;
        }
        return alloc(join_project_fn, *this, t1, t2, col_cnt, cols1, cols2, removed_col_cnt, removed_cols);    
    }

    class check_table_plugin::union_fn : public table_union_fn {
        scoped_ptr<table_union_fn> m_tocheck;
        scoped_ptr<table_union_fn> m_checker;
    public:
        union_fn(check_table_plugin& p, table_base const& tgt, const table_base& src, table_base const* delta) {
            m_tocheck = p.get_manager().mk_union_fn(tocheck(tgt), tocheck(src), tocheck(delta));
            m_checker = p.get_manager().mk_union_fn(checker(tgt), checker(src), checker(delta));
        }
        
        void operator()(table_base& tgt, const table_base& src, table_base* delta) override {
            IF_VERBOSE(1, verbose_stream() << __FUNCTION__ << "\n";);
            (*m_tocheck)(tocheck(tgt), tocheck(src), tocheck(delta));
            (*m_checker)(checker(tgt), checker(src), checker(delta));
            get(tgt).well_formed();
            if (delta) {
                get(*delta).well_formed();
            }
        }
    };

    table_union_fn * check_table_plugin::mk_union_fn(const table_base & tgt, const table_base & src, const table_base * delta) {
        if (!check_kind(tgt) || !check_kind(src) || (delta && !check_kind(*delta))) {
            return nullptr;
        }
        return alloc(union_fn, *this, tgt, src, delta);
        
    }

    class check_table_plugin::project_fn : public table_transformer_fn {
        scoped_ptr<table_transformer_fn> m_checker;
        scoped_ptr<table_transformer_fn> m_tocheck;
    public:
        project_fn(check_table_plugin& p, const table_base & t, unsigned col_cnt, const unsigned * removed_cols) {
            m_checker = p.get_manager().mk_project_fn(checker(t), col_cnt, removed_cols);
            m_tocheck = p.get_manager().mk_project_fn(tocheck(t), col_cnt, removed_cols);
        }

        table_base* operator()(table_base const& src) override {
            table_base* tchecker = (*m_checker)(checker(src));
            table_base* ttocheck = (*m_tocheck)(tocheck(src));
            check_table* result = alloc(check_table, get(src).get_plugin(), tchecker->get_signature(), ttocheck, tchecker);
            return result;
        }
    };
    
    table_transformer_fn * check_table_plugin::mk_project_fn(const table_base & t, unsigned col_cnt, const unsigned * removed_cols) {
        if (!check_kind(t)) {
            return nullptr;
        }
        return alloc(project_fn, *this, t, col_cnt, removed_cols);        
    }

    class check_table_plugin::select_equal_and_project_fn : public table_transformer_fn {
        scoped_ptr<table_transformer_fn> m_checker;
        scoped_ptr<table_transformer_fn> m_tocheck;
    public:
        select_equal_and_project_fn(check_table_plugin& p, const table_base & t, const table_element & value, unsigned col) {
            m_checker = p.get_manager().mk_select_equal_and_project_fn(checker(t), value, col);
            m_tocheck = p.get_manager().mk_select_equal_and_project_fn(tocheck(t), value, col);
        }

        table_base* operator()(table_base const& src) override {
            table_base* tchecker = (*m_checker)(checker(src));
            table_base* ttocheck = (*m_tocheck)(tocheck(src));
            check_table* result = alloc(check_table, get(src).get_plugin(), tchecker->get_signature(), ttocheck, tchecker);
            return result;
        }
    };

    table_transformer_fn * check_table_plugin::mk_select_equal_and_project_fn(const table_base & t, 
            const table_element & value, unsigned col) {
        if (!check_kind(t)) {
            return nullptr;
        }
        return alloc(select_equal_and_project_fn, *this, t, value, col);        
    }

    class check_table_plugin::rename_fn : public table_transformer_fn {
        scoped_ptr<table_transformer_fn> m_checker;
        scoped_ptr<table_transformer_fn> m_tocheck;
    public:
        rename_fn(check_table_plugin& p, const table_base & t, unsigned cycle_len, unsigned const* cycle) {
            m_checker = p.get_manager().mk_rename_fn(checker(t), cycle_len, cycle);
            m_tocheck = p.get_manager().mk_rename_fn(tocheck(t), cycle_len, cycle);
        }

        table_base* operator()(table_base const& src) override {
            IF_VERBOSE(1, verbose_stream() << __FUNCTION__ << "\n";);
            table_base* tchecker = (*m_checker)(checker(src));
            table_base* ttocheck = (*m_tocheck)(tocheck(src));
            check_table* result = alloc(check_table, get(src).get_plugin(), ttocheck->get_signature(), ttocheck, tchecker);
            return result;
        }
    };
    
    table_transformer_fn * check_table_plugin::mk_rename_fn(const table_base & t, unsigned len, const unsigned * cycle) {
        if (!check_kind(t)) {
            return nullptr;
        }
        return alloc(rename_fn, *this, t, len, cycle);
    }

    class check_table_plugin::filter_identical_fn : public table_mutator_fn {
        scoped_ptr<table_mutator_fn> m_checker;
        scoped_ptr<table_mutator_fn> m_tocheck;
    public:
        filter_identical_fn(check_table_plugin& p, const table_base & t,unsigned cnt, unsigned const* cols)
        {
            m_checker = p.get_manager().mk_filter_identical_fn(checker(t), cnt, cols);
            m_tocheck = p.get_manager().mk_filter_identical_fn(tocheck(t), cnt, cols);        
        }

        void operator()(table_base & t) override {
            (*m_checker)(checker(t));
            (*m_tocheck)(tocheck(t));
            get(t).well_formed();
        }
    };

    table_mutator_fn * check_table_plugin::mk_filter_identical_fn(const table_base & t, unsigned col_cnt, 
        const unsigned * identical_cols) {
        if (check_kind(t)) {
            return alloc(filter_identical_fn, *this, t, col_cnt, identical_cols);
        }
        return nullptr;
    }

    class check_table_plugin::filter_equal_fn : public table_mutator_fn {
        scoped_ptr<table_mutator_fn> m_checker;
        scoped_ptr<table_mutator_fn> m_tocheck;
    public:
        filter_equal_fn(check_table_plugin& p, const table_base & t, const table_element & v, unsigned col)
        {
            m_checker = p.get_manager().mk_filter_equal_fn(checker(t), v, col);
            m_tocheck = p.get_manager().mk_filter_equal_fn(tocheck(t), v, col); 
        }

        void operator()(table_base& src) override {
            (*m_checker)(checker(src));
            (*m_tocheck)(tocheck(src));
            get(src).well_formed();
        }
    };

    table_mutator_fn * check_table_plugin::mk_filter_equal_fn(const table_base & t, const table_element & value, unsigned col) {
        if (check_kind(t)) {
            return alloc(filter_equal_fn, *this, t, value, col);
        }
        return nullptr;
    }

    class check_table_plugin::filter_interpreted_fn : public table_mutator_fn {
        scoped_ptr<table_mutator_fn> m_checker;
        scoped_ptr<table_mutator_fn> m_tocheck;
    public:
        filter_interpreted_fn(check_table_plugin& p, const table_base & t, app * condition)
        {
            m_checker = p.get_manager().mk_filter_interpreted_fn(checker(t), condition);
            m_tocheck = p.get_manager().mk_filter_interpreted_fn(tocheck(t), condition); 
        }

        void operator()(table_base& src) override {
            (*m_checker)(checker(src));
            (*m_tocheck)(tocheck(src));
            get(src).well_formed();
        }
    };

    table_mutator_fn * check_table_plugin::mk_filter_interpreted_fn(const table_base & t, app * condition) {
        if (check_kind(t)) {
            return alloc(filter_interpreted_fn, *this, t, condition);
        }
        return nullptr;
    }

    class check_table_plugin::filter_interpreted_and_project_fn : public table_transformer_fn {
        scoped_ptr<table_transformer_fn> m_checker;
        scoped_ptr<table_transformer_fn> m_tocheck;
    public:
        filter_interpreted_and_project_fn(check_table_plugin& p, const table_base & t, app * condition,
            unsigned removed_col_cnt, const unsigned * removed_cols)
        {
            m_checker = p.get_manager().mk_filter_interpreted_and_project_fn(checker(t), condition, removed_col_cnt, removed_cols);
            m_tocheck = p.get_manager().mk_filter_interpreted_and_project_fn(tocheck(t), condition, removed_col_cnt, removed_cols); 
        }

        table_base* operator()(table_base const& src) override {
            table_base* tchecker = (*m_checker)(checker(src));
            table_base* ttocheck = (*m_tocheck)(tocheck(src));
            check_table* result = alloc(check_table, get(src).get_plugin(), ttocheck->get_signature(), ttocheck, tchecker);
            return result;
        }
    };

    table_transformer_fn * check_table_plugin::mk_filter_interpreted_and_project_fn(const table_base & t,
        app * condition, unsigned removed_col_cnt, const unsigned * removed_cols) {
        if (check_kind(t)) {
            return alloc(filter_interpreted_and_project_fn, *this, t, condition, removed_col_cnt, removed_cols);
        }
        return nullptr;
    }

    class check_table_plugin::filter_by_negation_fn : public table_intersection_filter_fn {
        scoped_ptr<table_intersection_filter_fn> m_checker;
        scoped_ptr<table_intersection_filter_fn> m_tocheck;
    public:
        filter_by_negation_fn(
            check_table_plugin& p,
            const table_base & t, 
            const table_base & negated_obj, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * negated_cols) {
            m_checker = p.get_manager().mk_filter_by_negation_fn(checker(t), checker(negated_obj), joined_col_cnt, t_cols, negated_cols);
            m_tocheck = p.get_manager().mk_filter_by_negation_fn(tocheck(t), tocheck(negated_obj), joined_col_cnt, t_cols, negated_cols);
        }

        void operator()(table_base& src, table_base const& negated_obj) override {
            IF_VERBOSE(1, verbose_stream() << __FUNCTION__ << "\n";);
            (*m_checker)(checker(src), checker(negated_obj));
            (*m_tocheck)(tocheck(src), tocheck(negated_obj));
            get(src).well_formed();
        }
        
    };

    table_intersection_filter_fn * check_table_plugin::mk_filter_by_negation_fn(const table_base & t, 
        const table_base & negated_obj, unsigned joined_col_cnt, 
        const unsigned * t_cols, const unsigned * negated_cols) {
        if (check_kind(t) && check_kind(negated_obj)) {
            return alloc(filter_by_negation_fn, *this, t, negated_obj, joined_col_cnt, t_cols, negated_cols);
        }
        return nullptr;
    }

    // ------------------
    // check_table


    check_table::check_table(check_table_plugin & p, const table_signature & sig):
        table_base(p, sig) {
        (well_formed());
    }

    check_table::check_table(check_table_plugin & p, const table_signature & sig, table_base* tocheck, table_base* checker):
        table_base(p, sig),
        m_checker(checker),
        m_tocheck(tocheck) {            
        well_formed();
    }

    check_table::~check_table() {
        m_tocheck->deallocate();
        m_checker->deallocate();
    }

    bool check_table::well_formed() const {
        get_plugin().m_count++;
        iterator it = m_tocheck->begin(), end = m_tocheck->end();
        for (; it != end; ++it) {
            table_fact fact;
            it->get_fact(fact);
            if (!m_checker->contains_fact(fact)) {
                m_tocheck->display(verbose_stream());
                m_checker->display(verbose_stream());
                verbose_stream() << get_plugin().m_count << "\n";
                UNREACHABLE();
                fatal_error(0);
                return false;
            }
        }
        iterator it2 = m_checker->begin(), end2 = m_checker->end();
        for (; it2 != end2; ++it2) {
            table_fact fact;
            it2->get_fact(fact);
            if (!m_tocheck->contains_fact(fact)) {
                m_tocheck->display(verbose_stream());
                m_checker->display(verbose_stream());
                verbose_stream() << get_plugin().m_count << "\n";
                UNREACHABLE();
                fatal_error(0);
                return false;
            }
        }
        return true;
    }

    bool check_table::empty() const {
        if (m_tocheck->empty() != m_checker->empty()) {
            m_tocheck->display(verbose_stream());
            m_checker->display(verbose_stream());
            verbose_stream() << get_plugin().m_count << "\n";
            fatal_error(0);
        }
        return m_tocheck->empty();
    }


    void check_table::add_fact(const table_fact & f) {
        IF_VERBOSE(1, verbose_stream() << __FUNCTION__ << "\n";);
        m_tocheck->add_fact(f);
        m_checker->add_fact(f);
        well_formed();        
    }

    void check_table::remove_fact(const table_element*  f) {
        IF_VERBOSE(1, verbose_stream() << __FUNCTION__ << "\n";);
        m_tocheck->remove_fact(f);
        m_checker->remove_fact(f);
        well_formed();        
    }

    bool check_table::contains_fact(const table_fact & f) const {
        return m_checker->contains_fact(f);
    }
    
    table_base * check_table::clone() const {        
        IF_VERBOSE(1, verbose_stream() << __FUNCTION__ << "\n";);
        check_table* result = alloc(check_table, get_plugin(), get_signature(), m_tocheck->clone(), m_checker->clone());
        return result;
    }

    table_base * check_table::complement(func_decl* p, const table_element * func_columns) const {
        check_table* result = alloc(check_table, get_plugin(), get_signature(), m_tocheck->complement(p, func_columns), m_checker->complement(p, func_columns));
        return result;
    }

};

