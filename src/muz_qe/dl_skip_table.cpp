/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_skip_table.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner)
    Leonardo de Moura (leonardo) 2010-10-14
    

Revision History:

--*/

#ifndef _EXTERNAL_RELEASE

#include "dl_skip_table.h"
#include "dl_table.h"
#include "dl_context.h"


namespace datalog {
    
    skip_table & skip_table_plugin::get(table_base& r) {
        return static_cast<skip_table&>(r);
    }
    
    skip_table const & skip_table_plugin::get(table_base const& r) {
        return static_cast<skip_table const &>(r);
    }

    table_base * skip_table_plugin::mk_empty(const table_signature & s) {
        return alloc(skip_table, *this, s);
    }

    skip_table* skip_table_plugin::mk_join(
        table_base const& t1, table_base const& t2, table_signature const& result_sig,
        unsigned_vector const& cols1, unsigned_vector const& cols2) {
        skip_table const& s1 = get(t1);
        skip_table const& s2 = get(t2);        
        imdd_manager& m = s1.get_imdd_manager();        
        imdd_ref pr(m);
        m.mk_join(s1.get_imdd(), s2.get_imdd(), pr, cols1, cols2);
        return alloc(skip_table, s1.get_plugin(), result_sig, pr);           
    }

    skip_table* skip_table_plugin::mk_join_project(
        table_base const& t1, table_base const& t2, table_signature const& result_sig,
        unsigned_vector const& cols1, unsigned_vector const& cols2,
        unsigned_vector const& proj_cols) {

        skip_table const& s1 = get(t1);
        skip_table const& s2 = get(t2);
        imdd_manager& m = s1.get_imdd_manager();
        imdd_ref pr(m);
        m.mk_join_project(s1.get_imdd(), s2.get_imdd(), pr, cols1, cols2, proj_cols);
        return alloc(skip_table, s1.get_plugin(), result_sig, pr);           
    }
    
    class skip_table_plugin::join_fn : public convenient_table_join_fn {
    public:
        join_fn(const table_base & t1, const table_base & t2,
                unsigned col_cnt, const unsigned * cols1, const unsigned * cols2):
            convenient_table_join_fn(t1.get_signature(), t2.get_signature(), col_cnt, cols1, cols2) {
        }

        virtual table_base* operator()(const table_base & t1, const table_base & t2) {
            return skip_table_plugin::mk_join(t1, t2, get_result_signature(), m_cols1, m_cols2);
        }
    };

    table_join_fn * skip_table_plugin::mk_join_fn(const table_base & t1, const table_base & t2,
                                                  unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (check_kind(t1) && check_kind(t2)) {
            return alloc(join_fn, t1, t2, col_cnt, cols1, cols2);    
        }
        TRACE("dl", tout << "could not handle operation\n";);
        return 0;
    }

    class skip_table_plugin::join_project_fn : public convenient_table_join_project_fn {
    public:
        join_project_fn(const table_base & t1, const table_base & t2,
                        unsigned col_cnt, const unsigned * cols1, const unsigned * cols2,
                        unsigned removed_col_cnt, const unsigned * removed_cols):
            convenient_table_join_project_fn(t1.get_signature(), t2.get_signature(), col_cnt, cols1, cols2, 
                                             removed_col_cnt, removed_cols) {
        }

        virtual table_base* operator()(const table_base & t1, const table_base & t2) {
            return skip_table_plugin::mk_join_project(t1, t2, get_result_signature(), m_cols1, m_cols2, m_removed_cols);
        }
    };
    


    table_join_fn * skip_table_plugin::mk_join_project_fn(
        const table_base & t1, const table_base & t2,
        unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, 
        unsigned removed_col_cnt, const unsigned * removed_cols) {
        if (check_kind(t1) && check_kind(t2)) {
            return alloc(join_project_fn, t1, t2, joined_col_cnt, cols1, cols2, removed_col_cnt, removed_cols);    
        }
        TRACE("dl", tout << "could not handle operation\n";);
        return 0;
    }

    class skip_table_plugin::union_fn : public table_union_fn {
    public:
        virtual void operator()(table_base& tgt, const table_base& src, table_base* delta) {
            skip_table& s1 = get(tgt);
            skip_table const& s2 = get(src);
            imdd_manager& m = s1.get_imdd_manager();
            imdd_ref r(m);
            m.mk_union(s1.get_imdd(), s2.get_imdd(), r);
            if (delta) {
                skip_table& d = get(*delta);
                if (m.is_subset(r, s1.get_imdd())) {
                    d.update(m.mk_empty(s1.get_signature().size()));
                }
                else {
                    d.update(r);
                }
            }
            s1.update(r);
        }
    };

    table_union_fn * skip_table_plugin::mk_union_fn(const table_base & tgt, const table_base & src, const table_base * delta) {
        if (check_kind(tgt) && check_kind(src) && (!delta || check_kind(*delta))) {
            return alloc(union_fn);
        }
        TRACE("dl", tout << "could not handle operation\n";);
        return 0;        
    }

    skip_table* skip_table_plugin::mk_project(table_base const& src, table_signature const& result_sig, unsigned_vector const& cols) {
        skip_table const& s = get(src);
        imdd_manager& m = s.get_imdd_manager();            
        imdd_ref pr(m);
        m.mk_project(s.get_imdd(), pr, cols.size(), cols.c_ptr());
        return alloc(skip_table, s.get_plugin(), result_sig, pr);
    }


    class skip_table_plugin::project_fn : public convenient_table_project_fn {
    public:
        project_fn(table_signature const& orig_sig, unsigned col_cnt, unsigned const* removed_cols): 
          convenient_table_project_fn(orig_sig, col_cnt, removed_cols) {}

        table_base* operator()(table_base const& src) {
            return mk_project(src, get_result_signature(), m_removed_cols);
        }
    };
    
    table_transformer_fn * skip_table_plugin::mk_project_fn(const table_base & t, unsigned col_cnt, const unsigned * removed_cols) {
        if (check_kind(t)) {
            return alloc(project_fn, t.get_signature(), col_cnt, removed_cols);        
        }
        TRACE("dl", tout << "could not handle operation\n";);
        return 0;
    }

    class skip_table_plugin::rename_fn : public convenient_table_rename_fn {

        void swap2(imdd_ref& n, unsigned col1, unsigned col2) {
            imdd_manager& m = n.get_manager();
            imdd_ref tmp(m);
            if (col1 == col2) {
                return;
            }
            if (col1 > col2) {
                std::swap(col1, col2);
            }
            for (unsigned i = col1; i < col2; ++i) {
                m.mk_swap(n, tmp, i);
                n = tmp;
            }
            for (unsigned i = col2 - 1; i > col1; ) {
                --i;
                m.mk_swap(n, tmp, i);
                n = tmp;
            }                       
        }
    public:
        rename_fn(table_signature const& sig, unsigned cycle_len, unsigned const* cycle):
          convenient_rename_fn(sig, cycle_len, cycle) {}

        table_base* operator()(table_base const& src) {
            TRACE("skip", 
                for (unsigned i = 0; i < m_cycle.size(); ++i) {
                    tout << m_cycle[i] << " ";
                }
                tout << "\n";
                src.display(tout););
            skip_table const& s = get(src);
            imdd_ref n(s.m_imdd, s.get_imdd_manager());
            unsigned cycle_len = m_cycle.size();
            unsigned col1, col2;
            // TBD: review this for proper direction
            for (unsigned i = 0; i + 1 < cycle_len; ++i) {
                col1 = m_cycle[i];
                col2 = m_cycle[i+1];
                swap2(n, col1, col2);
            }
            if (cycle_len > 2) {
                col1 = m_cycle[cycle_len-1];
                col2 = m_cycle[0];
                swap2(n, col1, col2);
            }
            skip_table* res = alloc(skip_table, s.get_plugin(), get_result_signature(), n);
            TRACE("skip",res->display(tout););
            return res;
        }
    };
    
    table_transformer_fn * skip_table_plugin::mk_rename_fn(const table_base & t, unsigned len, const unsigned * cycle) {
        if (check_kind(t)) {
            return alloc(rename_fn, t.get_signature(), len, cycle);
        }
        TRACE("dl", tout << "could not handle operation\n";);
        return 0;
    }

    class skip_table_plugin::filter_identical_fn : public table_mutator_fn {
        unsigned_vector m_cols;

    public:
        filter_identical_fn(unsigned cnt, unsigned const* cols):
          m_cols(cnt, cols)
        {}

        void operator()(table_base & t) {
            skip_table& s = get(t);
            imdd_manager& m = s.get_imdd_manager();              
            m.mk_filter_identical(s.get_imdd(), s.m_imdd, m_cols.size(), m_cols.c_ptr(), true);
        }
    };

    table_mutator_fn * skip_table_plugin::mk_filter_identical_fn(const table_base & t, unsigned col_cnt, 
        const unsigned * identical_cols) {
        if (check_kind(t)) {
            return alloc(filter_identical_fn, col_cnt, identical_cols);
        }
        TRACE("dl", tout << "could not handle operation\n";);
        return 0;
    }

    class skip_table_plugin::filter_equal_fn : public table_mutator_fn {
        unsigned m_col;
        unsigned m_value;
    public:
        filter_equal_fn(const table_base & t, const table_element & v, unsigned col):
            m_col(col),
            m_value(static_cast<unsigned>(v))
        {
            SASSERT(v <= UINT_MAX);
        }

        virtual void operator()(table_base& src) {
            skip_table& s = get(src);
            imdd_manager& m = s.get_imdd_manager();
            m.mk_filter_equal(s.get_imdd(), s.m_imdd, m_col, m_value);
        }
    };

    table_mutator_fn * skip_table_plugin::mk_filter_equal_fn(const table_base & t, const table_element & value, 
        unsigned col) {
        if (check_kind(t)) {
            return alloc(filter_equal_fn, t, value, col);
        }
        TRACE("dl", tout << "could not handle operation\n";);
        return 0;
    }

 class skip_table_plugin::filter_not_equal_fn : public table_mutator_fn {
        unsigned m_col;
        unsigned m_value;
    public:
        filter_not_equal_fn(const table_base & t, const table_element & v, unsigned col):
            m_col(col),
            m_value(static_cast<unsigned>(v))
        {
            SASSERT(v <= UINT_MAX);
        }

        virtual void operator()(table_base& src) {
            skip_table& s = get(src);
            imdd_manager& m = s.get_imdd_manager();
            m.mk_filter_disequal(s.get_imdd(), s.m_imdd, m_col, m_value);
        }
    };

    table_mutator_fn * skip_table_plugin::mk_filter_not_equal_fn(const table_base & t, const table_element & value, 
        unsigned col) {
        if (check_kind(t)) {
            return alloc(filter_not_equal_fn, t, value, col);
        }
        TRACE("dl", tout << "could not handle operation\n";);
        return 0;
    }

    class skip_table_plugin::filter_distinct_fn : public table_mutator_fn {
        unsigned m_col1;
        unsigned m_col2;
    public:
        filter_distinct_fn(const table_base & t, unsigned col1, unsigned col2):
            m_col1(col1),
            m_col2(col2) {
        }

        virtual void operator()(table_base& src) {
            skip_table& s = get(src);
            imdd_manager& m = s.get_imdd_manager();
            m.mk_filter_distinct(s.get_imdd(), s.m_imdd, m_col1, m_col2);
        }
    };

    table_mutator_fn * skip_table_plugin::mk_filter_distinct_fn(const table_base & t, unsigned col1, unsigned col2) {
        if (check_kind(t)) {
            return alloc(filter_distinct_fn, t, col1, col2);
        }
        TRACE("dl", tout << "could not handle operation\n";);
        return 0;
    }

    //
    // The default implementation uses an iterator
    // if the condition is a comparison <, <=, then interval table native will be an advantage.
    // 
    table_mutator_fn * skip_table_plugin::mk_filter_interpreted_fn(const table_base & t, app * condition) {
        ast_manager& m = get_ast_manager();
        dl_decl_util& util = get_context().get_decl_util();
        uint64 value;

        if (m.is_eq(condition)) {
            expr* x = condition->get_arg(0);
            expr* y = condition->get_arg(1);
            if (is_var(y)) {
                std::swap(x,y);
            }
            if (is_var(x) && is_var(y)) {
                unsigned cols[2] = { to_var(x)->get_idx(), to_var(y)->get_idx() };
                return mk_filter_identical_fn(t, 2, cols);
            }            
            if (is_var(x) && util.is_numeral_ext(y, value)) {
                return mk_filter_equal_fn(t, value, to_var(x)->get_idx());
            }
        }

        if (m.is_not(condition) && is_app(condition->get_arg(0))) {
            condition = to_app(condition->get_arg(0));
            if (m.is_eq(condition)) {
                expr* x = condition->get_arg(0);
                expr* y = condition->get_arg(1);
                if (is_var(y)) {
                    std::swap(x,y);
                }
                if (is_var(x) && is_var(y)) {
                    return mk_filter_distinct_fn(t, to_var(x)->get_idx(), to_var(y)->get_idx());
                }      
                if (is_var(x) && util.is_numeral_ext(y, value)) {
                    return mk_filter_not_equal_fn(t, value, to_var(x)->get_idx());
                }      
            }
        }
        
        TRACE("dl", tout << "could not handle operation\n";);
        return 0;
    }

    class skip_table_plugin::filter_by_negation_fn : public convenient_table_negation_filter_fn {
    public:
        filter_by_negation_fn(
            const table_base & tgt, const table_base & neg, 
            unsigned joined_col_cnt, const unsigned * t_cols, const unsigned * negated_cols) 
            : convenient_table_negation_filter_fn(tgt, neg, joined_col_cnt, t_cols, negated_cols) {

        }

        //
        // Compute 
        //        { (x,y) | t(x,y) & ! exists z . negated_obj(x,z) }
        //
        // 1. Project z
        // 2. Join with result.
        //

        virtual void operator()(table_base & tgt0, const table_base & neg0) {
            skip_table & tgt = get(tgt0);
            const skip_table & neg = get(neg0);
            unsigned_vector cols2(m_cols2);
            unsigned_vector proj_cols;
            table_base* t1 = 0;
            if (!m_all_neg_bound) {
                unsigned_vector proj_cols, remap;
                table_signature sig2;
                table_signature const& neg_sig = neg.get_signature();
                for (unsigned i = 0, j = 0; i < m_bound.size(); ++i) {
                    if (m_bound[i]) {
                        remap.push_back(j++);
                        sig2.push_back(neg_sig[i]);
                    }
                    else {
                        proj_cols.push_back(i);
                        remap.push_back(0);
                    }
                }
                for (unsigned i = 0; i < cols2.size(); ++i) {
                    cols2[i] = remap[cols2[i]];
                }
                skip_table* t0 = skip_table_plugin::mk_project(neg, sig2, proj_cols);
                t1 = t0->complement();                
                t0->deallocate();
                proj_cols.reset();
            }
            else {
                t1 = neg.complement();
            }
            for (unsigned i = 0; i < t1->get_signature().size(); ++i) {
                proj_cols.push_back(tgt0.get_signature().size()+i);
            }
            skip_table* t2 = skip_table_plugin::mk_join_project(tgt0, *t1, tgt0.get_signature(), m_cols1, cols2, proj_cols);            
            t1->deallocate();
            tgt.update(*t2);
            t2->deallocate();
        }
    };

    table_intersection_filter_fn * skip_table_plugin::mk_filter_by_negation_fn(
        const table_base & t, 
        const table_base & negated_obj, unsigned joined_col_cnt, 
        const unsigned * t_cols, const unsigned * negated_cols) {
        
        if (check_kind(t) && check_kind(negated_obj)) {
            return alloc(filter_by_negation_fn, t, negated_obj, joined_col_cnt, t_cols, negated_cols);
        }
        TRACE("dl", tout << "could not handle operation\n";);
        return 0;
    }

    bool skip_table_plugin::can_handle_signature(table_signature const& sig) {
        for (unsigned i = 0; i < sig.size(); ++i) {
            if (sig[i] >= UINT_MAX) {
                return false;
            }
        }
        return true;        
    }

    // ------------------
    // skip_table


    skip_table::skip_table(skip_table_plugin & p, const table_signature & sig):
        table_base(p, sig),
        m_imdd(p.get_imdd_manager().mk_empty(sig.size()), p.get_imdd_manager()) {            
        SASSERT(well_formed());
    }

    skip_table::skip_table(skip_table_plugin & p, const table_signature & sig, imdd* m):
        table_base(p, sig),
        m_imdd(m, p.get_imdd_manager()) {            
            SASSERT(well_formed());
    }

    skip_table::~skip_table() {
    }


    bool skip_table::well_formed() const {
        table_signature const& sig = get_signature();
        return 
            get_plugin().can_handle_signature(sig) &&
            (get_imdd()->get_arity() == sig.size());
    }

    bool skip_table::empty() const {
        return get_imdd()->empty();
    }

    void skip_table::update(imdd* n) {
        m_imdd = n;
        SASSERT(well_formed());
    }

    void skip_table::add_fact(const table_fact & f) {
        imdd_manager& m = get_plugin().get_imdd_manager();
        unsigned const* fact = get_fact(f.c_ptr());
        m.add_fact(get_imdd(), m_imdd, f.size(), fact);
        SASSERT(well_formed());
    }

    void skip_table::remove_fact(const table_element* f) {
        imdd_manager& m = get_imdd_manager();
        unsigned const* fact = get_fact(f);
        m.remove_facts(get_imdd(), m_imdd, get_signature().size(), fact, fact);
    }

    bool skip_table::contains_fact(const table_fact & f) const {
        imdd_manager& m = get_imdd_manager();
        unsigned const* fact = get_fact(f.c_ptr());
        return m.contains(get_imdd(), f.size(), fact);
    }
    
    table_base * skip_table::clone() const {
        return alloc(skip_table, get_plugin(), get_signature(), get_imdd());
    }

    table_base * skip_table::complement() const {
        imdd_manager& m = get_plugin().get_imdd_manager();        
        table_signature const& sig = get_signature();
        unsigned_vector mins, maxs;
        for (unsigned i = 0; i < sig.size(); ++i) {
            SASSERT(sig[i] < UINT_MAX);
            mins.push_back(0);
            maxs.push_back(static_cast<unsigned>(sig[i]));                
        }
        imdd_ref cmpl(m);
        m.mk_complement(get_imdd(), cmpl, sig.size(), mins.c_ptr(), maxs.c_ptr());
        return alloc(skip_table, get_plugin(), get_signature(), cmpl);
    }

    unsigned const* skip_table::get_fact(table_element const* f) const {
        table_signature const& sig = get_signature();
        const_cast<unsigned_vector&>(m_fact).reset();
        for (unsigned i = 0; i < sig.size(); ++i) {
            const_cast<unsigned_vector&>(m_fact).push_back(static_cast<unsigned>(f[i]));
            SASSERT(f[i] < UINT_MAX);
        }
        return m_fact.c_ptr();
    }



    class skip_table::our_iterator_core : public table_base::iterator_core {
        skip_table const&      m_table;
        imdd_manager::iterator m_iterator;

        class our_row : public row_interface {
            const our_iterator_core & m_parent;
        public:
            our_row(const our_iterator_core & parent) : row_interface(parent.m_table), m_parent(parent) {}

            virtual void get_fact(table_fact & result) const {
                result.reset();
                unsigned arity = m_parent.m_iterator.get_arity();
                unsigned const* values = *(m_parent.m_iterator);
                for (unsigned i = 0; i < arity; ++i) {
                    result.push_back(values[i]);
                }
            }
            virtual table_element operator[](unsigned col) const {
                SASSERT(col < m_parent.m_iterator.get_arity());
                unsigned const* values = *(m_parent.m_iterator);
                return values[col];
            }
        };

        our_row m_row_obj;

    public:
        struct b {};
        struct e {};

        our_iterator_core(skip_table const& t, b):
            m_table(t),
            m_iterator(t.m_imdd.get_manager(), t.get_imdd()),
            m_row_obj(*this) {}

        our_iterator_core(skip_table const& t, e):
            m_table(t),
            m_iterator(),
            m_row_obj(*this) {}

        virtual bool is_finished() const {
            return m_iterator == imdd_manager::iterator();
        }

        virtual row_interface & operator*() {
            SASSERT(!is_finished());
            return m_row_obj;
        }

        virtual void operator++() {
            SASSERT(!is_finished());
            ++m_iterator;
        }
    };
    

    table_base::iterator skip_table::begin() const {
        return mk_iterator(alloc(our_iterator_core, *this, our_iterator_core::b()));
    }

    table_base::iterator skip_table::end() const {
        return mk_iterator(alloc(our_iterator_core, *this, our_iterator_core::e()));
    }

    unsigned skip_table::get_size_estimate_rows() const {
        imdd_manager& m = get_plugin().get_imdd_manager();
        size_t sz = m.get_num_rows(get_imdd());
        unsigned sz0 = static_cast<unsigned>(sz);
        SASSERT (sz == sz0 && "we need to use size_t or big-ints for row count");
        return sz0;
    }

    unsigned skip_table::get_size_estimate_bytes() const {
        imdd_manager& m = get_plugin().get_imdd_manager();
        return m.memory(get_imdd());
    }

};

#endif
