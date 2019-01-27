/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_table_relation.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-14.

Revision History:

--*/


#include<string>
#include "muz/base/dl_context.h"
#include "muz/rel/dl_relation_manager.h"
#include "muz/rel/dl_table_relation.h"


namespace datalog {

    // -----------------------------------
    //
    // table_relation_plugin
    //
    // -----------------------------------

    symbol table_relation_plugin::create_plugin_name(const table_plugin &p) {
        std::string name = std::string("tr_") + p.get_name().bare_str();
        return symbol(name.c_str());
    }

    bool table_relation_plugin::can_handle_signature(const relation_signature & s) {
        table_signature tsig;
        return 
            get_manager().relation_signature_to_table(s, tsig) &&
            m_table_plugin.can_handle_signature(tsig);
    }


    relation_base * table_relation_plugin::mk_empty(const relation_signature & s) {
        table_signature tsig;
        if (!get_manager().relation_signature_to_table(s, tsig)) {
            return nullptr;
        }
        table_base * t = m_table_plugin.mk_empty(tsig);
        return alloc(table_relation, *this, s, t);
    }

    relation_base * table_relation_plugin::mk_full_relation(const relation_signature & s, func_decl* p, family_id kind) {
        table_signature tsig;
        if(!get_manager().relation_signature_to_table(s, tsig)) {
            return nullptr;
        }
        table_base * t = m_table_plugin.mk_full(p, tsig, kind);
        return alloc(table_relation, *this, s, t);
    }

    /**
      The newly created object takes ownership of the \c t object.
    */
    relation_base * table_relation_plugin::mk_from_table(const relation_signature & s, table_base * t) {
        if (&t->get_plugin() == &m_table_plugin)
            return alloc(table_relation, *this, s, t);
        table_relation_plugin& other = t->get_manager().get_table_relation_plugin(t->get_plugin());
        return alloc(table_relation, other, s, t);    
    }

    class table_relation_plugin::tr_join_project_fn : public convenient_relation_join_project_fn {
        scoped_ptr<table_join_fn> m_tfun;
    public:
        tr_join_project_fn(const relation_signature & s1, const relation_signature & s2, unsigned col_cnt, 
            const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt,
            const unsigned * removed_cols, table_join_fn * tfun) 
            : convenient_relation_join_project_fn(s1, s2, col_cnt, cols1, cols2, removed_col_cnt,
                    removed_cols), m_tfun(tfun) {}
        
        relation_base * operator()(const relation_base & t1, const relation_base & t2) override {
            SASSERT(t1.from_table());
            SASSERT(t2.from_table());
            table_relation_plugin & plugin = static_cast<table_relation_plugin &>(t1.get_plugin());

            const table_relation & tr1 = static_cast<const table_relation &>(t1);
            const table_relation & tr2 = static_cast<const table_relation &>(t2);
            
            table_base * tres = (*m_tfun)(tr1.get_table(), tr2.get_table());

            TRACE("dl_table_relation", tout << "# join => "; tres->display(tout););
            if(&tres->get_plugin()!=&plugin.m_table_plugin) {
                IF_VERBOSE(1, verbose_stream() << "new type returned\n";);
                //Operation returned a table of different type than the one which is associated with
                //this plugin. We need to get a correct table_relation_plugin and create the relation 
                //using it.
                return plugin.get_manager().get_table_relation_plugin(tres->get_plugin())
                    .mk_from_table(get_result_signature(), tres);
            }
            return plugin.mk_from_table(get_result_signature(), tres);
        }
    };

    relation_join_fn * table_relation_plugin::mk_join_fn(const relation_base & r1, const relation_base & r2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if(!r1.from_table() || !r2.from_table()) {
            return nullptr;
        }
        const table_relation & tr1 = static_cast<const table_relation &>(r1);
        const table_relation & tr2 = static_cast<const table_relation &>(r2);

        table_join_fn * tfun = get_manager().mk_join_fn(tr1.get_table(), tr2.get_table(), col_cnt, cols1, cols2);
        if(!tfun) {
            return nullptr;
        }

        return alloc(tr_join_project_fn, r1.get_signature(), r2.get_signature(), col_cnt, cols1, 
            cols2, 0, static_cast<const unsigned *>(nullptr), tfun);
    }

    relation_join_fn * table_relation_plugin::mk_join_project_fn(const relation_base & r1, 
            const relation_base & r2, unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, 
            unsigned removed_col_cnt, const unsigned * removed_cols) {
        if(!r1.from_table() || !r2.from_table()) {
            return nullptr;
        }
        const table_relation & tr1 = static_cast<const table_relation &>(r1);
        const table_relation & tr2 = static_cast<const table_relation &>(r2);

        table_join_fn * tfun = get_manager().mk_join_project_fn(tr1.get_table(), tr2.get_table(), joined_col_cnt, 
            cols1, cols2, removed_col_cnt, removed_cols);
        SASSERT(tfun);

        return alloc(tr_join_project_fn, r1.get_signature(), r2.get_signature(), joined_col_cnt, cols1, 
            cols2, removed_col_cnt, removed_cols, tfun);
    }


    class table_relation_plugin::tr_transformer_fn : public convenient_relation_transformer_fn {
        scoped_ptr<table_transformer_fn> m_tfun;
    public:
        tr_transformer_fn(const relation_signature & rsig, table_transformer_fn * tfun) 
            : m_tfun(tfun) { get_result_signature() = rsig; }

        relation_base * operator()(const relation_base & t) override {
            SASSERT(t.from_table());
            table_relation_plugin & plugin = static_cast<table_relation_plugin &>(t.get_plugin());

            const table_relation & tr = static_cast<const table_relation &>(t);
            
            table_base * tres = (*m_tfun)(tr.get_table());

            TRACE("dl_table_relation", tout << "# transform => "; tres->display(tout););
            if(&tres->get_plugin()!=&plugin.m_table_plugin) {
                //Transformation returned a table of different type than the one which is associated with this plugin.
                //We need to get a correct table_relation_plugin and create the relation using it.
                return plugin.get_manager().get_table_relation_plugin(tres->get_plugin())
                    .mk_from_table(get_result_signature(), tres);
            }
            return plugin.mk_from_table(get_result_signature(), tres);
        }
    };

    relation_transformer_fn * table_relation_plugin::mk_project_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * removed_cols) {
        if(!t.from_table()) {
            return nullptr;
        }
        const table_relation & tr = static_cast<const table_relation &>(t);

        table_transformer_fn * tfun = get_manager().mk_project_fn(tr.get_table(), col_cnt, removed_cols);
        SASSERT(tfun);

        relation_signature sig;
        relation_signature::from_project(t.get_signature(), col_cnt, removed_cols, sig);

        return alloc(tr_transformer_fn, sig, tfun);
    }

    relation_transformer_fn * table_relation_plugin::mk_rename_fn(const relation_base & t, unsigned permutation_cycle_len, 
        const unsigned * permutation_cycle) {
        if(!t.from_table()) {
            return nullptr;
        }
        const table_relation & tr = static_cast<const table_relation &>(t);

        table_transformer_fn * tfun = get_manager().mk_rename_fn(tr.get_table(), permutation_cycle_len, permutation_cycle);
        SASSERT(tfun);

        relation_signature sig;
        relation_signature::from_rename(t.get_signature(), permutation_cycle_len, permutation_cycle, sig);

        return alloc(tr_transformer_fn, sig, tfun);
    }

    relation_transformer_fn * table_relation_plugin::mk_permutation_rename_fn(const relation_base & t, 
        const unsigned * permutation) {
        if(!t.from_table()) {
            return nullptr;
        }
        const table_relation & tr = static_cast<const table_relation &>(t);

        table_transformer_fn * tfun = get_manager().mk_permutation_rename_fn(tr.get_table(), permutation);
        SASSERT(tfun);

        relation_signature sig;
        relation_signature::from_permutation_rename(t.get_signature(), permutation, sig);

        return alloc(tr_transformer_fn, sig, tfun);
    }

    relation_transformer_fn * table_relation_plugin::mk_select_equal_and_project_fn(const relation_base & t, 
            const relation_element & value, unsigned col) {
        if(!t.from_table()) {
            return nullptr;
        }
        const table_relation & tr = static_cast<const table_relation &>(t);

        table_element tvalue;
        get_manager().relation_to_table(tr.get_signature()[col], value, tvalue);

        table_transformer_fn * tfun = get_manager().mk_select_equal_and_project_fn(tr.get_table(), tvalue, col);
        SASSERT(tfun);
        relation_signature res_sig;
        relation_signature::from_project(t.get_signature(), 1, &col, res_sig);
        return alloc(tr_transformer_fn, res_sig, tfun);
    }

    /**
       Union functor that can unite table relation into any other relation (using any delta relation)
       by iterating through the table and calling \c add_fact of the target relation.
    */
    class table_relation_plugin::universal_target_union_fn : public relation_union_fn {
        void operator()(relation_base & tgt, const relation_base & src, relation_base * delta) override {
            SASSERT(src.from_table());

            const table_relation & tr_src = static_cast<const table_relation &>(src);
            relation_manager & rmgr = tr_src.get_manager();
            const relation_signature & sig = tr_src.get_signature();
            SASSERT(tgt.get_signature()==sig);
            SASSERT(!delta || delta->get_signature()==sig);
            
            table_base::iterator it  = tr_src.get_table().begin();
            table_base::iterator end = tr_src.get_table().end();

            table_fact tfact;
            relation_fact rfact(rmgr.get_context());
            for (; it != end; ++it) {
                it->get_fact(tfact);
                rmgr.table_fact_to_relation(sig, tfact, rfact);
                if(delta) {
                    if(!tgt.contains_fact(rfact)) {
                        tgt.add_new_fact(rfact);
                        delta->add_fact(rfact);
                    }
                }
                else {
                    tgt.add_fact(rfact);
                }
            }
            TRACE("dl_table_relation", tout << "# universal union => "; tgt.display(tout););
        }
    };

    class table_relation_plugin::tr_union_fn : public relation_union_fn {
        scoped_ptr<table_union_fn> m_tfun;
    public:
        tr_union_fn(table_union_fn * tfun) : m_tfun(tfun) {}

        void operator()(relation_base & tgt, const relation_base & src, relation_base * delta) override {
            SASSERT(tgt.from_table());
            SASSERT(src.from_table());
            SASSERT(!delta || delta->from_table());

            table_relation & tr_tgt = static_cast<table_relation &>(tgt);
            const table_relation & tr_src = static_cast<const table_relation &>(src);
            table_relation * tr_delta = static_cast<table_relation *>(delta);
            
            (*m_tfun)(tr_tgt.get_table(), tr_src.get_table(), tr_delta ? &tr_delta->get_table() : nullptr);

            TRACE("dl_table_relation", tout << "# union => "; tr_tgt.get_table().display(tout););
        }
    };

    relation_union_fn * table_relation_plugin::mk_union_fn(const relation_base & tgt, const relation_base & src,
        const relation_base * delta) {
        if(!src.from_table()) {
            return nullptr;
        }
        if(!tgt.from_table() || (delta && !delta->from_table())) {
            return alloc(universal_target_union_fn);
        }
        const table_relation & tr_tgt = static_cast<const table_relation &>(tgt);
        const table_relation & tr_src = static_cast<const table_relation &>(src);
        const table_relation * tr_delta = static_cast<const table_relation *>(delta);

        table_union_fn * tfun = get_manager().mk_union_fn(tr_tgt.get_table(), tr_src.get_table(), 
            tr_delta ? &tr_delta->get_table() : nullptr);
        SASSERT(tfun);

        return alloc(tr_union_fn, tfun);
    }


    class table_relation_plugin::tr_mutator_fn : public relation_mutator_fn {
        scoped_ptr<table_mutator_fn> m_tfun;
    public:
        tr_mutator_fn(table_mutator_fn * tfun) : m_tfun(tfun) {}

        void operator()(relation_base & r) override {
            SASSERT(r.from_table());
            table_relation & tr = static_cast<table_relation &>(r);            
            (*m_tfun)(tr.get_table());
            TRACE("dl_table_relation", tout << "# mutator => "; tr.get_table().display(tout););
        }
    };

    relation_mutator_fn * table_relation_plugin::mk_filter_identical_fn(const relation_base & t, unsigned col_cnt, 
        const unsigned * identical_cols) {
        if(!t.from_table()) {
            return nullptr;
        }
        const table_relation & tr = static_cast<const table_relation &>(t);

        table_mutator_fn * tfun = get_manager().mk_filter_identical_fn(tr.get_table(), col_cnt, identical_cols);
        SASSERT(tfun);
        return alloc(tr_mutator_fn, tfun);
    }

    relation_mutator_fn * table_relation_plugin::mk_filter_equal_fn(const relation_base & t, const relation_element & value, 
        unsigned col) {
        if(!t.from_table()) {
            return nullptr;
        }
        const table_relation & tr = static_cast<const table_relation &>(t);

        table_element tvalue;
        get_manager().relation_to_table(tr.get_signature()[col], value, tvalue);

        table_mutator_fn * tfun = get_manager().mk_filter_equal_fn(tr.get_table(), tvalue, col);
        SASSERT(tfun);
        return alloc(tr_mutator_fn, tfun);
    }

    relation_mutator_fn * table_relation_plugin::mk_filter_interpreted_fn(const relation_base & t, app * condition) {
        bool condition_needs_transforming = false;
        if(!t.from_table() || condition_needs_transforming) {
            return nullptr;
        }
        const table_relation & tr = static_cast<const table_relation &>(t);
        table_mutator_fn * tfun = get_manager().mk_filter_interpreted_fn(tr.get_table(), condition);
        SASSERT(tfun);
        return alloc(tr_mutator_fn, tfun);
    }

    relation_transformer_fn * table_relation_plugin::mk_filter_interpreted_and_project_fn(const relation_base & t,
            app * condition, unsigned removed_col_cnt, const unsigned * removed_cols) {
        if (!t.from_table())
            return nullptr;

        const table_relation & tr = static_cast<const table_relation &>(t);
        table_transformer_fn * tfun = get_manager().mk_filter_interpreted_and_project_fn(tr.get_table(),
            condition, removed_col_cnt, removed_cols);
        SASSERT(tfun);

        relation_signature sig;
        relation_signature::from_project(t.get_signature(), removed_col_cnt, removed_cols, sig);
        return alloc(tr_transformer_fn, sig, tfun);
    }

    class table_relation_plugin::tr_intersection_filter_fn : public relation_intersection_filter_fn {
        scoped_ptr<table_intersection_filter_fn> m_tfun;
    public:
        tr_intersection_filter_fn(table_intersection_filter_fn * tfun) : m_tfun(tfun) {}

        void operator()(relation_base & r, const relation_base & src) override {
            SASSERT(r.from_table()); 
            SASSERT(src.from_table());

            table_relation & tr = static_cast<table_relation &>(r);
            const table_relation & tr_src = static_cast<const table_relation &>(src);
            
            (*m_tfun)(tr.get_table(), tr_src.get_table());
            TRACE("dl_table_relation", tout << "# negation_filter => "; tr.get_table().display(tout););
        }
    };

    relation_intersection_filter_fn * table_relation_plugin::mk_filter_by_intersection_fn(const relation_base & r, 
            const relation_base & src, unsigned joined_col_cnt, const unsigned * r_cols, const unsigned * src_cols) {
        if(!r.from_table() || !src.from_table()) {
            return nullptr;
        }
        const table_relation & tr = static_cast<const table_relation &>(r);
        const table_relation & tr_neg = static_cast<const table_relation &>(src);
        table_intersection_filter_fn * tfun = get_manager().mk_filter_by_intersection_fn(tr.get_table(), 
            tr_neg.get_table(), joined_col_cnt, r_cols, src_cols);
        if(!tfun) {
            return nullptr;
        }

        return alloc(tr_intersection_filter_fn, tfun);
    }


    relation_intersection_filter_fn * table_relation_plugin::mk_filter_by_negation_fn(const relation_base & r, 
            const relation_base & negated_rel, unsigned joined_col_cnt, 
            const unsigned * r_cols, const unsigned * negated_cols) {
        if(!r.from_table() || !negated_rel.from_table()) {
            return nullptr;
        }
        const table_relation & tr = static_cast<const table_relation &>(r);
        const table_relation & tr_neg = static_cast<const table_relation &>(negated_rel);
        table_intersection_filter_fn * tfun = get_manager().mk_filter_by_negation_fn(tr.get_table(), 
            tr_neg.get_table(), joined_col_cnt, r_cols, negated_cols);
        SASSERT(tfun);

        return alloc(tr_intersection_filter_fn, tfun);
    }


    // -----------------------------------
    //
    // table_relation
    //
    // -----------------------------------

    void table_relation::add_table_fact(const table_fact & f) {
        get_table().add_fact(f);
    }

    void table_relation::add_fact(const relation_fact & f) {
        SASSERT(f.size()==get_signature().size());
        table_fact vals;
        get_manager().relation_fact_to_table(get_signature(), f, vals);
        get_table().add_fact(vals);
        TRACE("dl_table_relation", tout << "# add fact => "; get_table().display(tout););
    }

    bool table_relation::contains_fact(const relation_fact & f) const {
        table_fact vals;
        get_manager().relation_fact_to_table(get_signature(), f, vals);
        return get_table().contains_fact(vals);
    }

    relation_base * table_relation::clone() const {
        table_base * tres = get_table().clone();
        return get_plugin().mk_from_table(get_signature(), tres);
    }

    relation_base * table_relation::complement(func_decl* p) const {
        table_base * tres = get_table().complement(p);
        return get_plugin().mk_from_table(get_signature(), tres);
    }

    void table_relation::display_tuples(func_decl & pred, std::ostream & out) const {
        context & ctx = get_manager().get_context();
        unsigned arity = pred.get_arity();

        out << "Tuples in " << pred.get_name() << ": \n";

        table_base::iterator it  = get_table().begin();
        table_base::iterator end = get_table().end();

        table_fact fact;
        for (; it != end; ++it) {
            it->get_fact(fact);
            
            out << "\t(";

            for(unsigned i=0;i<arity;i++) {
                if(i!=0) {
                    out << ',';
                }

                table_element sym_num = fact[i];

                relation_sort sort = pred.get_domain(i);

                out << ctx.get_argument_name(&pred, i) << '=';
                ctx.print_constant_name(sort, sym_num, out);
                out << '(' << sym_num << ')';
            }
            out << ")\n";

        }
    }

};

