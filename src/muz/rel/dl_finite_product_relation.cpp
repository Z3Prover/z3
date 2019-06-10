/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_finite_product_relation.cpp

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
#include "muz/rel/dl_finite_product_relation.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/th_rewriter.h"

namespace datalog {

    //static variables

    const table_sort finite_product_relation::s_rel_idx_sort = INT_MAX;

    void universal_delete(finite_product_relation* ptr) {
        ptr->deallocate();
    }


    // -----------------------------------
    //
    // finite_product_relation_plugin
    //
    // -----------------------------------

    finite_product_relation & finite_product_relation_plugin::get(relation_base & r) {
        SASSERT(r.get_plugin().is_finite_product_relation());
        return static_cast<finite_product_relation &>(r);
    }

    const finite_product_relation & finite_product_relation_plugin::get(const relation_base & r) {
        SASSERT(r.get_plugin().is_finite_product_relation());
        return static_cast<const finite_product_relation &>(r);
    }

    finite_product_relation * finite_product_relation_plugin::get(relation_base * r) {
        SASSERT(!r || r->get_plugin().is_finite_product_relation());
        return static_cast<finite_product_relation *>(r);
    }

    const finite_product_relation * finite_product_relation_plugin::get(const relation_base * r) {
        SASSERT(!r || r->get_plugin().is_finite_product_relation());
        return static_cast<const finite_product_relation *>(r);
    }

    symbol finite_product_relation_plugin::get_name(relation_plugin & inner_plugin) {
        std::string str = std::string("fpr_")+inner_plugin.get_name().bare_str();
        return symbol(str.c_str());
    }

    finite_product_relation_plugin & finite_product_relation_plugin::get_plugin(relation_manager & rmgr, 
            relation_plugin & inner) {
        finite_product_relation_plugin * res;
        if(!rmgr.try_get_finite_product_relation_plugin(inner, res)) {
            res = alloc(finite_product_relation_plugin, inner, rmgr);
            rmgr.register_plugin(res);
        }
        return *res;
    }

    finite_product_relation_plugin::finite_product_relation_plugin(relation_plugin & inner_plugin, 
                relation_manager & manager) 
            : relation_plugin(get_name(inner_plugin), manager, ST_FINITE_PRODUCT_RELATION), 
            m_inner_plugin(inner_plugin), m_spec_store(*this) {
    }

    void finite_product_relation_plugin::initialize(family_id fid) { 
        relation_plugin::initialize(fid);
        m_spec_store.add_available_kind(get_kind());
    }

    family_id finite_product_relation_plugin::get_relation_kind(finite_product_relation & r, 
            const bool * table_columns) {
        const relation_signature & sig = r.get_signature();
        svector<bool> table_cols_vect(sig.size(), table_columns);
        return m_spec_store.get_relation_kind(sig, rel_spec(table_cols_vect));
    }

    void finite_product_relation_plugin::get_all_possible_table_columns(relation_manager & rmgr, 
            const relation_signature & s, svector<bool> & table_columns) {
        SASSERT(table_columns.empty());
        unsigned s_sz = s.size();
        for(unsigned i=0; i<s_sz; i++) {
            table_sort t_sort;
            //we don't care about the result of the conversion, just that it can be converted
            bool can_be_table_column = rmgr.relation_sort_to_table(s[i], t_sort);
            table_columns.push_back(can_be_table_column);
        }
    }

    void finite_product_relation_plugin::split_signatures(const relation_signature & s, 
            table_signature & table_sig, relation_signature & remaining_sig) {
        relation_manager & rmgr = get_manager();
        unsigned n = s.size();
        for(unsigned i=0; i<n; i++) {
            table_sort t_sort;
            if(rmgr.relation_sort_to_table(s[i], t_sort)) {
                table_sig.push_back(t_sort);
            }
            else {
                remaining_sig.push_back(s[i]);
            }
        }
    }

    void finite_product_relation_plugin::split_signatures(const relation_signature & s, const bool * table_columns,
            table_signature & table_sig, relation_signature & remaining_sig) {
        relation_manager & rmgr = get_manager();
        unsigned n = s.size();
        for(unsigned i=0; i<n; i++) {
            if(table_columns[i]) {
                table_sort t_sort;
                VERIFY( rmgr.relation_sort_to_table(s[i], t_sort) );
                table_sig.push_back(t_sort);
            }
            else {
                remaining_sig.push_back(s[i]);
            }
        }
    }

    bool finite_product_relation_plugin::can_handle_signature(const relation_signature & s) {
        table_signature table_sig;
        relation_signature remaining_sig;
        split_signatures(s, table_sig, remaining_sig);
        return m_inner_plugin.can_handle_signature(remaining_sig) 
            && get_manager().try_get_appropriate_plugin(table_sig);
    }

    relation_base * finite_product_relation_plugin::mk_empty(const relation_signature & s) {
        svector<bool> table_columns;
        get_all_possible_table_columns(s, table_columns);
#ifndef _EXTERNAL_RELEASE
        unsigned s_sz = s.size();
        unsigned rel_col_cnt = 0;
        for(unsigned i=0; i<s_sz; i++) {
            if(!table_columns[i]) {
                rel_col_cnt++;
            }
        }
        if(get_manager().get_context().dbg_fpr_nonempty_relation_signature() && rel_col_cnt==0) {
            //if the relation is empty, we will use the second half of the signature for the relation
            relation_signature candidate_rel_sig;
            unsigned rel_sig_ofs = s.size()/2;
            unsigned rel_sig_sz = s.size()-rel_sig_ofs;
            candidate_rel_sig.append(rel_sig_sz, s.c_ptr()+rel_sig_ofs);
            if(m_inner_plugin.can_handle_signature(candidate_rel_sig)) {
                for(unsigned i=rel_sig_ofs; i<s_sz; i++) {
                    table_columns[i] = false;
                }
            }

        }
#endif
        return mk_empty(s, table_columns.c_ptr());
    }

    finite_product_relation * finite_product_relation_plugin::mk_empty(const relation_signature & s, 
            const bool * table_columns, family_id inner_kind) {
        //find table_plugin that can handle the table signature
        table_signature table_sig;
        relation_signature remaining_sig;
        split_signatures(s, table_columns, table_sig, remaining_sig);
        table_sig.push_back(finite_product_relation::s_rel_idx_sort);
        table_sig.set_functional_columns(1);
        table_plugin & tplugin = get_manager().get_appropriate_plugin(table_sig);
        return alloc(finite_product_relation, *this, s, table_columns, tplugin, m_inner_plugin, inner_kind);
    }

    finite_product_relation * finite_product_relation_plugin::mk_empty(const finite_product_relation & original) {
        return get(mk_empty(original.get_signature(), original.get_kind()));
    }

    relation_base * finite_product_relation_plugin::mk_empty(const relation_base & original) {
        SASSERT(&original.get_plugin()==this);
        return mk_empty(get(original));
    }

    relation_base * finite_product_relation_plugin::mk_empty(const relation_signature & s, family_id kind) {
        rel_spec spec;
        m_spec_store.get_relation_spec(s, kind, spec);
        return mk_empty(s, spec.m_table_cols.c_ptr(), spec.m_inner_kind);
    }


    relation_base * finite_product_relation_plugin::mk_full(func_decl* p, const relation_signature & s) {
        finite_product_relation * res = get(mk_empty(s));
        res->complement_self(p);
        return res;
    }

    bool finite_product_relation_plugin::can_convert_to_table_relation(const finite_product_relation & r) {
        return r.m_other_sig.empty();
    }

    table_relation * finite_product_relation_plugin::to_table_relation(const finite_product_relation & r) {
        SASSERT(can_convert_to_table_relation(r));
        r.garbage_collect(true);
        //now all rows in the table will correspond to rows in the resulting table_relation

        const table_base & t = r.get_table();

        unsigned removed_col = t.get_signature().size()-1;
        scoped_ptr<table_transformer_fn> project_fun = 
            get_manager().mk_project_fn(r.get_table(), 1, &removed_col);

        table_base * res_table = (*project_fun)(t);
        SASSERT(res_table->get_signature().functional_columns()==0);
        return static_cast<table_relation *>(get_manager().mk_table_relation(r.get_signature(), res_table));
    }


    bool finite_product_relation_plugin::can_be_converted(const relation_base & r) {
        if(&r.get_plugin()==&get_inner_plugin()) {
            //can be converted by mk_from_inner_relation
            return true;
        }
        if(r.from_table()) {
            //We can convert directly from table plugin only if the inner plugin can handle empty signatures.

            //TODO: If the inner plugin cannot handle empty signatures, we may try to move some of the
            //table columns into the inner relation signature.
            return get_inner_plugin().can_handle_signature(relation_signature());
        }
        return false;
    }

    finite_product_relation * finite_product_relation_plugin::mk_from_table_relation(const table_relation & r) {
        func_decl* pred = nullptr;
        const relation_signature & sig = r.get_signature();
        const table_base & t = r.get_table();
        table_plugin & tplugin = r.get_table().get_plugin();

        relation_signature inner_sig; //empty signature for the inner relation
        if(!get_inner_plugin().can_handle_signature(inner_sig)) {
            return nullptr;
        }

        table_signature idx_singleton_sig;
        idx_singleton_sig.push_back(finite_product_relation::s_rel_idx_sort);
        idx_singleton_sig.set_functional_columns(1);

        scoped_rel<table_base> idx_singleton;
        if(tplugin.can_handle_signature(idx_singleton_sig)) {
            idx_singleton = tplugin.mk_empty(idx_singleton_sig);
        }
        else {
            idx_singleton = get_manager().mk_empty_table(idx_singleton_sig);
        }
        table_fact idx_singleton_fact;
        idx_singleton_fact.push_back(0);
        idx_singleton->add_fact(idx_singleton_fact);

        scoped_ptr<table_join_fn> join_fun = get_manager().mk_join_fn(t, *idx_singleton, 0, nullptr, nullptr);
        SASSERT(join_fun);
        scoped_rel<table_base> res_table = (*join_fun)(t, *idx_singleton);

        svector<bool> table_cols(sig.size(), true);
        finite_product_relation * res = mk_empty(sig, table_cols.c_ptr());

        //this one does not need to be deleted -- it will be taken over by \c res in the \c init function
        relation_base * inner_rel = get_inner_plugin().mk_full(pred, inner_sig, get_inner_plugin().get_kind());

        relation_vector rels;
        rels.push_back(inner_rel);

        res->init(*res_table, rels, true);
        return res;
    }

    finite_product_relation * finite_product_relation_plugin::mk_from_inner_relation(const relation_base & r) {
        SASSERT(&r.get_plugin()==&get_inner_plugin());
        const relation_signature & sig = r.get_signature();

        table_signature idx_singleton_sig;
        idx_singleton_sig.push_back(finite_product_relation::s_rel_idx_sort);
        idx_singleton_sig.set_functional_columns(1);

        scoped_rel<table_base> idx_singleton = get_manager().mk_empty_table(idx_singleton_sig);
        table_fact idx_singleton_fact;
        idx_singleton_fact.push_back(0);
        idx_singleton->add_fact(idx_singleton_fact);

        svector<bool> table_cols(sig.size(), false);
        finite_product_relation * res = mk_empty(sig, table_cols.c_ptr());

        relation_vector rels;
        rels.push_back(r.clone());

        res->init(*idx_singleton, rels, true);
        return res;
    }

    class finite_product_relation_plugin::converting_join_fn : public convenient_relation_join_fn {
        finite_product_relation_plugin & m_plugin;
        scoped_ptr<relation_join_fn> m_native_join;

        finite_product_relation * convert(const relation_base & r) {
            SASSERT(&r.get_plugin()!=&m_plugin);
            if(&r.get_plugin()==&m_plugin.get_inner_plugin()) {
                return m_plugin.mk_from_inner_relation(r);
            }
            SASSERT(r.from_table());
            const table_relation & tr = static_cast<const table_relation &>(r);
            finite_product_relation * res = m_plugin.mk_from_table_relation(tr);
            SASSERT(res);
            return res;
        }

    public:
        converting_join_fn(finite_product_relation_plugin & plugin, const relation_signature & sig1, 
            const relation_signature & sig2, unsigned col_cnt, const unsigned * cols1, 
            const unsigned * cols2) 
            : convenient_relation_join_fn(sig1, sig2, col_cnt, cols1, cols2),
            m_plugin(plugin) {}

        relation_base * operator()(const relation_base & r1, const relation_base & r2) override {
            scoped_rel<finite_product_relation> r1_conv;
            if(&r1.get_plugin()!=&m_plugin) {
                r1_conv = convert(r1);
            }
            scoped_rel<finite_product_relation> r2_conv;
            if(&r2.get_plugin()!=&m_plugin) {
                r2_conv = convert(r2);
            }

            const finite_product_relation & fpr1 = r1_conv ? *r1_conv : get(r1);
            const finite_product_relation & fpr2 = r2_conv ? *r2_conv : get(r2);

            SASSERT(&fpr1.get_plugin()==&m_plugin);
            SASSERT(&fpr2.get_plugin()==&m_plugin);

            if(!m_native_join) {
                m_native_join = m_plugin.get_manager().mk_join_fn(fpr1, fpr2, m_cols1, m_cols2, false);
            }
            return (*m_native_join)(fpr1, fpr2);
        }
    };


    class finite_product_relation_plugin::join_fn : public convenient_relation_join_fn {
        scoped_ptr<table_join_fn> m_tjoin_fn;
        scoped_ptr<relation_join_fn> m_rjoin_fn;
        
        unsigned_vector m_t_joined_cols1;
        unsigned_vector m_t_joined_cols2;
        unsigned_vector m_r_joined_cols1;
        unsigned_vector m_r_joined_cols2;

        //Column equalities betweet table and inner relations.
        //The columns numbers correspont to the columns of the table/inner relation 
        //in the result of the join operation
        unsigned_vector m_tr_table_joined_cols;
        unsigned_vector m_tr_rel_joined_cols;

        scoped_ptr<relation_mutator_fn> m_filter_tr_identities;

        scoped_ptr<table_transformer_fn> m_tjoined_second_rel_remover;

        //determines which columns of the result are table columns and which are in the inner relation
        svector<bool> m_res_table_columns;

    public:
        class join_maker : public table_row_mutator_fn {
            join_fn & m_parent;
            const finite_product_relation & m_r1;
            const finite_product_relation & m_r2;
            relation_vector & m_rjoins;
        public:
            join_maker(join_fn & parent, const finite_product_relation & r1, const finite_product_relation & r2,
                    relation_vector & rjoins)
                : m_parent(parent), m_r1(r1), m_r2(r2), m_rjoins(rjoins) {}

            bool operator()(table_element * func_columns) override {
                const relation_base & or1 = m_r1.get_inner_rel(func_columns[0]);
                const relation_base & or2 = m_r2.get_inner_rel(func_columns[1]);
                SASSERT(&or1);
                SASSERT(&or2);
                unsigned new_rel_num = m_rjoins.size();
                m_rjoins.push_back(m_parent.do_rjoin(or1, or2));
                func_columns[0]=new_rel_num;
                return true;
            }
        };

        join_fn(const finite_product_relation & r1, const finite_product_relation & r2, unsigned col_cnt, 
                    const unsigned * cols1, const unsigned * cols2) 
                : convenient_relation_join_fn(r1.get_signature(), r2.get_signature(), col_cnt, cols1, cols2) {
            unsigned second_table_after_join_ofs = r1.m_table2sig.size();
            unsigned second_inner_rel_after_join_ofs = r1.m_other2sig.size();
            for(unsigned i=0;i<col_cnt; i++) {
                if(!r1.is_table_column(cols1[i]) && !r2.is_table_column(cols2[i])) {
                    m_r_joined_cols1.push_back(r1.m_sig2other[cols1[i]]);
                    m_r_joined_cols2.push_back(r2.m_sig2other[cols2[i]]);
                }
                else if(r1.is_table_column(cols1[i]) && r2.is_table_column(cols2[i])) {
                    m_t_joined_cols1.push_back(r1.m_sig2table[cols1[i]]);
                    m_t_joined_cols2.push_back(r2.m_sig2table[cols2[i]]);
                }
                else if(!r1.is_table_column(cols1[i]) && r2.is_table_column(cols2[i])) {
                    m_tr_rel_joined_cols.push_back(r1.m_sig2other[cols1[i]]);
                    m_tr_table_joined_cols.push_back(second_table_after_join_ofs + r2.m_sig2table[cols2[i]]);
                }
                else {
                    SASSERT(r1.is_table_column(cols1[i]) && !r2.is_table_column(cols2[i]));
                    m_tr_table_joined_cols.push_back(r1.m_sig2table[cols1[i]]);
                    m_tr_rel_joined_cols.push_back(second_inner_rel_after_join_ofs + r2.m_sig2other[cols2[i]]);
                }
            }
            m_tjoin_fn = r1.get_manager().mk_join_fn(r1.get_table(), r2.get_table(), m_t_joined_cols1.size(), 
                m_t_joined_cols1.c_ptr(), m_t_joined_cols2.c_ptr());
            SASSERT(m_tjoin_fn);


            unsigned r1_sig_sz = r1.get_signature().size();
            unsigned r2_sig_sz = r2.get_signature().size();
            for(unsigned i=0; i<r1_sig_sz; i++) {
                m_res_table_columns.push_back(r1.is_table_column(i));
            }
            for(unsigned i=0; i<r2_sig_sz; i++) {
                m_res_table_columns.push_back(r2.is_table_column(i));
            }

        }
        
        relation_base * do_rjoin(const relation_base & r1, const relation_base & r2) {
            if(!m_rjoin_fn) {
                m_rjoin_fn = r1.get_manager().mk_join_fn(r1, r2, m_r_joined_cols1, m_r_joined_cols2, false);
            }
            SASSERT(m_rjoin_fn);
            return (*m_rjoin_fn)(r1, r2);
        }

        relation_base * operator()(const relation_base & rb1, const relation_base & rb2) override {
            finite_product_relation_plugin & plugin = get(rb1).get_plugin();
            relation_manager & rmgr = plugin.get_manager();

            const finite_product_relation & r1 = get(rb1);
            const finite_product_relation & r2 = get(rb2);

            scoped_rel<table_base> tjoined = (*m_tjoin_fn)(r1.get_table(), r2.get_table());

            relation_vector joined_orelations;

            {
                join_maker * mutator = alloc(join_maker, *this, r1, r2, joined_orelations); //dealocated in inner_join_mapper
                scoped_ptr<table_mutator_fn> inner_join_mapper = rmgr.mk_map_fn(*tjoined, mutator);
                (*inner_join_mapper)(*tjoined);
            }


            if(!m_tjoined_second_rel_remover) {
                unsigned removed_col = tjoined->get_signature().size()-1;
                m_tjoined_second_rel_remover = rmgr.mk_project_fn(*tjoined, 1, &removed_col);
            }
            //remove the second functional column from tjoined to get a table that corresponds
            //to the table signature of the resulting relation
            scoped_rel<table_base> res_table = (*m_tjoined_second_rel_remover)(*tjoined);

            relation_plugin & res_oplugin = 
                joined_orelations.empty() ? r1.m_other_plugin : joined_orelations.back()->get_plugin();

            //TODO: Maybe we might want to specify a particular relation kind, instead of just null_family_id.
            //It would however need to be somehow inferred for the new signature.

            finite_product_relation * res = alloc(finite_product_relation, r1.get_plugin(), get_result_signature(),
                m_res_table_columns.c_ptr(), res_table->get_plugin(), res_oplugin, null_family_id);

            res->init(*res_table, joined_orelations, true);

            if(!m_tr_table_joined_cols.empty()) {
                //There were some shared variables between the table and the relation part.
                //We enforce those equalities here.
                if(!m_filter_tr_identities) {
                    m_filter_tr_identities = plugin.mk_filter_identical_pairs(*res, m_tr_table_joined_cols.size(),
                        m_tr_table_joined_cols.c_ptr(), m_tr_rel_joined_cols.c_ptr());
                    SASSERT(m_filter_tr_identities);
                }
                (*m_filter_tr_identities)(*res);
            }
            return res;
        }
    };




    relation_join_fn * finite_product_relation_plugin::mk_join_fn(const relation_base & rb1, const relation_base & rb2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if(!check_kind(rb1) || !check_kind(rb2)) {
            bool r1foreign = &rb1.get_plugin()!=this;
            bool r2foreign = &rb2.get_plugin()!=this;
            if( (!r1foreign || can_be_converted(rb1)) && (!r2foreign || can_be_converted(rb2))) {
                return alloc(converting_join_fn, *this, rb1.get_signature(), rb2.get_signature(), col_cnt, cols1,
                    cols2);
            }
            return nullptr;
        }
        const finite_product_relation & r1 = get(rb1);
        const finite_product_relation & r2 = get(rb2);

        return alloc(join_fn, r1, r2, col_cnt, cols1, cols2);
    }


    class finite_product_relation_plugin::project_fn : public convenient_relation_project_fn {
        unsigned_vector m_removed_table_cols;
        unsigned_vector m_removed_rel_cols;

        scoped_ptr<relation_transformer_fn> m_rel_projector;
        scoped_ptr<relation_union_fn> m_inner_rel_union;

        //determines which columns of the result are table columns and which are in the inner relation
        svector<bool> m_res_table_columns;
    public:
        project_fn(const finite_product_relation & r, unsigned col_cnt, const unsigned * removed_cols) 
                : convenient_relation_project_fn(r.get_signature(), col_cnt, removed_cols) {
            SASSERT(col_cnt>0);
            for(unsigned i=0; i<col_cnt; i++) {
                unsigned col = removed_cols[i];
                if(r.is_table_column(col)) {
                    m_removed_table_cols.push_back(r.m_sig2table[col]);
                }
                else {
                    m_removed_rel_cols.push_back(r.m_sig2other[col]);
                }
            }

            unsigned sig_sz = r.get_signature().size();
            unsigned removed_idx = 0;
            for(unsigned i=0; i<sig_sz; i++) {
                if(removed_idx<col_cnt && removed_cols[removed_idx]==i) {
                    removed_idx++;
                    continue;
                }
                SASSERT(removed_idx==col_cnt || removed_cols[removed_idx]>i);
                m_res_table_columns.push_back(r.is_table_column(i));
            }
        }

        class project_reducer : public table_row_pair_reduce_fn {
            project_fn & m_parent;
            relation_vector & m_relations;
        public:

            project_reducer(project_fn & parent, relation_vector & relations) 
                : m_parent(parent), m_relations(relations) {}

            void operator()(table_element * func_columns, const table_element * merged_func_columns) override {
                relation_base * tgt = m_relations[static_cast<unsigned>(func_columns[0])]->clone();
                relation_base & src = *m_relations[static_cast<unsigned>(merged_func_columns[0])];
                if(!m_parent.m_inner_rel_union) {
                    m_parent.m_inner_rel_union = tgt->get_manager().mk_union_fn(*tgt, src);
                }
                (*m_parent.m_inner_rel_union)(*tgt, src);

                unsigned new_idx = m_relations.size();
                m_relations.push_back(tgt);
                func_columns[0] = new_idx;
            }
        };

        relation_base * operator()(const relation_base & rb) override {
            const finite_product_relation & r = get(rb);
            finite_product_relation_plugin & plugin = r.get_plugin();
            const table_base & rtable = r.get_table();
            relation_manager & rmgr = plugin.get_manager();

            r.garbage_collect(false);
            relation_vector res_relations;
            unsigned orig_rel_cnt = r.m_others.size();
            for(unsigned i=0; i<orig_rel_cnt; i++) {
                relation_base * orig_rel = r.m_others[i];
                res_relations.push_back(orig_rel ? orig_rel->clone() : nullptr);
            }
            SASSERT(res_relations.size()==orig_rel_cnt);

            bool shared_res_table = false;
            const table_base * res_table;

            if(m_removed_table_cols.empty()) {
                shared_res_table = true;
                res_table = &rtable;
            }
            else {
                project_reducer * preducer = alloc(project_reducer, *this, res_relations);
                scoped_ptr<table_transformer_fn> tproject = 
                    rmgr.mk_project_with_reduce_fn(rtable, m_removed_table_cols.size(), m_removed_table_cols.c_ptr(), preducer);
                res_table = (*tproject)(rtable);
            }

            relation_plugin * res_oplugin = nullptr;

            if(!m_removed_rel_cols.empty()) {
                unsigned res_rel_cnt = res_relations.size();
                for(unsigned i=0; i<res_rel_cnt; i++) {
                    if(res_relations[i]==0) {
                        continue;
                    }
                    relation_base * inner_rel = res_relations[i];
                    if(!m_rel_projector) {
                        m_rel_projector = rmgr.mk_project_fn(*inner_rel, m_removed_rel_cols);
                    }
                    res_relations[i] = (*m_rel_projector)(*inner_rel);
                    inner_rel->deallocate();
                    if(!res_oplugin) {
                        res_oplugin = &res_relations[i]->get_plugin();
                    }
                }
            }

            if(!res_oplugin) {
                res_oplugin = &r.m_other_plugin;
            }

            //TODO: Maybe we might want to specify a particular relation kind, instead of just null_family_id.
            //It would however need to be somehow inferred for the new signature.

            finite_product_relation * res = alloc(finite_product_relation, r.get_plugin(), get_result_signature(),
                m_res_table_columns.c_ptr(), res_table->get_plugin(), *res_oplugin, null_family_id);
            
            res->init(*res_table, res_relations, false);

            if(!shared_res_table) {
                const_cast<table_base *>(res_table)->deallocate();
            }

            return res;
        }
    };

    relation_transformer_fn * finite_product_relation_plugin::mk_project_fn(const relation_base & rb, unsigned col_cnt, 
            const unsigned * removed_cols) {
        if(&rb.get_plugin()!=this) {
            return nullptr;
        }
        return alloc(project_fn, get(rb), col_cnt, removed_cols);
    }



    class finite_product_relation_plugin::rename_fn : public convenient_relation_rename_fn {
        scoped_ptr<table_transformer_fn> m_table_renamer;
        scoped_ptr<relation_transformer_fn> m_rel_renamer;
        bool m_rel_identity;

        unsigned_vector m_rel_permutation;

        //determines which columns of the result are table columns and which are in the inner relation
        svector<bool> m_res_table_columns;
    public:
        rename_fn(const finite_product_relation & r, unsigned cycle_len, const unsigned * permutation_cycle) 
                : convenient_relation_rename_fn(r.get_signature(), cycle_len, permutation_cycle) {
            SASSERT(cycle_len>1);

            unsigned sig_sz = r.get_signature().size();
            unsigned_vector permutation;
            add_sequence(0, sig_sz, permutation);
            permutate_by_cycle(permutation, cycle_len, permutation_cycle);

            unsigned_vector table_permutation;

            bool table_identity = true;
            m_rel_identity = true;
            for(unsigned new_i=0; new_i<sig_sz; new_i++) {
                unsigned idx = permutation[new_i];
                bool is_orig_table = r.is_table_column(idx);
                m_res_table_columns.push_back(is_orig_table);
            }
            collect_sub_permutation(permutation, r.m_sig2table, table_permutation, table_identity);
            table_permutation.push_back(table_permutation.size()); //the functional column stays where it is
            collect_sub_permutation(permutation, r.m_sig2other, m_rel_permutation, m_rel_identity);

            if(!table_identity) {
                m_table_renamer = r.get_manager().mk_permutation_rename_fn(r.get_table(), table_permutation);
            }

        }

        relation_base * operator()(const relation_base & rb) override {
            const finite_product_relation & r = get(rb);
            const table_base & rtable = r.get_table();

            r.garbage_collect(false);
            relation_vector res_relations;
            unsigned orig_rel_cnt = r.m_others.size();
            for(unsigned i=0; i<orig_rel_cnt; i++) {
                relation_base * orig_rel = r.m_others[i];
                res_relations.push_back(orig_rel ? orig_rel->clone() : nullptr);
            }

            if(!m_rel_identity) {
                unsigned res_rel_cnt = res_relations.size();
                for(unsigned i=0; i<res_rel_cnt; i++) {
                    if(res_relations[i]==0) {
                        continue;
                    }
                    scoped_rel<relation_base> inner_rel = res_relations[i];
                    if(!m_rel_renamer) {
                        m_rel_renamer = r.get_manager().mk_permutation_rename_fn(*inner_rel, m_rel_permutation);
                    }

                    res_relations[i] = (*m_rel_renamer)(*inner_rel);
                }
            }
            scoped_rel<table_base> res_table_scoped;
            const table_base * res_table = &rtable;

            if(m_table_renamer) {
                res_table_scoped = (*m_table_renamer)(*res_table);
                res_table = res_table_scoped.get();
            }

            //TODO: Maybe we might want to specify a particular relation kind, instead of just null_family_id.
            //It would however need to be somehow inferred for the new signature.

            finite_product_relation * res = alloc(finite_product_relation, r.get_plugin(), get_result_signature(),
                m_res_table_columns.c_ptr(), res_table->get_plugin(), r.m_other_plugin, null_family_id);

            res->init(*res_table, res_relations, false);

            return res;
        }
    };

    relation_transformer_fn * finite_product_relation_plugin::mk_rename_fn(const relation_base & rb, 
        unsigned permutation_cycle_len, const unsigned * permutation_cycle) {

        if(&rb.get_plugin()!=this) {
            return nullptr;
        }
        const finite_product_relation & r = get(rb);
        return alloc(rename_fn, r, permutation_cycle_len, permutation_cycle);
    }


    class finite_product_relation_plugin::union_fn : public relation_union_fn {
        bool m_use_delta;
        unsigned_vector m_data_cols;//non-functional columns in the product-relation table (useful for creating operations)
        scoped_ptr<table_join_fn> m_common_join; //result of the join contains (data columns), tgt_rel_idx, src_rel_idx
        scoped_ptr<relation_union_fn> m_rel_union;
        scoped_ptr<table_union_fn> m_table_union;
        scoped_ptr<table_intersection_filter_fn> m_remove_overlaps;
        scoped_ptr<table_transformer_fn> m_remove_src_column_from_overlap;

        //this one is populated only if we're doing union with delta
        scoped_ptr<relation_union_fn> m_delta_merging_union;

        scoped_ptr<table_join_fn> m_overlap_delta_table_builder;
    public:
        union_fn(const finite_product_relation & tgt, bool use_delta) : m_use_delta(use_delta) {}

        relation_union_fn & get_inner_rel_union_op(relation_base & r) {
            if(!m_rel_union) {
                m_rel_union = r.get_manager().mk_union_fn(r, r, m_use_delta ? &r : nullptr);
            }
            return *m_rel_union;
        }

        class union_mapper : public table_row_mutator_fn {
            union_fn & m_parent;
            finite_product_relation & m_tgt;
            const finite_product_relation & m_src;
            table_base * m_delta_indexes; //table with signature (updated tgt rel index, delta_index in m_delta_rels)
            relation_vector * m_delta_rels;
            table_fact m_di_fact; //auxiliary fact for inserting into \c m_delta_indexes
        public:
            /**
               If \c delta_indexes is 0, it means we are not collecting indexes.
            */
            union_mapper(union_fn & parent, finite_product_relation & tgt, const finite_product_relation & src,
                    table_base * delta_indexes, relation_vector * delta_rels) 
                : m_parent(parent), 
                m_tgt(tgt), 
                m_src(src), 
                m_delta_indexes(delta_indexes), 
                m_delta_rels(delta_rels) {}

            ~union_mapper() override {}

            bool operator()(table_element * func_columns) override {
                relation_base & otgt_orig = m_tgt.get_inner_rel(func_columns[0]);
                const relation_base & osrc = m_src.get_inner_rel(func_columns[1]);

                relation_base * otgt = otgt_orig.clone();
                unsigned new_tgt_idx = m_tgt.get_next_rel_idx();
                m_tgt.set_inner_rel(new_tgt_idx, otgt);
                if(m_delta_indexes) {
                    relation_base * odelta = otgt->get_plugin().mk_empty(otgt->get_signature());
                    m_parent.get_inner_rel_union_op(*otgt)(*otgt, osrc, odelta);
                    
                    unsigned delta_idx = m_delta_rels->size();
                    m_delta_rels->push_back(odelta);
                    m_di_fact.reset();
                    m_di_fact.push_back(new_tgt_idx);
                    m_di_fact.push_back(delta_idx);
                    m_delta_indexes->add_fact(m_di_fact);
                }
                else {
                    m_parent.get_inner_rel_union_op(*otgt)(*otgt, osrc);
                }

                func_columns[0]=new_tgt_idx;
                return true;
            }
        };

        /**
           Makes a table whose last column has indexes to relations in \c src into a table
           with indexes to relation \c tgt.
        */
        class src_copying_mapper : public table_row_mutator_fn {
            finite_product_relation & m_tgt;
            const finite_product_relation & m_src;
        public:
            /**
               If \c delta_indexes is 0, it means we are not collecting indexes.
            */
            src_copying_mapper(finite_product_relation & tgt, const finite_product_relation & src) 
                : m_tgt(tgt), m_src(src) {}

            bool operator()(table_element * func_columns) override {
                const relation_base & osrc = m_src.get_inner_rel(func_columns[0]);
                unsigned new_tgt_idx = m_tgt.get_next_rel_idx();
                m_tgt.set_inner_rel(new_tgt_idx, osrc.clone());
                func_columns[0]=new_tgt_idx;
                return true;
            }
        };

        void operator()(relation_base & tgtb, const relation_base & srcb, relation_base * deltab) override {
            finite_product_relation & tgt = get(tgtb);
            const finite_product_relation & src0 = get(srcb);
            finite_product_relation * delta = get(deltab);

            relation_manager & rmgr = tgt.get_manager();

            scoped_rel<finite_product_relation> src_aux_copy; //copy of src in case its specification needs to be modified

            if(!vectors_equal(tgt.m_table2sig, src0.m_table2sig) 
                || (delta && !vectors_equal(tgt.m_table2sig, delta->m_table2sig)) ) {
                src_aux_copy = src0.clone();
                ptr_vector<finite_product_relation> orig_rels;
                orig_rels.push_back(src_aux_copy.get());
                orig_rels.push_back(&tgt);
                if(delta) {
                    orig_rels.push_back(delta);
                }
                if(!finite_product_relation::try_unify_specifications(orig_rels)) {
                    throw default_exception("finite_product_relation union: cannot convert relations to common specification");
                }
            }

            const finite_product_relation & src = src_aux_copy ? *src_aux_copy : src0;

            table_plugin & tplugin = tgt.get_table_plugin();

            if(!m_common_join) {
                unsigned data_cols_cnt = tgt.m_table_sig.size()-1;
                for(unsigned i=0; i<data_cols_cnt; i++) {
                    m_data_cols.push_back(i);
                }
                m_common_join = rmgr.mk_join_project_fn(tgt.get_table(), tgt.get_table(), m_data_cols, m_data_cols, 
                    m_data_cols);
            }


            scoped_rel<table_base> table_overlap = (*m_common_join)(tgt.get_table(), src.get_table());

            scoped_rel<table_base> delta_indexes;
            relation_vector delta_rels;
            if(m_use_delta) {
                table_signature di_sig;
                di_sig.push_back(finite_product_relation::s_rel_idx_sort);
                di_sig.push_back(finite_product_relation::s_rel_idx_sort);
                di_sig.set_functional_columns(1);
                delta_indexes = tplugin.mk_empty(di_sig);
            }

            {
                union_mapper * umapper = alloc(union_mapper, *this, tgt, src, delta_indexes.get(), &delta_rels);
                scoped_ptr<table_mutator_fn> mapping_fn = rmgr.mk_map_fn(*table_overlap, umapper);
                (*mapping_fn)(*table_overlap);
            }

            if(!m_remove_src_column_from_overlap) {
                unsigned removed_cols[] = { table_overlap->get_signature().size()-1 };
                m_remove_src_column_from_overlap = rmgr.mk_project_fn(*table_overlap, 1, removed_cols);
            }
            //transform table_overlap into the signature of tgt.get_table(), so that the functional
            //column contains indexes of the united relations
            scoped_rel<table_base> regular_overlap = (*m_remove_src_column_from_overlap)(*table_overlap);


            if(!m_remove_overlaps) {
                m_remove_overlaps = rmgr.mk_filter_by_negation_fn(tgt.get_table(), *regular_overlap, m_data_cols,
                    m_data_cols);
            }

            //in tgt keep only the rows that are in tgt only
            (*m_remove_overlaps)(tgt.get_table(), *regular_overlap);

            //add rows in which tgt and src overlapped
            if(!m_table_union) {
                m_table_union = rmgr.mk_union_fn(tgt.get_table(), tgt.get_table());
            }
            (*m_table_union)(tgt.get_table(), *regular_overlap);

            scoped_rel<table_base> src_only = src.get_table().clone();
            (*m_remove_overlaps)(*src_only, *regular_overlap);

            scoped_rel<table_base> src_only2; //a copy of src_only for use in building the delta
            if(m_use_delta) {
                src_only2 = src_only->clone();
            }

            {
                src_copying_mapper * cpmapper = alloc(src_copying_mapper, tgt, src);
                scoped_ptr<table_mutator_fn> mapping_fn = rmgr.mk_map_fn(*src_only, cpmapper);
                (*mapping_fn)(*src_only);
            }

            //add rows that were only in src
            (*m_table_union)(tgt.get_table(), *src_only);

            if(m_use_delta) {
                bool extending_delta = !delta->empty();
                //current delta, we will add it to the deltab argument later if it was not given to us empty
                finite_product_relation * cdelta;
                if(extending_delta) {
                    cdelta = delta->get_plugin().mk_empty(*delta);
                }
                else {
                    cdelta = delta;
                }

                if(!m_overlap_delta_table_builder) {
                    unsigned table_fn_col = regular_overlap->get_signature().size()-1;
                    unsigned first_col = 0;
                    unsigned removed_cols[] = { table_fn_col, table_fn_col+1 };
                    m_overlap_delta_table_builder = rmgr.mk_join_project_fn(*regular_overlap, *delta_indexes, 1,
                        &table_fn_col, &first_col, 2, removed_cols);
                }

                scoped_rel<table_base> overlap_delta_table = 
                    (*m_overlap_delta_table_builder)(*regular_overlap, *delta_indexes);

                cdelta->init(*overlap_delta_table, delta_rels, true);
                
                {
                    src_copying_mapper * cpmapper = alloc(src_copying_mapper, *cdelta, src);
                    scoped_ptr<table_mutator_fn> mapping_fn = rmgr.mk_map_fn(*src_only2, cpmapper);
                    (*mapping_fn)(*src_only2);
                }

                //add rows that were only in src
                (*m_table_union)(cdelta->get_table(), *src_only2);

                if(extending_delta) {
                    if(!m_delta_merging_union) {
                        m_delta_merging_union = rmgr.mk_union_fn(*delta, *cdelta);
                    }
                    (*m_delta_merging_union)(*delta, *cdelta);
                    cdelta->deallocate();
                }
            }
        }
    };

#if 0
    /**
       Union operation taking advantage of the fact that the inner relation of all the arguments
       is a singleton relation.
    */
    class finite_product_relation_plugin::inner_singleton_union_fn : public relation_union_fn {

        class offset_row_mapper : public table_row_mutator_fn {
        public:
            unsigned m_ofs;
            virtual bool operator()(table_element * func_columns) {
                func_columns[0] += m_ofs;
                return true;
            }
        };

        // [Leo]: gcc complained about the following class.
        // It does not have a constructor and uses a reference

        class inner_relation_copier : public table_row_mutator_fn {
            finite_product_relation & m_tgt;
            const finite_product_relation & m_src;
            finite_product_relation * m_delta;
            unsigned m_tgt_ofs;
            unsigned m_delta_ofs;
        public:
            virtual bool operator()(table_element * func_columns) {
                unsigned src_idx = static_cast<unsigned>(func_columns[0]);
                unsigned tgt_idx = src_idx + m_tgt_ofs;
                unsigned delta_idx = m_delta ? (src_idx + m_delta_ofs) : 0;
                SASSERT(!m_delta || m_tgt.m_others[tgt_idx]==m_delta->m_others[delta_idx]);
                SASSERT(m_tgt.m_others[tgt_idx]==0 || m_tgt.m_others[tgt_idx]==m_src.m_others[src_idx]);
                if(m_tgt.m_others[tgt_idx]==0) {
                    m_tgt.m_others[tgt_idx] = m_src.m_others[src_idx]->clone();
                    if(m_delta) {
                        m_delta->m_others[delta_idx] = m_src.m_others[src_idx]->clone();
                    }
                }
                return true;
            }
        };

        scoped_ptr<table_union_fn> m_t_union_fun;
        offset_row_mapper * m_offset_mapper_obj; //initialized together with m_offset_mapper_fun, and deallocated by it
        scoped_ptr<table_mutator_fn> m_offset_mapper_fun;



    public:
        virtual void operator()(relation_base & tgtb, const relation_base & srcb, relation_base * deltab) {
            finite_product_relation & tgt = get(tgtb);
            const finite_product_relation & src = get(srcb);
            finite_product_relation * delta = get(deltab);

            finite_product_relation_plugin & plugin = tgt.get_plugin();
            relation_manager & rmgr = plugin.get_manager();

            //we want only non-empty inner relations to remain
            tgt.garbage_collect(true);
            src.garbage_collect(true);

            table_base & tgt_table = tgt.get_table();
            const table_base & src_table = src.get_table();

            scoped_rel<table_base> offsetted_src = src_table.clone();

            if(!m_offset_mapper_fun) {
                m_offset_mapper_obj = alloc(offset_row_mapper);
                m_offset_mapper_fun = rmgr.mk_map_fn(*offsetted_src, m_offset_mapper_obj);
            }
            unsigned src_rel_offset = tgt.m_others.size();
            m_offset_mapper_obj->m_ofs = src_rel_offset;

            (*m_offset_mapper_fun)(*offsetted_src);
            
            //if we need to generate a delta, we get collect it into an empty relation and then union
            //it with the delta passed in as argument.
            scoped_rel<finite_product_relation> loc_delta = delta ? get(plugin.mk_empty(*delta)) : 0;
            //even if we don't need to generate the delta for the caller, we still want to have a delta 
            //table to know which relations to copy.
            scoped_rel<table_base> loc_delta_table_scoped;
            if(!loc_delta) {
                loc_delta_table_scoped = tgt_table.get_plugin().mk_empty(tgt_table);
            }
            table_base * loc_delta_table = loc_delta ? &loc_delta->get_table() : loc_delta_table_scoped.get();

            if(!m_t_union_fun) {
                m_t_union_fun = rmgr.mk_union_fn(tgt_table, *offsetted_src, loc_delta_table);
            }
            (*m_t_union_fun)(tgt_table, *offsetted_src, loc_delta_table);


            //TODO: copy the relations into tgt and (possibly) delta using inner_relation_copier
            //TODO: unite the local delta with the delta passed in as an argument
            NOT_IMPLEMENTED_YET();
        }
    };
#endif

    class finite_product_relation_plugin::converting_union_fn : public relation_union_fn {
        scoped_ptr<relation_union_fn> m_tr_union_fun;
    public:
        void operator()(relation_base & tgtb, const relation_base & srcb, relation_base * deltab) override {
            SASSERT(srcb.get_plugin().is_finite_product_relation());
            const finite_product_relation & src = get(srcb);
            finite_product_relation_plugin & plugin = src.get_plugin();
            scoped_rel<table_relation> tr_src = plugin.to_table_relation(src);
            if(!m_tr_union_fun) {
                m_tr_union_fun = plugin.get_manager().mk_union_fn(tgtb, *tr_src, deltab);
                SASSERT(m_tr_union_fun);
            }
            (*m_tr_union_fun)(tgtb, *tr_src, deltab);
        }
    };

    relation_union_fn * finite_product_relation_plugin::mk_union_fn(const relation_base & tgtb, const relation_base & srcb,
        const relation_base * deltab) {
        if(&srcb.get_plugin()!=this) {
            return nullptr;
        }
        const finite_product_relation & src = get(srcb);
        if(&tgtb.get_plugin()!=this || (deltab && &deltab->get_plugin()!=this) ) {
            if(can_convert_to_table_relation(src)) {
                return alloc(converting_union_fn);
            }
            return nullptr;
        }

        const finite_product_relation * delta = get(deltab);

        return alloc(union_fn, get(tgtb), delta!=nullptr);
    }


    class finite_product_relation_plugin::filter_identical_fn : public relation_mutator_fn {
        //the table and relation columns that should be identical
        //the column numbering is local to the table or inner relation
        unsigned_vector m_table_cols;
        unsigned_vector m_rel_cols;

        scoped_ptr<table_mutator_fn> m_table_filter;
        scoped_ptr<relation_mutator_fn> m_rel_filter;
        scoped_ptr<relation_mutator_fn> m_tr_filter;
    public:
        filter_identical_fn(const finite_product_relation & r, unsigned col_cnt, const unsigned * identical_cols) 
                : m_table_filter(nullptr), m_rel_filter(nullptr), m_tr_filter(nullptr) {
            finite_product_relation_plugin & plugin = r.get_plugin();
            for(unsigned i=0; i<col_cnt; i++) {
                unsigned col = identical_cols[i];
                if(r.is_table_column(col)) {
                    m_table_cols.push_back(r.m_sig2table[col]);
                }
                else {
                    m_rel_cols.push_back(r.m_sig2other[col]);
                }
            }
            if(m_table_cols.size()>1) {
                m_table_filter = r.get_manager().mk_filter_identical_fn(r.get_table(), m_table_cols.size(), 
                    m_table_cols.c_ptr());
                SASSERT(m_table_filter);
            }
            if(!m_table_cols.empty() && !m_rel_cols.empty()) {
                unsigned tr_filter_table_cols[] = { m_table_cols[0] };
                unsigned tr_filter_rel_cols[] = { m_rel_cols[0] };
                m_tr_filter = plugin.mk_filter_identical_pairs(r, 1, tr_filter_table_cols, tr_filter_rel_cols);
                SASSERT(m_tr_filter);
            }
        }

        void ensure_rel_filter(const relation_base & orel) {
            SASSERT(m_rel_cols.size()>1);
            if(m_rel_filter) {
                return;
            }
            m_rel_filter = orel.get_manager().mk_filter_identical_fn(orel, m_rel_cols.size(), m_rel_cols.c_ptr());
            SASSERT(m_rel_filter);
        }

        void operator()(relation_base & rb) override {
            finite_product_relation & r = get(rb);

            if(m_table_cols.size()>1) {
                (*m_table_filter)(r.get_table());
            }

            if(m_rel_cols.size()>1) {
                r.garbage_collect(true);
                unsigned rel_cnt = r.m_others.size();
                for(unsigned rel_idx=0; rel_idx<rel_cnt; rel_idx++) {
                    if(r.m_others[rel_idx]==0) {
                        continue;
                    }
                    ensure_rel_filter(*r.m_others[rel_idx]);
                    (*m_rel_filter)(*r.m_others[rel_idx]);
                }
            }

            if(!m_table_cols.empty() && !m_rel_cols.empty()) {
                (*m_tr_filter)(r);
            }
        }
    };

    relation_mutator_fn * finite_product_relation_plugin::mk_filter_identical_fn(const relation_base & rb, 
            unsigned col_cnt, const unsigned * identical_cols) {
        if(&rb.get_plugin()!=this) {
            return nullptr;
        }
        return alloc(filter_identical_fn, get(rb), col_cnt, identical_cols);
    }

    class finite_product_relation_plugin::filter_equal_fn : public relation_mutator_fn {
        scoped_ptr<table_mutator_fn> m_table_filter;
        scoped_ptr<relation_mutator_fn> m_rel_filter;
        unsigned m_col;
        app_ref m_value;
    public:
        filter_equal_fn(const finite_product_relation & r, const relation_element & value, unsigned col)
                : m_col(col), m_value(value, r.get_context().get_manager()) {
            if(r.is_table_column(col)) {
                table_element tval;
                r.get_manager().relation_to_table(r.get_signature()[col], value, tval);
                m_table_filter = r.get_manager().mk_filter_equal_fn(r.get_table(), tval, r.m_sig2table[col]);
            }
        }

        void operator()(relation_base & rb) override {
            finite_product_relation & r = get(rb);

            if(m_table_filter) {
                (*m_table_filter)(r.get_table());
                return;
            }
            r.garbage_collect(false);
            relation_vector & inner_rels = r.m_others;
            unsigned rel_cnt = inner_rels.size();
            for(unsigned i=0; i<rel_cnt; i++) {
                if(inner_rels[i]==0) {
                    continue;
                }
                if(!m_rel_filter) {
                    m_rel_filter = r.get_manager().mk_filter_equal_fn(*inner_rels[i], m_value, r.m_sig2other[m_col]);
                }
                (*m_rel_filter)(*inner_rels[i]);
            }
        }
    };


    relation_mutator_fn * finite_product_relation_plugin::mk_filter_equal_fn(const relation_base & rb, 
            const relation_element & value, unsigned col) {
        if(&rb.get_plugin()!=this) {
            return nullptr;
        }
        return alloc(filter_equal_fn, get(rb), value, col);
    }


    class finite_product_relation_plugin::filter_interpreted_fn : public relation_mutator_fn {
        ast_manager & m_manager;
        var_subst & m_subst;

        scoped_ptr<table_mutator_fn> m_table_filter;
        scoped_ptr<relation_mutator_fn> m_rel_filter;
        app_ref m_cond;

        idx_set m_table_cond_columns;
        idx_set m_rel_cond_columns;

        //like m_table_cond_columns and m_rel_cond_columns, only the indexes are local to the 
        //table/relation, not to the signature of the whole relation
        idx_set m_table_local_cond_columns;
        idx_set m_rel_local_cond_columns;

        /**
           If equal to 0, it means the interpreted condition uses all table columns. Then the original
           table is used instead of the result of the projection.
        */
        scoped_ptr<table_transformer_fn> m_table_cond_columns_project;
        /**
           \brief Column indexes of the global relations to which correspond the data columns in the table
           that is result of applying the \c m_table_cond_columns_project functor.
        */
        unsigned_vector m_global_origins_of_projected_columns;

        scoped_ptr<table_join_fn> m_assembling_join_project;


        /**
           \brief Renaming that transforms the variable numbers pointing to the global relation into
           variables that point to the inner relation variables.

           The elements that do not correspond to columns of the inner relation (but rather to the table 
           columns) is modified in \c operator() when evaluating the condition for all the relevant 
           combinations of table values.
        */
        expr_ref_vector m_renaming_for_inner_rel;
    public:
        filter_interpreted_fn(const finite_product_relation & r, app * condition)
                : m_manager(r.get_context().get_manager()), 
                m_subst(r.get_context().get_var_subst()),
                m_cond(condition, m_manager),
                m_renaming_for_inner_rel(m_manager) {
            relation_manager & rmgr = r.get_manager();

            rule_manager& rm = r.get_context().get_rule_manager();
            idx_set& cond_columns = rm.collect_vars(m_cond);

            unsigned sig_sz = r.get_signature().size();
            for(unsigned i=0; i<sig_sz; i++) {
                if(r.is_table_column(i)) {
                    m_table_cond_columns.insert(i);
                }
                else {
                    m_rel_cond_columns.insert(i);
                }
            }
            set_intersection(m_table_cond_columns, cond_columns);
            set_intersection(m_rel_cond_columns, cond_columns);
            transform_set(r.m_sig2table, m_table_cond_columns, m_table_local_cond_columns);
            transform_set(r.m_sig2other, m_rel_cond_columns, m_rel_local_cond_columns);

            if(m_rel_cond_columns.empty()) {
                expr_ref_vector renaming(m_manager);
                get_renaming_args(r.m_sig2table, r.get_signature(), renaming);
                expr_ref table_cond = m_subst(condition, renaming.size(), renaming.c_ptr());
                m_table_filter = rmgr.mk_filter_interpreted_fn(r.get_table(), to_app(table_cond));
            }
            else {
                get_renaming_args(r.m_sig2other, r.get_signature(), m_renaming_for_inner_rel);

                if(!m_table_cond_columns.empty()) {
                    //We will keep the table variables that appear in the condition together 
                    //with the index column and then iterate through the tuples, evaluating
                    //the rest of the condition on the inner relations.
                    unsigned_vector removed_cols;
                    unsigned table_data_col_cnt = r.m_table_sig.size()-1;
                    for(unsigned i=0; i<table_data_col_cnt; i++) {
                        if(m_table_local_cond_columns.contains(i)) {
                            m_global_origins_of_projected_columns.push_back(r.m_table2sig[i]);
                        }
                        else {
                            removed_cols.push_back(i);
                        }
                    }
                    if(!removed_cols.empty()) {
                        m_table_cond_columns_project = rmgr.mk_project_fn(r.get_table(), removed_cols);
                    }
                }
            }
        }

        void operator()(relation_base & rb) override {
            finite_product_relation & r = get(rb);
            table_base & rtable = r.get_table();
            table_plugin & tplugin = r.get_table_plugin();
            const relation_signature & osig = r.get_signature();
            relation_manager & rmgr = r.get_manager();
            unsigned rsig_sz = r.get_signature().size();
            
            if(m_rel_cond_columns.empty()) {
                SASSERT(m_table_filter);
                (*m_table_filter)(rtable);
                return;
            }
            if(m_table_cond_columns.empty()) {
                r.garbage_collect(false);
                unsigned rel_cnt = r.m_others.size();
                for(unsigned i=0; i<rel_cnt; i++) {
                    relation_base * inner = r.m_others[i];
                    if(inner==nullptr) {
                        continue;
                    }
                    if(!m_rel_filter) {
                        expr_ref inner_cond = m_subst(m_cond, m_renaming_for_inner_rel.size(), m_renaming_for_inner_rel.c_ptr());
                        m_rel_filter = rmgr.mk_filter_interpreted_fn(*inner, to_app(inner_cond));
                    }
                    (*m_rel_filter)(*inner);
                }
                return;
            }

            //get table without the data columns on which we don't enforce identities
            //The relation index column may be non-functional.
            scoped_rel<table_base> tproj_scope;
            const table_base * tproj;
            if(m_table_cond_columns_project) {
                tproj_scope = (*m_table_cond_columns_project)(rtable);
                tproj = tproj_scope.get();
            }
            else {
                tproj = &rtable;
            }
            unsigned projected_data_cols = tproj->get_signature().size()-1;
            SASSERT(m_table_cond_columns.num_elems()==projected_data_cols);
            
            table_signature filtered_sig = tproj->get_signature();
            filtered_sig.push_back(finite_product_relation::s_rel_idx_sort);
            filtered_sig.set_functional_columns(1);

            relation_vector new_rels;

            scoped_rel<table_base> filtered_table = tplugin.mk_empty(filtered_sig);
            table_fact f;
            unsigned renaming_ofs = m_renaming_for_inner_rel.size()-1;
            table_base::iterator pit = tproj->begin();
            table_base::iterator pend = tproj->end();
            for(; pit!=pend; ++pit) {
                pit->get_fact(f);
                unsigned old_rel_idx = static_cast<unsigned>(f.back());
                const relation_base & old_rel = r.get_inner_rel(old_rel_idx);

                //put the table values into the substitution
                for(unsigned i=0; i<projected_data_cols; i++) {
                    unsigned orig_col_idx = m_global_origins_of_projected_columns[i];
                    relation_element r_el;
                    rmgr.table_to_relation(osig[orig_col_idx], f[i], r_el);
                    m_renaming_for_inner_rel.set(renaming_ofs-orig_col_idx, r_el);
                }

                //create the condition with table values substituted in and relation values properly renamed
                expr_ref inner_cond(m_manager);
                inner_cond = m_subst(m_cond, m_renaming_for_inner_rel.size(), m_renaming_for_inner_rel.c_ptr());
                th_rewriter rw(m_manager);
                rw(inner_cond);
                if (m_manager.is_false(inner_cond)) {
                    continue;
                }

                relation_base * new_rel = old_rel.clone();
                
                scoped_ptr<relation_mutator_fn> filter = rmgr.mk_filter_interpreted_fn(*new_rel, to_app(inner_cond));
                (*filter)(*new_rel);
 
                if(new_rel->empty()) {
                    new_rel->deallocate();
                    continue;
                }

                unsigned new_rel_idx = new_rels.size();
                new_rels.push_back(new_rel);
                f.push_back(new_rel_idx);
                filtered_table->add_fact(f);
            }

            if(!m_assembling_join_project) {
                unsigned_vector table_cond_columns_vect;
                for(unsigned i=0; i<rsig_sz; i++) {
                    if(m_table_local_cond_columns.contains(i)) {
                        table_cond_columns_vect.push_back(i);
                    }
                }

                m_assembling_join_project = mk_assembler_of_filter_result(rtable, *filtered_table, 
                    table_cond_columns_vect);
            }

            scoped_rel<table_base> new_table = (*m_assembling_join_project)(rtable, *filtered_table);
            r.reset();
            r.init(*new_table, new_rels, true);
        }
    };

    relation_mutator_fn * finite_product_relation_plugin::mk_filter_interpreted_fn(const relation_base & rb, 
            app * condition) {
        if(&rb.get_plugin()!=this) {
            return nullptr;
        }
        return alloc(filter_interpreted_fn, get(rb), condition);
    }

    class finite_product_relation_plugin::negation_filter_fn : public relation_intersection_filter_fn {

        unsigned_vector m_r_cols;
        unsigned_vector m_neg_cols;

        scoped_ptr<table_intersection_filter_fn> m_table_neg_filter;
        scoped_ptr<table_join_fn> m_table_neg_complement_selector;
        scoped_ptr<relation_join_fn> m_neg_intersection_join;
        scoped_ptr<table_join_fn> m_table_intersection_join;
        scoped_ptr<table_union_fn> m_table_overlap_union;
        scoped_ptr<table_intersection_filter_fn> m_table_subtract;
        scoped_ptr<relation_intersection_filter_fn> m_inner_subtract;
        scoped_ptr<table_transformer_fn> m_overlap_table_last_column_remover;
        scoped_ptr<table_union_fn> m_r_table_union;

        bool m_table_overlaps_only;

        unsigned_vector m_r_shared_table_cols;
        unsigned_vector m_neg_shared_table_cols;

        unsigned_vector m_r_shared_rel_cols;
        unsigned_vector m_neg_shared_rel_cols;
    public:
        negation_filter_fn(const finite_product_relation & r, const finite_product_relation & neg, 
                    unsigned joined_col_cnt, const unsigned * r_cols, const unsigned * neg_cols)
                : m_r_cols(joined_col_cnt, r_cols),
                m_neg_cols(joined_col_cnt, neg_cols),
                m_table_overlaps_only(true) {
            const table_signature & tsig = r.m_table_sig;
            const table_base & rtable = r.get_table();
            relation_manager & rmgr = r.get_manager();

            for(unsigned i=0; i<joined_col_cnt; i++) {
                if(r.is_table_column(r_cols[i]) && neg.is_table_column(neg_cols[i])) {
                    m_r_shared_table_cols.push_back(r.m_sig2table[r_cols[i]]);
                    m_neg_shared_table_cols.push_back(neg.m_sig2table[neg_cols[i]]);
                }
                else {
                    m_table_overlaps_only = false;
                }
            }
            if(m_table_overlaps_only) {
                m_table_neg_filter = rmgr.mk_filter_by_negation_fn(rtable, neg.get_table(), 
                    m_r_shared_table_cols, m_neg_shared_table_cols);
                SASSERT(m_table_neg_filter);
            }
            else {
                unsigned_vector removed_cols;
                add_sequence(r.get_signature().size(), neg.get_signature().size(), removed_cols);
                m_neg_intersection_join = rmgr.mk_join_project_fn(r, neg, m_r_cols, m_neg_cols, removed_cols, false);
                SASSERT(m_neg_intersection_join);

                unsigned_vector data_cols;
                add_sequence(0, tsig.size()-1, data_cols);
                removed_cols.reset();
                //remove the second copy of table data columns
                add_sequence(tsig.size()-1, tsig.size()-1, removed_cols);
                m_table_intersection_join = rmgr.mk_join_project_fn(rtable, rtable, data_cols, data_cols, 
                    removed_cols);
                SASSERT(m_table_intersection_join);

                m_table_subtract = rmgr.mk_filter_by_negation_fn(rtable, rtable, data_cols, data_cols);
                SASSERT(m_table_subtract);
            }
        }

        void handle_only_tables_overlap_case(finite_product_relation & r, const finite_product_relation & neg) {
            SASSERT(m_table_overlaps_only);
            (*m_table_neg_filter)(r.get_table(), neg.get_table());
        }


        class rel_subtractor : public table_row_mutator_fn {
            negation_filter_fn & m_parent;
            finite_product_relation & m_r;
            const finite_product_relation & m_inters; //intersection of the relation and the negated one
        public:
            rel_subtractor(negation_filter_fn & parent, finite_product_relation & r, 
                        const finite_product_relation & inters)
                : m_parent(parent), m_r(r), m_inters(inters) {}

            bool operator()(table_element * func_columns) override {
                relation_base * r_inner = m_r.get_inner_rel(func_columns[0]).clone();
                const relation_base & inters_inner = m_inters.get_inner_rel(func_columns[1]);

                if(!m_parent.m_inner_subtract) {
                    unsigned_vector all_rel_cols;
                    add_sequence(0, r_inner->get_signature().size() , all_rel_cols);
                    m_parent.m_inner_subtract = m_r.get_manager().mk_filter_by_negation_fn(*r_inner, 
                        inters_inner, all_rel_cols, all_rel_cols);
                }
                (*m_parent.m_inner_subtract)(*r_inner, inters_inner);

                unsigned new_rel_num = m_r.get_next_rel_idx();
                m_r.set_inner_rel(new_rel_num, r_inner);
                func_columns[0]=new_rel_num;
                return true;
            }
        };


        void operator()(relation_base & rb, const relation_base & negb) override {
            finite_product_relation & r = get(rb);
            const finite_product_relation & neg = get(negb);

            if(m_table_overlaps_only) {
                handle_only_tables_overlap_case(r, neg);
                return;
            }

            scoped_rel<finite_product_relation> intersection = get((*m_neg_intersection_join)(r, neg));

            DEBUG_CODE(
                finite_product_relation_plugin & plugin = r.get_plugin();
                SASSERT(&intersection->get_plugin()==&plugin); //the result of join is also finite product
                SASSERT(r.get_signature()==intersection->get_signature()););
            table_base & r_table = r.get_table();
            table_plugin & tplugin = r_table.get_plugin();
            relation_manager & rmgr = r.get_manager();

            //we need to do this before we perform the \c m_table_subtract
            //the sigrature of the \c table_overlap0 relation is 
            //(data_columns)(original rel idx)(subtracted rel idx)
            scoped_rel<table_base> table_overlap0 = (*m_table_intersection_join)(r_table, 
                intersection->get_table());
            
            //the rows that don't appear in the table of the intersection are safe to stay
            (*m_table_subtract)(r_table,  intersection->get_table());
            
            //now we will examine the rows that do appear in the intersection

            //There are no functional columns in the \c table_overlap0 relation (because of 
            //the project we did). We need to make both rel idx columns functional.
            //We do not lose any rows, since the data columns by themselves are unique.

            table_signature table_overlap_sig(table_overlap0->get_signature());
            table_overlap_sig.set_functional_columns(2);
            scoped_rel<table_base> table_overlap = tplugin.mk_empty(table_overlap_sig);

            if(!m_table_overlap_union) {
                m_table_overlap_union = rmgr.mk_union_fn(*table_overlap, *table_overlap0);
                SASSERT(m_table_overlap_union);
            }
            (*m_table_overlap_union)(*table_overlap, *table_overlap0);

            {
                rel_subtractor * mutator = alloc(rel_subtractor, *this, r, *intersection);
                scoped_ptr<table_mutator_fn> mapper = rmgr.mk_map_fn(*table_overlap, mutator);
                (*mapper)(*table_overlap);
            }

            if(!m_overlap_table_last_column_remover) {
                unsigned removed_col = table_overlap->get_signature().size()-1;
                m_overlap_table_last_column_remover = rmgr.mk_project_fn(*table_overlap, 1, &removed_col);
            }
            scoped_rel<table_base> final_overlapping_rows_table = 
                (*m_overlap_table_last_column_remover)(*table_overlap);

            if(!m_r_table_union) {
                m_r_table_union = rmgr.mk_union_fn(r_table, *final_overlapping_rows_table);
            }

            (*m_r_table_union)(r_table, *final_overlapping_rows_table);
        }
    };

    relation_intersection_filter_fn * finite_product_relation_plugin::mk_filter_by_negation_fn(const relation_base & rb, 
            const relation_base & negb, unsigned joined_col_cnt, 
            const unsigned * r_cols, const unsigned * negated_cols) {
        if(&rb.get_plugin()!=this || &negb.get_plugin()!=this) {
            return nullptr;
        }
        
        return alloc(negation_filter_fn, get(rb), get(negb), joined_col_cnt, r_cols, negated_cols);
    }


    class finite_product_relation_plugin::filter_identical_pairs_fn : public relation_mutator_fn {
        scoped_ptr<table_transformer_fn> m_tproject_fn; //if zero, no columns need to be projected away
        unsigned m_col_cnt;
        unsigned_vector m_table_cols;
        unsigned_vector m_rel_cols;

        scoped_ptr<table_join_fn> m_assembling_join_project;
        scoped_ptr<table_union_fn> m_updating_union;
    public:
        filter_identical_pairs_fn(const finite_product_relation & r, unsigned col_cnt, const unsigned * table_cols, 
                    const unsigned * rel_cols) :
                m_col_cnt(col_cnt),
                m_table_cols(col_cnt, table_cols),
                m_rel_cols(col_cnt, rel_cols) {
            SASSERT(col_cnt>0);
            const table_signature & tsig = r.m_table_sig;
            unsigned t_sz = tsig.size();

            sort_two_arrays(col_cnt, m_table_cols.begin(), m_rel_cols.begin());
            SASSERT(m_table_cols.back()<t_sz-1); //check the table columns aren't outside the table data columns
            SASSERT(*std::max_element(m_rel_cols.begin(), m_rel_cols.end())<r.m_other_sig.size()); //the same for relation

            unsigned_vector removed_cols;
            add_sequence_without_set(0, t_sz-1, m_table_cols, removed_cols);
            if(!removed_cols.empty()) {
                m_tproject_fn = r.get_manager().mk_project_fn(r.get_table(), removed_cols.size(), removed_cols.c_ptr());
            }
        }

        void operator()(relation_base & rb) override {
            finite_product_relation & r = get(rb);
            finite_product_relation_plugin & plugin = r.get_plugin();
            table_plugin & tplugin = r.get_table_plugin();
            relation_signature & osig = r.m_other_sig;
            relation_manager & rmgr = tplugin.get_manager();
            table_base & rtable = r.get_table();
            ast_manager & m = plugin.get_ast_manager();

            //get table without the data columns on which we don't enforce identities
            //The relation index column may or may not be non-functional (according to whether we do the projection)
            scoped_rel<table_base> tproj;
            if(m_tproject_fn) {
                tproj = (*m_tproject_fn)(r.get_table());
            }
            else {
                tproj = r.get_table().clone();
            }
            SASSERT(m_col_cnt+1==tproj->get_signature().size());
            
            table_signature filtered_sig = tproj->get_signature();
            filtered_sig.push_back(finite_product_relation::s_rel_idx_sort);
            filtered_sig.set_functional_columns(1);

            relation_vector new_rels;
            scoped_rel<table_base> filtered_table = tplugin.mk_empty(filtered_sig);
            table_fact f;
            table_base::iterator pit = tproj->begin();
            table_base::iterator pend = tproj->end();
            for(; pit!=pend; ++pit) {
                pit->get_fact(f);
                unsigned old_rel_idx = static_cast<unsigned>(f.back());
                const relation_base & old_rel = r.get_inner_rel(old_rel_idx);
                relation_base * new_rel = old_rel.clone();
                for(unsigned i=0; i<m_col_cnt; i++) {
                    relation_element_ref r_el(m);
                    rmgr.table_to_relation(osig[m_rel_cols[i]], f[i], r_el);
                    scoped_ptr<relation_mutator_fn> filter = rmgr.mk_filter_equal_fn(*new_rel, r_el, m_rel_cols[i]);
                    (*filter)(*new_rel);
                }

                if(new_rel->empty()) {
                    new_rel->deallocate();
                    continue;
                }

                unsigned new_rel_idx = new_rels.size();
                new_rels.push_back(new_rel);
                f.push_back(new_rel_idx);
                filtered_table->add_fact(f);
            }

            if(!m_assembling_join_project) {
                m_assembling_join_project = mk_assembler_of_filter_result(rtable, *filtered_table, m_table_cols);
            }

            scoped_rel<table_base> new_table = (*m_assembling_join_project)(r.get_table(), *filtered_table);

            r.reset();
            r.init(*new_table, new_rels, true);
        }
    };

    relation_mutator_fn * finite_product_relation_plugin::mk_filter_identical_pairs(const finite_product_relation & r, 
            unsigned col_cnt, const unsigned * table_cols, const unsigned * rel_cols) {
        return alloc(filter_identical_pairs_fn, r, col_cnt, table_cols, rel_cols);
    }

    table_join_fn * finite_product_relation_plugin::mk_assembler_of_filter_result(const table_base & relation_table, 
            const table_base & filtered_table, const unsigned_vector & selected_columns) {

        table_plugin & tplugin = relation_table.get_plugin();
        const table_signature & rtable_sig = relation_table.get_signature();
        unsigned rtable_sig_sz = rtable_sig.size();
        unsigned selected_col_cnt = selected_columns.size();
        SASSERT(selected_col_cnt+2==filtered_table.get_signature().size());
        SASSERT(rtable_sig.functional_columns()==1);
        SASSERT(filtered_table.get_signature().functional_columns()==1);

        unsigned_vector rtable_joined_cols;
        rtable_joined_cols.append(selected_col_cnt, selected_columns.c_ptr()); //filtered table cols
        rtable_joined_cols.push_back(rtable_sig_sz-1); //unfiltered relation indexes

        unsigned_vector filtered_joined_cols;
        add_sequence(0, selected_col_cnt, filtered_joined_cols); //filtered table cols
        filtered_joined_cols.push_back(selected_col_cnt); //unfiltered relation indexes
        SASSERT(rtable_joined_cols.size()==filtered_joined_cols.size());

        //the signature after join:
        //(all relation table columns)(all filtered relation table columns)(unfiltered rel idx non-func from 'filtered')
        //   (unfiltered rel idx func from 'rtable')(filtered rel idx)
        unsigned_vector removed_cols;
        unsigned filtered_nonfunc_ofs = rtable_sig_sz-1;
        add_sequence(filtered_nonfunc_ofs, selected_col_cnt, removed_cols); //data columns from 'filtered'
        unsigned idx_ofs = filtered_nonfunc_ofs+selected_col_cnt;
        removed_cols.push_back(idx_ofs); //unfiltered relation indexes from 'filtered'
        removed_cols.push_back(idx_ofs+1); //unfiltered relation indexes from rtable

        table_join_fn * res = tplugin.get_manager().mk_join_project_fn(relation_table, filtered_table, 
            rtable_joined_cols, filtered_joined_cols, removed_cols);
        SASSERT(res);
        return res;
    }

    // -----------------------------------
    //
    // finite_product_relation
    //
    // -----------------------------------

    finite_product_relation::finite_product_relation(finite_product_relation_plugin & p, 
                const relation_signature & s, const bool * table_columns, table_plugin & tplugin,
                relation_plugin & oplugin, family_id other_kind)
            : relation_base(p, s), 
            m_other_plugin(oplugin),
            m_other_kind(other_kind),
            m_full_rel_idx(UINT_MAX) {
        const relation_signature & rel_sig = get_signature();
        unsigned sz = rel_sig.size();
        m_sig2table.resize(sz, UINT_MAX);
        m_sig2other.resize(sz, UINT_MAX);
        for(unsigned i=0; i<sz; i++) {
            if(table_columns[i]) {
                m_sig2table[i]=m_table_sig.size();
                table_sort srt;
                //the table columns must have table-friendly sorts
                VERIFY( get_manager().relation_sort_to_table(rel_sig[i], srt) );
                m_table_sig.push_back(srt);
                m_table2sig.push_back(i);
            }
            else {
                m_sig2other[i]=m_other_sig.size();
                m_other_sig.push_back(rel_sig[i]);
                m_other2sig.push_back(i);
            }
        }
        SASSERT(m_table_sig.size()+m_other_sig.size()==sz);

        m_table_sig.push_back(s_rel_idx_sort);
        m_table_sig.set_functional_columns(1);

        m_table = tplugin.mk_empty(m_table_sig);

        set_kind(p.get_relation_kind(*this, table_columns));
    }

    finite_product_relation::finite_product_relation(const finite_product_relation & r)
            : relation_base(r), 
            m_table_sig(r.m_table_sig),
            m_table2sig(r.m_table2sig),
            m_sig2table(r.m_sig2table),
            m_other_sig(r.m_other_sig),
            m_other2sig(r.m_other2sig),
            m_sig2other(r.m_sig2other),
            m_other_plugin(r.m_other_plugin),
            m_other_kind(r.m_other_kind),
            m_table(r.m_table->clone()),
            m_others(r.m_others),
            m_available_rel_indexes(r.m_available_rel_indexes),
            m_full_rel_idx(r.m_full_rel_idx),
            m_live_rel_collection_project(),
            m_empty_rel_removal_filter() {
        //m_others is now just a shallow copy, we need use clone of the relations that in it now
        unsigned other_sz = m_others.size();
        for(unsigned i=0; i<other_sz; i++) {
            if(m_others[i]==0) {
                //unreferenced relation index
                continue;
            }
            m_others[i] = get_inner_rel(i).clone();
        }
    }

    void finite_product_relation::swap(relation_base & r0) {
        SASSERT(can_swap(r0));
        finite_product_relation & r = finite_product_relation_plugin::get(r0);
        SASSERT(get_signature()==r.get_signature());
        SASSERT(&get_plugin()==&r.get_plugin());
        SASSERT(&m_other_plugin==&r.m_other_plugin);

        m_table_sig.swap(r.m_table_sig);
        m_table2sig.swap(r.m_table2sig);
        m_sig2table.swap(r.m_sig2table);
        m_other_sig.swap(r.m_other_sig);
        m_other2sig.swap(r.m_other2sig);
        m_sig2other.swap(r.m_sig2other);
        std::swap(m_table, r.m_table);
        m_others.swap(r.m_others);
        m_available_rel_indexes.swap(r.m_available_rel_indexes);
        std::swap(m_full_rel_idx,r.m_full_rel_idx);
        m_live_rel_collection_project=nullptr;
        m_empty_rel_removal_filter=nullptr;

        relation_base::swap(r0);
    }

    finite_product_relation::~finite_product_relation() { 
        m_table->deallocate();
        relation_vector::iterator it = m_others.begin();
        relation_vector::iterator end = m_others.end();
        for(; it!=end; ++it) {
            relation_base * rel= *it;
            if(rel) {
                rel->deallocate();
            }
        }
    }

    context & finite_product_relation::get_context() const {
        return get_manager().get_context();
    }

    unsigned finite_product_relation::get_next_rel_idx() const {
        unsigned res;
        if(!m_available_rel_indexes.empty()) {
            res = m_available_rel_indexes.back();
            m_available_rel_indexes.pop_back();
        }
        else {
            res = m_others.size();
            m_others.push_back(0);
        }
        SASSERT(m_others[res]==0);
        return res;
    }

    void finite_product_relation::recycle_rel_idx(unsigned idx) const {
        SASSERT(m_others[idx]==0);
        m_available_rel_indexes.push_back(idx);
    }

    unsigned finite_product_relation::get_full_rel_idx() {
        if(m_full_rel_idx==UINT_MAX) {
            m_full_rel_idx = get_next_rel_idx();
            relation_base * full_other = mk_full_inner(nullptr);
            m_others[m_full_rel_idx] = full_other;
        }
        return m_full_rel_idx;
    }

    void finite_product_relation::init(const table_base & table_vals, const relation_vector & others, bool contiguous) {
        SASSERT(m_table_sig.equal_up_to_fn_mark(table_vals.get_signature()));
        SASSERT(empty());
        if(!m_others.empty()) {
            garbage_collect(false);
        }
        SASSERT(m_others.empty());

        m_others = others;
        scoped_ptr<table_union_fn> table_union = get_manager().mk_union_fn(get_table(), table_vals);
        (*table_union)(get_table(), table_vals);

        if(!contiguous) {
            unsigned rel_cnt = m_others.size();
            for(unsigned i=0; i<rel_cnt; i++) {
                if(m_others[i]==0) {
                    m_available_rel_indexes.push_back(i);
                }
            }
        }
    }

    void finite_product_relation::extract_table_fact(const relation_fact & rf, table_fact & tf) const {
        const relation_signature & sig = get_signature();
        relation_manager & rmgr = get_manager();

        tf.reset();
        //this is m_table_sig.size()-1 since the last column in table signature if index of the other relation
        unsigned t_rel_sz = m_table2sig.size();
        for(unsigned i=0; i<t_rel_sz; i++) {
            table_element el;
            unsigned sig_idx = m_table2sig[i];
            rmgr.relation_to_table(sig[sig_idx], rf[sig_idx], el);
            tf.push_back(el);
        }
        tf.push_back(0);
    }

    void finite_product_relation::extract_other_fact(const relation_fact & rf, relation_fact & of) const {
        of.reset();
        unsigned o_sz = m_other_sig.size();
        for(unsigned i=0; i<o_sz; i++) {
            unsigned sig_idx = m_other2sig[i];
            of.push_back(rf[sig_idx]);
        }
    }

    relation_base * finite_product_relation::mk_empty_inner() {
        if(m_other_kind==null_family_id) {
            return m_other_plugin.mk_empty(m_other_sig);
        }
        else {
            return m_other_plugin.mk_empty(m_other_sig, m_other_kind);
        }
    }
    relation_base * finite_product_relation::mk_full_inner(func_decl* pred) {
        return m_other_plugin.mk_full(pred, m_other_sig, m_other_kind);
    }


    void finite_product_relation::add_fact(const relation_fact & f) {
        SASSERT(f.size()==get_signature().size());

        table_fact t_f;
        extract_table_fact(f, t_f);

        relation_fact o_f(get_manager().get_context());
        extract_other_fact(f, o_f);

        unsigned new_rel_idx = get_next_rel_idx();
        t_f.back()=new_rel_idx;

        relation_base * new_rel;
        if(m_table->suggest_fact(t_f)) {
            SASSERT(t_f.back()==new_rel_idx);
            new_rel = mk_empty_inner();
        } else {
            new_rel = get_inner_rel(t_f.back()).clone();

            t_f[t_f.size()-1]=new_rel_idx;
            m_table->ensure_fact(t_f);
        }
        new_rel->add_fact(o_f);
        set_inner_rel(new_rel_idx, new_rel);
    }

    bool finite_product_relation::contains_fact(const relation_fact & f) const {
        table_fact t_f;
        extract_table_fact(f, t_f);

        if(!m_table->fetch_fact(t_f)) {
            return false;
        }

        relation_fact o_f(get_context());
        extract_other_fact(f, o_f);

        const relation_base & other = get_inner_rel(t_f.back());

        return other.contains_fact(o_f);
    }

    bool finite_product_relation::empty() const {
        garbage_collect(true);
        return m_table->empty();
    }

    finite_product_relation * finite_product_relation::clone() const {
        return alloc(finite_product_relation, *this);
    }

    void finite_product_relation::complement_self(func_decl* p) {
        unsigned other_sz = m_others.size();
        for(unsigned i=0; i<other_sz; i++) {
            if(m_others[i]==0) {
                //unreferenced relation index
                continue;
            }
            relation_base * r = m_others[i]->complement(p);
            std::swap(m_others[i],r);
            r->deallocate();
        }
        table_element full_rel_idx = get_full_rel_idx();
        scoped_rel<table_base> complement_table = m_table->complement(p, &full_rel_idx);
        
        scoped_ptr<table_union_fn> u_fn = get_manager().mk_union_fn(*m_table, *complement_table, nullptr);
        SASSERT(u_fn);
        (*u_fn)(*m_table, *complement_table, nullptr);
    }

    finite_product_relation * finite_product_relation::complement(func_decl* p) const {
        finite_product_relation * res = clone();
        res->complement_self(p);
        return res;
    }

    class finite_product_relation::live_rel_collection_reducer : public table_row_pair_reduce_fn {
        idx_set & m_accumulator;
    public:
        live_rel_collection_reducer(idx_set & accumulator) : m_accumulator(accumulator) {}

        void operator()(table_element * func_columns, const table_element * merged_func_columns) override {
            m_accumulator.insert(static_cast<unsigned>(merged_func_columns[0]));
        }
    };

    void finite_product_relation::collect_live_relation_indexes(idx_set & res) const {
        SASSERT(res.empty());
        unsigned table_data_col_cnt = m_table_sig.size()-1;

        if(table_data_col_cnt==0) {
            if(!get_table().empty()) {
                table_base::iterator iit = get_table().begin();
                table_base::iterator iend = get_table().end();

                SASSERT(iit!=iend);
                res.insert(static_cast<unsigned>((*iit)[0]));
                SASSERT((++iit)==iend);
            }
            return;
        }

        if(!m_live_rel_collection_project) {
            buffer<unsigned, false> removed_cols;
            removed_cols.resize(table_data_col_cnt);
            for(unsigned i=0; i<table_data_col_cnt; i++) {
                removed_cols[i] = i;
            }
            live_rel_collection_reducer * reducer = alloc(live_rel_collection_reducer, m_live_rel_collection_acc);
            m_live_rel_collection_project = get_manager().mk_project_with_reduce_fn(get_table(), removed_cols.size(), removed_cols.c_ptr(), reducer);
            SASSERT(m_live_rel_collection_project);
        }

        m_live_rel_collection_acc.reset();
        scoped_rel<table_base> live_indexes_table = (*m_live_rel_collection_project)(get_table());
        res.swap(m_live_rel_collection_acc);

        SASSERT(live_indexes_table->get_signature().size()==1);
        SASSERT(live_indexes_table->get_signature().functional_columns()==1);
        if(!live_indexes_table->empty()) {
            table_base::iterator iit = live_indexes_table->begin();
            table_base::iterator iend = live_indexes_table->end();

            SASSERT(iit!=iend);
            res.insert(static_cast<unsigned>((*iit)[0]));
            SASSERT((++iit)==iend);
        }
    }

    void finite_product_relation::garbage_collect(bool remove_empty) const {
        idx_set live_indexes;
        collect_live_relation_indexes(live_indexes);

        scoped_rel<table_base> empty_rel_indexes; //populated only if \c remove_empty==true
        table_fact empty_rel_fact;

        unsigned rel_cnt = m_others.size();
#if Z3DEBUG
        unsigned encountered_live_indexes = 0;
#endif
        for(unsigned rel_idx=0; rel_idx<rel_cnt; rel_idx++) {
            if(m_others[rel_idx]==0) {
                continue;
            }
            if(live_indexes.contains(rel_idx)) {
                DEBUG_CODE( encountered_live_indexes++; );
                if(!remove_empty) {
                    continue;
                }
                if(!m_others[rel_idx]->empty()) {
                    continue;
                }
                if(empty_rel_indexes==0) {
                    table_signature empty_rel_indexes_sig;
                    empty_rel_indexes_sig.push_back(s_rel_idx_sort);
                    empty_rel_indexes = get_table_plugin().mk_empty(empty_rel_indexes_sig);
                }
                empty_rel_fact.reset();
                empty_rel_fact.push_back(rel_idx);
                empty_rel_indexes->add_fact(empty_rel_fact);
            }
            m_others[rel_idx]->deallocate();
            m_others[rel_idx] = 0;
            if(rel_idx==m_full_rel_idx) {
                m_full_rel_idx = UINT_MAX;
            }
            recycle_rel_idx(rel_idx);
        }
        SASSERT(encountered_live_indexes==live_indexes.num_elems());

        if(m_available_rel_indexes.size()==m_others.size()) {
            m_available_rel_indexes.reset();
            m_others.reset();
        }

        if(empty_rel_indexes) {
            SASSERT(remove_empty);

            if(!m_empty_rel_removal_filter) {
                unsigned t_joined_cols[] = { m_table_sig.size()-1 };
                unsigned ei_joined_cols[] = { 0 };
                m_empty_rel_removal_filter = get_manager().mk_filter_by_negation_fn(get_table(), *empty_rel_indexes,
                    1, t_joined_cols, ei_joined_cols);
            }

            (*m_empty_rel_removal_filter)(*m_table, *empty_rel_indexes);
        }
    }

    bool finite_product_relation::try_unify_specifications(ptr_vector<finite_product_relation> & rels) {
        if(rels.empty()) {
            return true;
        }
        unsigned sig_sz = rels.back()->get_signature().size();
        svector<bool> table_cols(sig_sz, true);

        ptr_vector<finite_product_relation>::iterator it = rels.begin();
        ptr_vector<finite_product_relation>::iterator end = rels.end();
        for(; it!=end; ++it) {
            finite_product_relation & rel = **it;
            for(unsigned i=0; i<sig_sz; i++) {
                table_cols[i] &= rel.is_table_column(i);
            }
        }

        it = rels.begin();
        for(; it!=end; ++it) {
            finite_product_relation & rel = **it;
            if(!rel.try_modify_specification(table_cols.c_ptr())) {
                return false;
            }
        }
        return true;
    }

    bool finite_product_relation::try_modify_specification(const bool * table_cols) {
        relation_manager & rmgr = get_manager();
        const relation_signature & sig = get_signature();

        unsigned_vector new_rel_columns; //in global signature
        unsigned_vector to_project_away; //in table signature
        relation_signature moved_cols_sig;
        unsigned sig_sz = get_signature().size();
        for(unsigned i=0; i<sig_sz; i++) {
            if(table_cols[i] && !is_table_column(i)) {
                //we cannot move columns from relation into the table, only the other way round
                return false;
            }
            if(is_table_column(i)) {
                if(!table_cols[i]) {
                    new_rel_columns.push_back(i);
                    moved_cols_sig.push_back(sig[i]);
                }
                else {
                    to_project_away.push_back(m_sig2table[i]);
                }
            }
        }
        //remove also the last column with inner relation index
        to_project_away.push_back(get_table().get_signature().size()-1);
        
        if(new_rel_columns.empty()) {
            //the specifications are the same
            return true;
        }
        if(!m_other_plugin.can_handle_signature(moved_cols_sig)) {
            return false;
        }

        //we will create a finite_product_relation that contains only relation columns and contains tuples
        //that appear in the table columns we are making into relation ones. Then we join this table
        //to the current one, and project and reorder the columns as needed to get the right result.
        //It the end we swap the content of the resulting table with the current one.

        scoped_ptr<table_transformer_fn> pr_fun = get_manager().mk_project_fn(get_table(), to_project_away);
        table_base * moved_cols_table = (*pr_fun)(get_table()); //gets destroyed inside moved_cols_trel
        scoped_rel<relation_base> moved_cols_trel = 
            rmgr.get_table_relation_plugin(moved_cols_table->get_plugin()).mk_from_table(moved_cols_sig, moved_cols_table);

        svector<bool> moved_cols_table_flags(moved_cols_sig.size(), false);

        scoped_rel<finite_product_relation> moved_cols_rel = get_plugin().mk_empty(moved_cols_sig, 
            moved_cols_table_flags.c_ptr());

        scoped_ptr<relation_union_fn> union_fun = 
            get_manager().mk_union_fn(*moved_cols_rel, *moved_cols_trel);
        SASSERT(union_fun); //the table_relation should be able to be 'unioned into' any relation

        (*union_fun)(*moved_cols_rel, *moved_cols_trel);

        unsigned_vector all_moved_cols_indexes;
        add_sequence(0, moved_cols_sig.size(), all_moved_cols_indexes);

        scoped_ptr<relation_join_fn> join_fun = get_manager().mk_join_project_fn(*this, *moved_cols_rel, new_rel_columns,
            all_moved_cols_indexes, new_rel_columns, false);

        scoped_rel<relation_base> unordered_rel = (*join_fun)(*this, *moved_cols_rel);
        SASSERT(unordered_rel->get_signature().size()==sig_sz); //the signature size should be the same as original

        //now we need to reorder the columns in the \c new_rel to match the original table
        unsigned_vector permutation;
        unsigned moved_cols_cnt = new_rel_columns.size();
        unsigned next_replaced_idx = 0;
        unsigned next_orig_idx = 0;
        for(unsigned i=0; i<sig_sz; i++) {
            if(next_replaced_idx<moved_cols_cnt && new_rel_columns[next_replaced_idx]==i) {
                permutation.push_back(sig_sz-moved_cols_cnt+next_replaced_idx);
                next_replaced_idx++;
            }
            else {
                permutation.push_back(next_orig_idx++);
            }
        }

        unsigned_vector cycle;
        while(try_remove_cycle_from_permutation(permutation, cycle)) {
            scoped_ptr<relation_transformer_fn> perm_fun = get_manager().mk_rename_fn(*unordered_rel, cycle);
            //the scoped_rel wrapper does the destruction of the old object
            unordered_rel = (*perm_fun)(*unordered_rel);
            cycle.reset();
        }

        finite_product_relation & new_rel = finite_product_relation_plugin::get(*unordered_rel);

        //Swap the content of the current object and new_rel. On exitting the function new_rel will be destroyed
        //since it points to the content of scoped_rel<relation_base> unordered_rel.
        swap(new_rel);
        
        return true;
    }

    void finite_product_relation::display(std::ostream & out) const {

        garbage_collect(true);

        out << "finite_product_relation:\n";

        out << " table:\n";
        get_table().display(out);

        unsigned other_sz = m_others.size();
        for(unsigned i=0; i<other_sz; i++) {
            if(m_others[i]==0) {
                //unreferenced relation index
                continue;
            }
            out << " inner relation " << i << ":\n";
            get_inner_rel(i).display(out);
        }
    }

    void finite_product_relation::display_tuples(func_decl & pred, std::ostream & out) const {
        out << "Tuples in " << pred.get_name() << ": \n";
        if(!m_other_plugin.from_table()) {
            display(out);
            return;
        }

        context & ctx = get_context();

        table_fact tfact;
        table_fact ofact;

        unsigned sig_sz = get_signature().size();
        unsigned rel_idx_col = m_table_sig.size()-1;

        table_base::iterator it = get_table().begin();
        table_base::iterator end = get_table().end();
        for(; it!=end ; ++it) {
            it->get_fact(tfact);

            const table_relation & orel = static_cast<const table_relation &>(get_inner_rel(tfact[rel_idx_col]));
            const table_base & otable = orel.get_table();
            table_base::iterator oit = otable.begin();
            table_base::iterator oend = otable.end();
            for(; oit!=oend; ++oit) {
                oit->get_fact(ofact);

                out << "\t(";
                for(unsigned i=0; i<sig_sz; i++) {
                    if(i!=0) {
                        out << ',';
                    }

                    table_element sym_num;
                    if(is_table_column(i)) {
                        sym_num = tfact[m_sig2table[i]];
                    }
                    else {
                        sym_num = ofact[m_sig2other[i]];
                    }
                    relation_sort sort = pred.get_domain(i);

                    out << ctx.get_argument_name(&pred, i) << '=';
                    ctx.print_constant_name(sort, sym_num, out);
                    out << '(' << sym_num << ')';
                }
                out << ")\n";

            }
        }
    }

    void finite_product_relation::to_formula(expr_ref& fml) const {
        relation_signature const& sig = get_signature();
        ast_manager& m = fml.get_manager();
        expr_ref_vector disjs(m), conjs(m);
        expr_ref tmp(m);
        dl_decl_util util(m);
        shift_vars sh(m);
        table_fact fact;
        table_base::iterator it = get_table().begin();
        table_base::iterator end = get_table().end();
        unsigned fact_sz = m_table_sig.size();
        for(; it!=end ; ++it) {
            it->get_fact(fact);
            conjs.reset();
            SASSERT(fact.size() == fact_sz);
            unsigned rel_idx = static_cast<unsigned>(fact[fact_sz-1]);
            m_others[rel_idx]->to_formula(tmp);
            for (unsigned i = 0; i + 1 < fact_sz; ++i) {
                conjs.push_back(m.mk_eq(m.mk_var(i, sig[i]), util.mk_numeral(fact[i], sig[i])));
            }
            sh(tmp, fact_sz-1, tmp);
            conjs.push_back(tmp);
            disjs.push_back(m.mk_and(conjs.size(), conjs.c_ptr()));
        }
        bool_rewriter(m).mk_or(disjs.size(), disjs.c_ptr(), fml);        
    }

};

