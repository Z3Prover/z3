/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_explanations.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-11-08.

Revision History:

--*/

#include <sstream>
#include "ast/ast_pp.h"
#include "muz/rel/dl_sieve_relation.h"

namespace datalog {

    // -----------------------------------
    //
    // sieve_relation
    //
    // -----------------------------------

    sieve_relation::sieve_relation(sieve_relation_plugin & p, const relation_signature & s,
                const bool * inner_columns, relation_base * inner) 
            : relation_base(p, s), m_inner_cols(s.size(), inner_columns), m_inner(inner) { 
        unsigned n = s.size();
        for(unsigned i=0; i<n; i++) {
            if(inner_columns && inner_columns[i]) {
                unsigned inner_idx = m_inner2sig.size();
                SASSERT(get_inner().get_signature()[inner_idx]==s[i]);
                m_sig2inner.push_back(inner_idx);
                m_inner2sig.push_back(i);
            }
            else {
                m_sig2inner.push_back(UINT_MAX);
                m_ignored_cols.push_back(i);
            }
        }

        set_kind(p.get_relation_kind(*this, inner_columns));
    }

    void sieve_relation::add_fact(const relation_fact & f) {
        relation_fact inner_f = f;
        project_out_vector_columns(inner_f, m_ignored_cols);
        get_inner().add_fact(inner_f);
    }

    bool sieve_relation::contains_fact(const relation_fact & f) const {
        relation_fact inner_f = f;
        project_out_vector_columns(inner_f, m_ignored_cols);
        return get_inner().contains_fact(inner_f);
    }

    sieve_relation * sieve_relation::clone() const {
        relation_base * new_inner = get_inner().clone();
        return get_plugin().mk_from_inner(get_signature(), m_inner_cols.c_ptr(), new_inner);
    }

    relation_base * sieve_relation::complement(func_decl* p) const {
        //this is not precisely a complement, because we still treat the ignored columns as
        //full, but it should give reasonable results inside the product relation
        relation_base * new_inner = get_inner().complement(p);
        return get_plugin().mk_from_inner(get_signature(), m_inner_cols.c_ptr(), new_inner);
    }

    void sieve_relation::to_formula(expr_ref& fml) const {
        ast_manager& m = fml.get_manager();
        expr_ref_vector s(m);
        expr_ref tmp(m);
        relation_signature const& sig = get_inner().get_signature();
        unsigned sz = sig.size();
        for (unsigned i = sz ; i > 0; ) {
            --i;
            unsigned idx = m_inner2sig[i];
            s.push_back(m.mk_var(idx, sig[i]));
        }
        get_inner().to_formula(tmp);
        fml = get_plugin().get_context().get_var_subst()(tmp, sz, s.c_ptr());
    }


    void sieve_relation::display(std::ostream & out) const {
        out << "Sieve relation ";
        print_container(m_inner_cols, out);
        out <<"\n";
        get_inner().display(out);
    }


    // -----------------------------------
    //
    // sieve_relation_plugin
    //
    // -----------------------------------

    sieve_relation_plugin & sieve_relation_plugin::get_plugin(relation_manager & rmgr) {
        sieve_relation_plugin * res = static_cast<sieve_relation_plugin *>(rmgr.get_relation_plugin(get_name()));
        if(!res) {
            res = alloc(sieve_relation_plugin, rmgr);
            rmgr.register_plugin(res);
        }
        return *res;
    }

    sieve_relation& sieve_relation_plugin::get(relation_base& r) {
        return dynamic_cast<sieve_relation&>(r);
    }

    sieve_relation const & sieve_relation_plugin::get(relation_base const& r) {
        return dynamic_cast<sieve_relation const&>(r);
    }

    sieve_relation* sieve_relation_plugin::get(relation_base* r) {
        return dynamic_cast<sieve_relation*>(r);
    }

    sieve_relation const* sieve_relation_plugin::get(relation_base const* r) {
        return dynamic_cast<sieve_relation const*>(r);
    }

    sieve_relation_plugin::sieve_relation_plugin(relation_manager & manager) 
            : relation_plugin(get_name(), manager, ST_SIEVE_RELATION), 
            m_spec_store(*this) {}

    void sieve_relation_plugin::initialize(family_id fid) { 
        relation_plugin::initialize(fid);
        m_spec_store.add_available_kind(get_kind());
    }

    family_id sieve_relation_plugin::get_relation_kind(const relation_signature & sig, 
            const bool * inner_columns, family_id inner_kind) {
        rel_spec spec(sig.size(), inner_columns, inner_kind);
        return m_spec_store.get_relation_kind(sig, spec);
    }

    family_id sieve_relation_plugin::get_relation_kind(sieve_relation & r, const bool * inner_columns) {
        const relation_signature & sig = r.get_signature();
        return get_relation_kind(sig, inner_columns, r.get_inner().get_kind());
    }

    void sieve_relation_plugin::extract_inner_columns(const relation_signature & s, relation_plugin & inner, 
            svector<bool> & inner_columns) {
        SASSERT(inner_columns.size()==s.size());
        unsigned n = s.size();
        relation_signature inner_sig_singleton;
        for(unsigned i=0; i<n; i++) {
            inner_sig_singleton.reset();
            inner_sig_singleton.push_back(s[i]);
            inner_columns[i] = inner.can_handle_signature(inner_sig_singleton);
        }
#if Z3DEBUG 
        //we assume that if a relation plugin can handle two sets of columns separetely, 
        //it can also handle them in one relation
        relation_signature inner_sig;
        collect_inner_signature(s, inner_columns, inner_sig);
        SASSERT(inner.can_handle_signature(inner_sig));
#endif
    }

    void sieve_relation_plugin::collect_inner_signature(const relation_signature & s, 
            const svector<bool> & inner_columns, relation_signature & inner_sig) {
        SASSERT(inner_columns.size()==s.size());
        inner_sig.reset();
        unsigned n = s.size();
        for(unsigned i=0; i<n; i++) {
            if(inner_columns[i]) {
                inner_sig.push_back(s[i]);
            }
        }
    }

    void sieve_relation_plugin::extract_inner_signature(const relation_signature & s, 
            relation_signature & inner_sig) {
        UNREACHABLE();
#if 0
        svector<bool> inner_cols(s.size());
        extract_inner_columns(s, inner_cols.c_ptr());
        collect_inner_signature(s, inner_cols, inner_sig);
#endif
    }

    bool sieve_relation_plugin::can_handle_signature(const relation_signature & s) {
        //we do not want this plugin to handle anything by default
        return false;
#if 0
        relation_signature inner_sig;
        extract_inner_signature(s, inner_sig);
        SASSERT(inner_sig.size()<=s.size());
        return !inner_sig.empty() && inner_sig.size()!=s.size();
#endif
    }

    sieve_relation * sieve_relation_plugin::mk_from_inner(const relation_signature & s, const bool * inner_columns, 
            relation_base * inner_rel) {
        SASSERT(!inner_rel->get_plugin().is_sieve_relation()); //it does not make sense to make a sieve of a sieve
        return alloc(sieve_relation, *this, s, inner_columns, inner_rel);
    }

    sieve_relation * sieve_relation_plugin::mk_empty(const sieve_relation & original) {
        return static_cast<sieve_relation *>(mk_empty(original.get_signature(), original.get_kind()));
    }

    relation_base * sieve_relation_plugin::mk_empty(const relation_base & original) {
        return mk_empty(static_cast<const sieve_relation &>(original));
    }

    relation_base * sieve_relation_plugin::mk_empty(const relation_signature & s, family_id kind) {
        rel_spec spec;
        m_spec_store.get_relation_spec(s, kind, spec);
        relation_signature inner_sig;
        collect_inner_signature(s, spec.m_inner_cols, inner_sig);
        relation_base * inner = get_manager().mk_empty_relation(inner_sig, spec.m_inner_kind);               
        return mk_from_inner(s, spec.m_inner_cols.c_ptr(), inner);
    }


    relation_base * sieve_relation_plugin::mk_empty(const relation_signature & s) {
        UNREACHABLE();
        return nullptr;
#if 0
        svector<bool> inner_cols(s.size());
        extract_inner_columns(s, inner_cols.c_ptr());
        return mk_empty(s, inner_cols.c_ptr());
#endif
    }

    sieve_relation * sieve_relation_plugin::mk_empty(const relation_signature & s, relation_plugin & inner_plugin) {
        SASSERT(!inner_plugin.is_sieve_relation()); //it does not make sense to make a sieve of a sieve
        svector<bool> inner_cols(s.size());
        extract_inner_columns(s, inner_plugin, inner_cols);
        relation_signature inner_sig;
        collect_inner_signature(s, inner_cols, inner_sig);
        relation_base * inner_rel = inner_plugin.mk_empty(inner_sig);
        return mk_from_inner(s, inner_cols, inner_rel);
    }

    relation_base * sieve_relation_plugin::mk_full(func_decl* p, const relation_signature & s) {
        relation_signature empty_sig;
        relation_plugin& plugin = get_manager().get_appropriate_plugin(s);
        relation_base * inner = plugin.mk_full(p, empty_sig, null_family_id);
        svector<bool> inner_cols;
        inner_cols.resize(s.size(), false);
        return mk_from_inner(s, inner_cols, inner);
    }

    sieve_relation * sieve_relation_plugin::full(func_decl* p, const relation_signature & s, relation_plugin & inner_plugin) {
        SASSERT(!inner_plugin.is_sieve_relation()); //it does not make sense to make a sieve of a sieve
        svector<bool> inner_cols(s.size());
        extract_inner_columns(s, inner_plugin, inner_cols);
        relation_signature inner_sig;
        collect_inner_signature(s, inner_cols, inner_sig);
        relation_base * inner_rel = inner_plugin.mk_full(p, inner_sig, null_family_id);
        return mk_from_inner(s, inner_cols, inner_rel);
    }

    class sieve_relation_plugin::join_fn : public convenient_relation_join_fn {
        sieve_relation_plugin & m_plugin;
        unsigned_vector m_inner_cols_1;
        unsigned_vector m_inner_cols_2;
        svector<bool> m_result_inner_cols;

        scoped_ptr<relation_join_fn> m_inner_join_fun;
    public:
        join_fn(sieve_relation_plugin & p, const relation_base & r1, const relation_base & r2, unsigned col_cnt, 
                    const unsigned * cols1, const unsigned * cols2, relation_join_fn * inner_join_fun)
                : convenient_relation_join_fn(r1.get_signature(), r2.get_signature(), col_cnt, cols1, cols2),
                m_plugin(p),
                m_inner_join_fun(inner_join_fun) {
            bool r1_sieved = r1.get_plugin().is_sieve_relation();
            bool r2_sieved = r2.get_plugin().is_sieve_relation();
            const sieve_relation * sr1 = r1_sieved ? static_cast<const sieve_relation *>(&r1) : nullptr;
            const sieve_relation * sr2 = r2_sieved ? static_cast<const sieve_relation *>(&r2) : nullptr;
            if(r1_sieved) {
                m_result_inner_cols.append(sr1->m_inner_cols);
            }
            else {
                m_result_inner_cols.resize(r1.get_signature().size(), true);
            }
            if(r2_sieved) {
                m_result_inner_cols.append(sr2->m_inner_cols);
            }
            else {
                m_result_inner_cols.resize(m_result_inner_cols.size() + r2.get_signature().size(), true);
            }
        }

        relation_base * operator()(const relation_base & r1, const relation_base & r2) override {
            bool r1_sieved = r1.get_plugin().is_sieve_relation();
            bool r2_sieved = r2.get_plugin().is_sieve_relation();
            SASSERT(r1_sieved || r2_sieved);
            const sieve_relation * sr1 = r1_sieved ? static_cast<const sieve_relation *>(&r1) : nullptr;
            const sieve_relation * sr2 = r2_sieved ? static_cast<const sieve_relation *>(&r2) : nullptr;
            const relation_base & inner1 = r1_sieved ? sr1->get_inner() : r1;
            const relation_base & inner2 = r2_sieved ? sr2->get_inner() : r2;

            relation_base * inner_res = (*m_inner_join_fun)(inner1, inner2);

            return m_plugin.mk_from_inner(get_result_signature(), m_result_inner_cols.c_ptr(), inner_res);
        }
    };

    relation_join_fn * sieve_relation_plugin::mk_join_fn(const relation_base & r1, const relation_base & r2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if( &r1.get_plugin()!=this && &r2.get_plugin()!=this ) {
            //we create just operations that involve the current plugin
            return nullptr;
        }
        bool r1_sieved = r1.get_plugin().is_sieve_relation();
        bool r2_sieved = r2.get_plugin().is_sieve_relation();
        const sieve_relation * sr1 = r1_sieved ? static_cast<const sieve_relation *>(&r1) : nullptr;
        const sieve_relation * sr2 = r2_sieved ? static_cast<const sieve_relation *>(&r2) : nullptr;
        const relation_base & inner1 = r1_sieved ? sr1->get_inner() : r1;
        const relation_base & inner2 = r2_sieved ? sr2->get_inner() : r2;

        unsigned_vector inner_cols1;
        unsigned_vector inner_cols2;

        for(unsigned i=0; i<col_cnt; i++) {
            //if at least one end of an equality is not an inner column, we ignore that equality
            //(which introduces imprecision)
            if(r1_sieved && !sr1->is_inner_col(cols1[i])) {
                continue;
            }
            if(r2_sieved && !sr2->is_inner_col(cols2[i])) {
                continue;
            }
            inner_cols1.push_back( r1_sieved ? sr1->get_inner_col(cols1[i]) : cols1[i] );
            inner_cols2.push_back( r2_sieved ? sr2->get_inner_col(cols2[i]) : cols2[i] );
        }

        relation_join_fn * inner_join_fun = get_manager().mk_join_fn(inner1, inner2, inner_cols1, inner_cols2, false);
        if(!inner_join_fun) {
            return nullptr;
        }
        return alloc(join_fn, *this, r1, r2, col_cnt, cols1, cols2, inner_join_fun);
    }


    class sieve_relation_plugin::transformer_fn : public convenient_relation_transformer_fn {
        svector<bool> m_result_inner_cols;

        scoped_ptr<relation_transformer_fn> m_inner_fun;
    public:
        transformer_fn(relation_transformer_fn * inner_fun, const relation_signature & result_sig, 
                    const bool * result_inner_cols)
                : m_result_inner_cols(result_sig.size(), result_inner_cols), m_inner_fun(inner_fun) {
            get_result_signature() = result_sig;
        }

        relation_base * operator()(const relation_base & r0) override {
            SASSERT(r0.get_plugin().is_sieve_relation());
            const sieve_relation & r = static_cast<const sieve_relation &>(r0);
            sieve_relation_plugin & plugin = r.get_plugin();

            relation_base * inner_res = (*m_inner_fun)(r.get_inner());

            return plugin.mk_from_inner(get_result_signature(), m_result_inner_cols.c_ptr(), inner_res);
        }
    };

    relation_transformer_fn * sieve_relation_plugin::mk_project_fn(const relation_base & r0, unsigned col_cnt, 
            const unsigned * removed_cols) {
        if(&r0.get_plugin()!=this) {
            return nullptr;
        }
        const sieve_relation & r = static_cast<const sieve_relation &>(r0);
        unsigned_vector inner_removed_cols;

        for(unsigned i=0; i<col_cnt; i++) {
            unsigned col = removed_cols[i];
            if(r.is_inner_col(col)) {
                inner_removed_cols.push_back(r.get_inner_col(col));
            }
        }

        svector<bool> result_inner_cols = r.m_inner_cols;
        project_out_vector_columns(result_inner_cols, col_cnt, removed_cols);

        relation_signature result_sig;
        relation_signature::from_project(r.get_signature(), col_cnt, removed_cols, result_sig);

        relation_transformer_fn * inner_fun;
        if(inner_removed_cols.empty()) {
            inner_fun = alloc(identity_relation_transformer_fn);
        }
        else {
            inner_fun = get_manager().mk_project_fn(r.get_inner(), inner_removed_cols);
        }
        
        if(!inner_fun) {
            return nullptr;
        }
        return alloc(transformer_fn, inner_fun, result_sig, result_inner_cols.c_ptr());
    }

    relation_transformer_fn * sieve_relation_plugin::mk_rename_fn(const relation_base & r0, 
            unsigned cycle_len, const unsigned * permutation_cycle) {
        if(&r0.get_plugin()!=this) {
            return nullptr;
        }
        const sieve_relation & r = static_cast<const sieve_relation &>(r0);

        unsigned sig_sz = r.get_signature().size();
        unsigned_vector permutation;
        add_sequence(0, sig_sz, permutation);
        permutate_by_cycle(permutation, cycle_len, permutation_cycle);

        bool inner_identity;
        unsigned_vector inner_permutation;
        collect_sub_permutation(permutation, r.m_sig2inner, inner_permutation, inner_identity);

        svector<bool> result_inner_cols = r.m_inner_cols;
        permutate_by_cycle(result_inner_cols, cycle_len, permutation_cycle);

        relation_signature result_sig;
        relation_signature::from_rename(r.get_signature(), cycle_len, permutation_cycle, result_sig);

        relation_transformer_fn * inner_fun = 
            get_manager().mk_permutation_rename_fn(r.get_inner(), inner_permutation);
        if(!inner_fun) {
            return nullptr;
        }
        return alloc(transformer_fn, inner_fun, result_sig, result_inner_cols.c_ptr());
    }


    class sieve_relation_plugin::union_fn : public relation_union_fn {
        scoped_ptr<relation_union_fn> m_union_fun;
    public:
        union_fn(relation_union_fn * union_fun) : m_union_fun(union_fun) {}

        void operator()(relation_base & tgt, const relation_base & src, relation_base * delta) override {
            bool tgt_sieved = tgt.get_plugin().is_sieve_relation();
            bool src_sieved = src.get_plugin().is_sieve_relation();
            bool delta_sieved = delta && delta->get_plugin().is_sieve_relation();
            sieve_relation * stgt = tgt_sieved ? static_cast<sieve_relation *>(&tgt) : nullptr;
            const sieve_relation * ssrc = src_sieved ? static_cast<const sieve_relation *>(&src) : nullptr;
            sieve_relation * sdelta = delta_sieved ? static_cast<sieve_relation *>(delta) : nullptr;
            relation_base & itgt = tgt_sieved ? stgt->get_inner() : tgt;
            const relation_base & isrc = src_sieved ? ssrc->get_inner() : src;
            relation_base * idelta = delta_sieved ? &sdelta->get_inner() : delta;

            (*m_union_fun)(itgt, isrc, idelta);
        }
    };

    relation_union_fn * sieve_relation_plugin::mk_union_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta) {
        if(&tgt.get_plugin()!=this && &src.get_plugin()!=this && (delta && &delta->get_plugin()!=this)) {
            //we create the operation only if it involves this plugin
            return nullptr;
        }

        bool tgt_sieved = tgt.get_plugin().is_sieve_relation();
        bool src_sieved = src.get_plugin().is_sieve_relation();
        bool delta_sieved = delta && delta->get_plugin().is_sieve_relation();
        const sieve_relation * stgt = tgt_sieved ? static_cast<const sieve_relation *>(&tgt) : nullptr;
        const sieve_relation * ssrc = src_sieved ? static_cast<const sieve_relation *>(&src) : nullptr;
        const sieve_relation * sdelta = delta_sieved ? static_cast<const sieve_relation *>(delta) : nullptr;
        const relation_base & itgt = tgt_sieved ? stgt->get_inner() : tgt;
        const relation_base & isrc = src_sieved ? ssrc->get_inner() : src;
        const relation_base * idelta = delta_sieved ? &sdelta->get_inner() : delta;

        //Now we require that the sieved and inner columns must match on all relations.
        //We may want to allow for some cases of misalignment even though it could introcude imprecision
        if( tgt_sieved && src_sieved && (!delta || delta_sieved) ) {
            if( !vectors_equal(stgt->m_inner_cols, ssrc->m_inner_cols)
                || (delta && !vectors_equal(stgt->m_inner_cols, sdelta->m_inner_cols)) ) {
                return nullptr;
            }
        }
        else {
            if( (stgt && !stgt->no_sieved_columns()) 
                  || (ssrc && !ssrc->no_sieved_columns())
                  || (sdelta && !sdelta->no_sieved_columns()) ) {
                //We have an unsieved relation and then some relation with some sieved columns,
                //which means there is an misalignment.
                return nullptr;
            }
        }

        relation_union_fn * union_fun = get_manager().mk_union_fn(itgt, isrc, idelta);
        if(!union_fun) {
            return nullptr;
        }

        return alloc(union_fn, union_fun);
    }


    class sieve_relation_plugin::filter_fn : public relation_mutator_fn {
        scoped_ptr<relation_mutator_fn> m_inner_fun;
    public:
        filter_fn(relation_mutator_fn * inner_fun) 
            : m_inner_fun(inner_fun) {}

        void operator()(relation_base & r0) override {
            SASSERT(r0.get_plugin().is_sieve_relation());
            sieve_relation & r = static_cast<sieve_relation &>(r0);

            (*m_inner_fun)(r.get_inner());
        }
    };

    relation_mutator_fn * sieve_relation_plugin::mk_filter_identical_fn(const relation_base & r0, 
            unsigned col_cnt, const unsigned * identical_cols) {
        if(&r0.get_plugin()!=this) {
            return nullptr;
        }
        const sieve_relation & r = static_cast<const sieve_relation &>(r0);
        unsigned_vector inner_icols;

        //we ignore the columns which do not belong to the inner relation (which introduces imprecision)
        for(unsigned i=0; i<col_cnt; i++) {
            unsigned col = identical_cols[i];
            if(r.is_inner_col(col)) {
                inner_icols.push_back(r.get_inner_col(col));
            }
        }

        if(inner_icols.size()<2) {
            return alloc(identity_relation_mutator_fn);
        }

        relation_mutator_fn * inner_fun = get_manager().mk_filter_identical_fn(r.get_inner(), inner_icols);
        if(!inner_fun) {
            return nullptr;
        }
        return alloc(filter_fn, inner_fun);
    }

    relation_mutator_fn * sieve_relation_plugin::mk_filter_equal_fn(const relation_base & r0, 
            const relation_element & value, unsigned col) {
        if(&r0.get_plugin()!=this) {
            return nullptr;
        }
        const sieve_relation & r = static_cast<const sieve_relation &>(r0);
        if(!r.is_inner_col(col)) {
            //if the column which do not belong to the inner relation, we do nothing (which introduces imprecision)
            return alloc(identity_relation_mutator_fn);
        }
        unsigned inner_col = r.get_inner_col(col);

        relation_mutator_fn * inner_fun = get_manager().mk_filter_equal_fn(r.get_inner(), value, inner_col);
        if(!inner_fun) {
            return nullptr;
        }
        return alloc(filter_fn, inner_fun);
    }

    relation_mutator_fn * sieve_relation_plugin::mk_filter_interpreted_fn(const relation_base & rb, 
            app * condition) {
        if(&rb.get_plugin()!=this) {
            return nullptr;
        }
        ast_manager & m = get_ast_manager();
        const sieve_relation & r = static_cast<const sieve_relation &>(rb);
        const relation_signature sig = r.get_signature();
        unsigned sz = sig.size();

        var_idx_set& cond_vars = get_context().get_rule_manager().collect_vars(condition);
        expr_ref_vector subst_vect(m);
        subst_vect.resize(sz);
        unsigned subst_ofs = sz-1;
        for(unsigned i=0; i<sz; i++) {
            if(!cond_vars.contains(i)) {
                continue;
            }
            if(!r.is_inner_col(i)) {
                //If the condition involves columns which do not belong to the inner relation, 
                //we do nothing (which introduces imprecision).
                //Maybe we might try to do some quantifier elimination...
                return alloc(identity_relation_mutator_fn);
            }
            subst_vect[subst_ofs-i] = m.mk_var(r.m_sig2inner[i], sig[i]);
        }
        expr_ref inner_cond = get_context().get_var_subst()(condition, subst_vect.size(), subst_vect.c_ptr());

        relation_mutator_fn * inner_fun = get_manager().mk_filter_interpreted_fn(r.get_inner(), to_app(inner_cond));
        if(!inner_fun) {
            return nullptr;
        }
        return alloc(filter_fn, inner_fun);
    }

    class sieve_relation_plugin::negation_filter_fn : public relation_intersection_filter_fn {
        scoped_ptr<relation_intersection_filter_fn> m_inner_fun;
    public:
        negation_filter_fn(relation_intersection_filter_fn * inner_fun)
            : m_inner_fun(inner_fun) {}

        void operator()(relation_base & r, const relation_base & neg) override {
            bool r_sieved = r.get_plugin().is_sieve_relation();
            bool neg_sieved = neg.get_plugin().is_sieve_relation();
            SASSERT(r_sieved || neg_sieved);
            sieve_relation * sr = r_sieved ? static_cast<sieve_relation *>(&r) : nullptr;
            const sieve_relation * sneg = neg_sieved ? static_cast<const sieve_relation *>(&neg) : nullptr;
            relation_base & inner_r = r_sieved ? sr->get_inner() : r;
            const relation_base & inner_neg = neg_sieved ? sneg->get_inner() : neg;

            (*m_inner_fun)(inner_r, inner_neg);
        }
    };

    relation_intersection_filter_fn * sieve_relation_plugin::mk_filter_by_negation_fn(const relation_base & r, 
            const relation_base & neg, unsigned col_cnt, const unsigned * r_cols, 
            const unsigned * neg_cols) {
        if(&r.get_plugin()!=this && &neg.get_plugin()!=this) {
            //we create just operations that involve the current plugin
            return nullptr;
        }
        bool r_sieved = r.get_plugin().is_sieve_relation();
        bool neg_sieved = neg.get_plugin().is_sieve_relation();
        SASSERT(r_sieved || neg_sieved);
        const sieve_relation * sr = r_sieved ? static_cast<const sieve_relation *>(&r) : nullptr;
        const sieve_relation * sneg = neg_sieved ? static_cast<const sieve_relation *>(&neg) : nullptr;
        const relation_base & inner_r = r_sieved ? sr->get_inner() : r;
        const relation_base & inner_neg = neg_sieved ? sneg->get_inner() : neg;

        unsigned_vector ir_cols;
        unsigned_vector ineg_cols;

        for(unsigned i=0; i<col_cnt; i++) {
            //if at least one end of an equality is not an inner column, we ignore that equality
            //(which introduces imprecision)
            bool r_col_inner = r_sieved && !sr->is_inner_col(r_cols[i]);
            bool neg_col_inner = neg_sieved && !sneg->is_inner_col(neg_cols[i]);
            if(r_col_inner && neg_col_inner) {
                ir_cols.push_back( r_sieved ? sr->get_inner_col(i) : i );
                ineg_cols.push_back( neg_sieved ? sneg->get_inner_col(i) : i );
            }
            else if(!r_col_inner && neg_col_inner) {
                //Sieved (i.e. full) column in r is matched on an inner column in neg.
                //If we assume the column in neg is not full, no rows from the inner relation of
                //r would be removed. So in this case we perform no operation at cost of a little 
                //impresicion.
                return alloc(identity_relation_intersection_filter_fn);
            }
            else {
                //Inner or sieved column in r must match a sieved column in neg.
                //Since sieved columns are full, this is always true so we can skip the equality.
                continue;
            }
        }

        relation_intersection_filter_fn * inner_fun = 
            get_manager().mk_filter_by_negation_fn(inner_r, inner_neg, ir_cols, ineg_cols);
        if(!inner_fun) {
            return nullptr;
        }
        return alloc(negation_filter_fn, inner_fun);
    }

    
};
