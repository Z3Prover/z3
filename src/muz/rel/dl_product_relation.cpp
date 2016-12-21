/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_product_relation.cpp

Abstract:

    A Relation combinator.

Author:

    Nikolaj Bjorner (nbjorner) 2010-4-11

Revision History:

Notes:

    <R,S> join <R',S'> = <R join R', S join S'>
           more refined version lets augment the product 
           relation as a consequence of join.
           <R,S> join Q =
             <R,S,T> join <T,T,Q> = 
             <R join T, S join T, T join Q>

    <R,S> u <R',S'> = <R u R', S u S'> 
            more refined version:
                    < (R u R') n (R u S') n (R' u S), (S u S') n (S u R') n (S' u R)>
            

    proj <R, S>    = < proj R, proj S>

    <R, S> & phi   = <R & phi, S & phi>
                    attach S to [R & phi] whenever R & phi can propagate to S
                    

    <R, S>[rename] = <R[rename], S[rename]>



--*/


#include "dl_sieve_relation.h"
#include "dl_table_relation.h"
#include "dl_product_relation.h"
#include "bool_rewriter.h"
#include "ast_pp.h"

namespace datalog {

    // -----------------------------------
    //
    // product_relation_plugin
    //
    // -----------------------------------

    product_relation_plugin & product_relation_plugin::get_plugin(relation_manager & rmgr) {
        product_relation_plugin * res = 
            static_cast<product_relation_plugin *>(rmgr.get_relation_plugin(get_name()));
        if(!res) {
            res = alloc(product_relation_plugin, rmgr);
            rmgr.register_plugin(res);
        }
        return *res;
    }

    product_relation_plugin::product_relation_plugin(relation_manager& m):
        relation_plugin(product_relation_plugin::get_name(), m, ST_PRODUCT_RELATION), 
        m_spec_store(*this) {
    }

    void product_relation_plugin::initialize(family_id fid) { 
        relation_plugin::initialize(fid);
        m_spec_store.add_available_kind(get_kind());
    }

    family_id product_relation_plugin::get_relation_kind(const relation_signature & sig, const rel_spec & spec) {
        SASSERT(spec.well_formed());
        return m_spec_store.get_relation_kind(sig, spec);
    }

    family_id product_relation_plugin::get_relation_kind(const product_relation & r) {
        return get_relation_kind(r.get_signature(), r.m_spec);
    }

    bool product_relation_plugin::can_handle_signature(const relation_signature & s) {
        return m_spec_store.contains_signature(s);
    }

    bool product_relation_plugin::can_handle_signature(const relation_signature & s, family_id k) {
        return true;
    }

    product_relation& product_relation_plugin::get(relation_base& r) {
        return dynamic_cast<product_relation&>(r);
    }

    product_relation const & product_relation_plugin::get(relation_base const& r) {
        return dynamic_cast<product_relation const&>(r);
    }

    product_relation* product_relation_plugin::get(relation_base* r) {
        return dynamic_cast<product_relation*>(r);
    }

    product_relation const* product_relation_plugin::get(relation_base const* r) {
        return dynamic_cast<product_relation const*>(r);
    }

    bool product_relation_plugin::is_product_relation(relation_base const& r) {
        return r.get_plugin().get_name() == product_relation_plugin::get_name();
    }

    bool product_relation_plugin::are_aligned(const product_relation& r1, const product_relation& r2) {
        unsigned sz = r1.size();
        if(sz!=r2.size()) {
            return false;
        }
        for(unsigned i=0; i<sz; i++) {
            if(r1[i].get_kind()!=r2[i].get_kind()) {
                return false;
            }
        }
        return true;
    }

    void product_relation_plugin::get_common_spec(const ptr_vector<const product_relation> & rels, 
            rel_spec & res) {
        vector<rel_spec> specs;
        ptr_vector<const product_relation>::const_iterator rit = rels.begin();
        ptr_vector<const product_relation>::const_iterator rend = rels.end();
        for(; rit!=rend; ++rit) {
            specs.push_back((*rit)->m_spec);
            SASSERT(specs.back().well_formed());
            std::sort(specs.back().begin(), specs.back().end());
        }

        vector<rel_spec>::iterator sit = specs.begin(), send = specs.end();

        res.reset();
        for(;;) {
            family_id next = -1;

            sit = specs.begin();
            for(; sit!=send; ++sit) {
                rel_spec & s = *sit;
                if(!s.empty() && s.back()>next) {
                    next = s.back();
                }
            }
            if(next==-1) {
                //we're done
                break;
            }
            res.push_back(next);
            sit = specs.begin();
            for(; sit!=send; ++sit) {
                rel_spec & s = *sit;
                while (!s.empty() && s.back()==next) {
                    s.pop_back();
                }
            }
        }
    }


    relation_base * product_relation_plugin::mk_empty(const relation_signature & s) {
        return alloc(product_relation,*this, s);
    }

    relation_base * product_relation_plugin::mk_empty(const relation_signature & s, family_id kind) {
        rel_spec spec;
        m_spec_store.get_relation_spec(s, kind, spec);
        relation_vector inner_rels;
        unsigned rel_cnt = spec.size();
        for(unsigned i=0; i<rel_cnt; i++) {
            inner_rels.push_back(get_manager().mk_empty_relation(s, spec[i]));
        }
        return alloc(product_relation,*this, s, inner_rels.size(), inner_rels.c_ptr());
    }

    relation_base * product_relation_plugin::mk_full(func_decl* p, const relation_signature & s, family_id kind) {
        if (kind == null_family_id || !m_spec_store.contains_signature(s)) {
            product_relation* result = alloc(product_relation, *this, s);
            result->m_default_empty = false;
            return result;
        }
        rel_spec spec;
        m_spec_store.get_relation_spec(s, kind, spec);
        SASSERT(spec.well_formed());
        relation_vector inner_rels;
        unsigned rel_cnt = spec.size();
        for(unsigned i=0; i<rel_cnt; i++) {
            inner_rels.push_back(get_manager().mk_full_relation(s, p, spec[i]));
        }
        return alloc(product_relation,*this, s, inner_rels.size(), inner_rels.c_ptr());
    }

    relation_base * product_relation_plugin::mk_full(func_decl* p, const relation_signature & s) {
        return alloc(product_relation, *this, s);
    }

    class product_relation_plugin::join_fn : public convenient_relation_join_fn {
        enum kind_t { T_INPUT, T_FULL};
        product_relation_plugin&     m_plugin;
        ptr_vector<relation_join_fn> m_joins;
        ptr_vector<relation_base> m_full;
        unsigned_vector           m_offset1;
        svector<kind_t>           m_kind1;
        unsigned_vector           m_offset2;
        svector<kind_t>           m_kind2;

        const relation_base & get_nonsieve_relation(const relation_base & r) {
            relation_plugin & rp = r.get_plugin();
            if(rp.is_sieve_relation()) {
                return static_cast<const sieve_relation &>(r).get_inner();
            }
            else {
                return r;
            }
        }

        relation_plugin & get_nonsieve_plugin(const relation_base & r) {
            return get_nonsieve_relation(r).get_plugin();
        }

        family_id get_nonsieve_kind(const relation_base & r) {
            return get_nonsieve_relation(r).get_kind();
        }

        /**
           A tableish relatio is either a table_relation or a sieve_relation with a table_relation inside.
        */
        bool is_tableish_relation(const relation_base & r) {
            return get_nonsieve_plugin(r).from_table();
        }

        relation_base * get_full_tableish_relation(const relation_signature & sig, func_decl* p, family_id kind) {
            relation_manager& rmgr = m_plugin.get_manager();
            table_signature tsig;
            if(rmgr.relation_signature_to_table(sig, tsig)) {
                return rmgr.mk_table_relation(sig, rmgr.get_appropriate_plugin(tsig).mk_full(p, tsig, kind));
            }
            unsigned sz = sig.size();
            tsig.reset();
            for(unsigned i=0; i<sz; i++) {
                table_sort tsort;
                if(rmgr.relation_sort_to_table(sig[i], tsort)) {
                    tsig.push_back(tsort);
                }
            }

            table_plugin & tplugin = rmgr.get_appropriate_plugin(tsig);
            relation_plugin & inner_plugin = rmgr.get_table_relation_plugin(tplugin);

            return sieve_relation_plugin::get_plugin(rmgr).full(p, sig, inner_plugin);
        }

        void init(relation_signature const& r1_sig, unsigned num_rels1, relation_base const* const* r1, 
                  relation_signature const& r2_sig, unsigned num_rels2, relation_base const* const* r2,
                  unsigned col_cnt, unsigned const* cols1, unsigned const* cols2) {
            func_decl* p = 0;
            bit_vector bv;
            bv.resize(num_rels2);
            relation_manager& rmgr = m_plugin.get_manager();
            unsigned_vector r1_tables_indexes;
            unsigned_vector r2_tables_indexes;
            for (unsigned i = 0; i < num_rels1; ++i) {
                if (is_tableish_relation(*r1[i])) {
                    r1_tables_indexes.push_back(i);
                    continue;
                }
                family_id r1_kind = get_nonsieve_kind(*r1[i]);
                bool found = false;
                for (unsigned j = 0; !found && j < num_rels2; ++j) {
                    if (r1_kind == get_nonsieve_kind(*r2[j])) {
                        SASSERT(!bv.get(j));
                        bv.set(j);
                        m_joins.push_back(rmgr.mk_join_fn(*r1[i], *r2[j], col_cnt, cols1, cols2, false)); 
                        SASSERT(m_joins.back());
                        found = true;
                        m_offset1.push_back(i);
                        m_kind1.push_back(T_INPUT);
                        m_offset2.push_back(j);
                        m_kind2.push_back(T_INPUT);
                    }
                }
                if (!found) {
                    relation_plugin & r1_plugin = get_nonsieve_plugin(*r1[i]);
                    relation_base* rel2;
                    if (r1_plugin.can_handle_signature(r2_sig)) {
                        rel2 = r1_plugin.mk_full(p, r2_sig, r1_kind);
                    }
                    else {
                        rel2 = sieve_relation_plugin::get_plugin(rmgr).full(p, r2_sig, r1_plugin);
                    }
                    m_offset1.push_back(i);
                    m_kind1.push_back(T_INPUT);
                    m_offset2.push_back(m_full.size());
                    m_kind2.push_back(T_FULL);
                    m_full.push_back(rel2);
                    m_joins.push_back(rmgr.mk_join_fn(*r1[i], *rel2, col_cnt, cols1, cols2, false));
                    SASSERT(m_joins.back());
                }
            }
            for (unsigned i = 0; i < num_rels2; ++i) {
                if (is_tableish_relation(*r2[i])) {
                    r2_tables_indexes.push_back(i);
                    continue;
                }
                if (!bv.get(i)) {
                    relation_plugin & r2_plugin = get_nonsieve_plugin(*r2[i]);
                    family_id r2_kind = get_nonsieve_kind(*r2[i]);
                    relation_base* rel1;
                    if (r2_plugin.can_handle_signature(r1_sig)) {
                        rel1 = r2_plugin.mk_full(p, r1_sig, r2_kind);
                    }
                    else {
                        rel1 = sieve_relation_plugin::get_plugin(rmgr).full(p, r1_sig, r2_plugin);
                    }
                    m_offset1.push_back(m_full.size());
                    m_kind1.push_back(T_FULL);
                    m_offset2.push_back(i);
                    m_kind2.push_back(T_INPUT);
                    m_full.push_back(rel1);
                    m_joins.push_back(rmgr.mk_join_fn(*rel1, *r2[i], col_cnt, cols1, cols2, false));
                    SASSERT(m_joins.back());
                }
            }

            if (!r1_tables_indexes.empty() && !r2_tables_indexes.empty()) {
                //We may perhaps want to group the table relations by kinds so that tables of the same kind
                //get joined...

                unsigned i1 = r1_tables_indexes.back();
                r1_tables_indexes.pop_back();
                unsigned i2 = r2_tables_indexes.back();
                r2_tables_indexes.pop_back();
                for(;;) {
                    m_offset1.push_back(i1);
                    m_kind1.push_back(T_INPUT);
                    m_offset2.push_back(i2);
                    m_kind2.push_back(T_INPUT);
                    m_joins.push_back(rmgr.mk_join_fn(*r1[i1], *r2[i2], col_cnt, cols1, cols2, false));
                    SASSERT(m_joins.back());

                    if(r1_tables_indexes.empty() && r2_tables_indexes.empty()) {
                        break;
                    }
                    if(!r2_tables_indexes.empty()) {
                        i2 = r2_tables_indexes.back();
                        r2_tables_indexes.pop_back();
                    }
                    if(!r1_tables_indexes.empty()) {
                        i1 = r1_tables_indexes.back();
                        r1_tables_indexes.pop_back();
                    }
                }
            } else if(!r2_tables_indexes.empty()) {
                SASSERT(r1_tables_indexes.empty());

                while(!r2_tables_indexes.empty()) {
                    unsigned r2_idx = r2_tables_indexes.back();
                    r2_tables_indexes.pop_back();
                    unsigned r1_idx = m_full.size();
                    family_id r2_kind = get_nonsieve_kind(*r2[r2_idx]);
                    relation_base * r1_full = get_full_tableish_relation(r1_sig, p, r2_kind);
                    m_full.push_back(r1_full);
                    m_offset1.push_back(r1_idx);
                    m_kind1.push_back(T_FULL);
                    m_offset2.push_back(r2_idx);
                    m_kind2.push_back(T_INPUT);
                    m_joins.push_back(rmgr.mk_join_fn(*r1_full, *r2[r2_idx], col_cnt, cols1, cols2, false));
                    SASSERT(m_joins.back());
                }
            }
            else if(!r1_tables_indexes.empty()) {
                SASSERT(r2_tables_indexes.empty());
                while(!r1_tables_indexes.empty()) {
                    unsigned r1_idx = r1_tables_indexes.back();
                    r1_tables_indexes.pop_back();
                    unsigned r2_idx = m_full.size();
                    family_id r1_kind = get_nonsieve_kind(*r1[r1_idx]);
                    relation_base * r2_full = get_full_tableish_relation(r2_sig, p, r1_kind);
                    m_full.push_back(r2_full);

                    m_offset1.push_back(r1_idx);
                    m_kind1.push_back(T_INPUT);
                    m_offset2.push_back(r2_idx);
                    m_kind2.push_back(T_FULL);
                    m_joins.push_back(rmgr.mk_join_fn(*r1[r1_idx], *r2_full, col_cnt, cols1, cols2, false));
                    SASSERT(m_joins.back());
                }
            }
            SASSERT(m_joins.size()==m_offset1.size());
            SASSERT(m_joins.size()==m_kind1.size());
            SASSERT(m_joins.size()==m_offset2.size());
            SASSERT(m_joins.size()==m_kind2.size());
        }

        relation_base const& access(unsigned idx, relation_base const& r) {
            if (product_relation_plugin::is_product_relation(r)) {
                return get(r)[idx];
            }
            SASSERT(idx == 0);
            return r;
        }

    public:
        join_fn(product_relation_plugin& p, 
                product_relation const& r1, product_relation const& r2, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
            : convenient_relation_join_fn(r1.get_signature(), r2.get_signature(), col_cnt, cols1, cols2),
              m_plugin(p) {
            init(r1.get_signature(), r1.size(), r1.m_relations.c_ptr(), 
                 r2.get_signature(), r2.size(), r2.m_relations.c_ptr(), col_cnt, cols1, cols2);
        }

        join_fn(product_relation_plugin& p, relation_base const& r1, product_relation const& r2, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
            : convenient_relation_join_fn(r1.get_signature(), r2.get_signature(), col_cnt, cols1, cols2),
              m_plugin(p) {
            relation_base const* rels1[1] = { &r1 };
            init(r1.get_signature(), 1, rels1, r2.get_signature(), r2.size(), r2.m_relations.c_ptr(), col_cnt, cols1, cols2);
        }

        join_fn(product_relation_plugin& p, product_relation const& r1, relation_base const& r2, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
            : convenient_relation_join_fn(r1.get_signature(), r2.get_signature(), col_cnt, cols1, cols2),
              m_plugin(p) {
            relation_base const* rels2[1] = { &r2 };
            init(r1.get_signature(), r1.size(), r1.m_relations.c_ptr(), r2.get_signature(), 1, rels2, col_cnt, cols1, cols2);
        }

        join_fn(product_relation_plugin& p, relation_base const& r1, relation_base const& r2, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
            : convenient_relation_join_fn(r1.get_signature(), r2.get_signature(), col_cnt, cols1, cols2),
              m_plugin(p) {
            SASSERT(r1.get_kind() != r2.get_kind());
            relation_base const* rels1[1] = { &r1 };
            relation_base const* rels2[1] = { &r2 };
            init(r1.get_signature(), 1, rels1, r2.get_signature(), 1, rels2, col_cnt, cols1, cols2);
        }

        ~join_fn() { 
            dealloc_ptr_vector_content(m_joins);
            dealloc_ptr_vector_content(m_full);
        }

        virtual relation_base * operator()(const relation_base & _r1, const relation_base & _r2) {
            TRACE("dl", _r1.display(tout); _r2.display(tout););
            ptr_vector<relation_base> relations;
            unsigned sz = m_joins.size();
            relation_base* result = 0;
            for (unsigned i = 0; i < sz; ++i) {
                relation_base const& r1 = (m_kind1[i] == T_FULL)?(*m_full[m_offset1[i]]):access(m_offset1[i], _r1);
                relation_base const& r2 = (m_kind2[i] == T_FULL)?(*m_full[m_offset2[i]]):access(m_offset2[i], _r2);
                relations.push_back((*m_joins[i])(r1, r2));
            }
            result = alloc(product_relation, m_plugin, get_result_signature(), sz, relations.c_ptr());
            TRACE("dl",result->display(tout););
            return result;
        }
    };

    relation_join_fn * product_relation_plugin::mk_join_fn(const relation_base & r1, const relation_base & r2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (is_product_relation(r1) && is_product_relation(r2)) {
            return alloc(join_fn, *this, get(r1), get(r2), col_cnt, cols1, cols2);
        }
        if (is_product_relation(r1)) {
            return alloc(join_fn, *this, get(r1), r2, col_cnt, cols1, cols2);
        }
        if (is_product_relation(r2)) {
            return alloc(join_fn, *this, r1, get(r2), col_cnt, cols1, cols2);
        }
        if (r1.get_kind() != r2.get_kind()) {
            return alloc(join_fn, *this, r1, r2, col_cnt, cols1, cols2);
        }
        return 0;
    }


    class product_relation_plugin::transform_fn : public relation_transformer_fn {
        relation_signature                  m_sig;
        ptr_vector<relation_transformer_fn> m_transforms;
    public:
        transform_fn(relation_signature s, unsigned num_trans, relation_transformer_fn** trans):
          m_sig(s),
          m_transforms(num_trans, trans) {}

          ~transform_fn() { dealloc_ptr_vector_content(m_transforms); }

        virtual relation_base * operator()(const relation_base & _r) {
            product_relation const& r = get(_r);
            product_relation_plugin& p = r.get_plugin();
            SASSERT(m_transforms.size() == r.size());
            ptr_vector<relation_base> relations;
            for (unsigned i = 0; i < r.size(); ++i) {
                relations.push_back((*m_transforms[i])(r[i]));
            }
            relation_base* result = alloc(product_relation, p, m_sig, relations.size(), relations.c_ptr());
            TRACE("dl", _r.display(tout); result->display(tout););
            return result;
        }
    };

    relation_transformer_fn * product_relation_plugin::mk_project_fn(const relation_base & _r, 
            unsigned col_cnt, const unsigned * removed_cols) {
        if (is_product_relation(_r)) {
            product_relation const& r = get(_r);
            ptr_vector<relation_transformer_fn> projs;
            for (unsigned i = 0; i < r.size(); ++i) {
                projs.push_back(get_manager().mk_project_fn(r[i], col_cnt, removed_cols));
            }
            relation_signature s;
            relation_signature::from_project(r.get_signature(), col_cnt, removed_cols, s);
            return alloc(transform_fn, s, projs.size(), projs.c_ptr());
        }
        return 0;
    }
   
    relation_transformer_fn * product_relation_plugin::mk_rename_fn(const relation_base & _r, 
            unsigned cycle_len, const unsigned * permutation_cycle) {
        if(is_product_relation(_r)) {
            ptr_vector<relation_transformer_fn> trans;
            product_relation const& r = get(_r);
            for (unsigned i = 0; i < r.size(); ++i) {                
                trans.push_back(get_manager().mk_rename_fn(r[i], cycle_len, permutation_cycle));
            }
            relation_signature s;
            relation_signature::from_rename(r.get_signature(), cycle_len, permutation_cycle, s);
            return alloc(transform_fn, s, trans.size(), trans.c_ptr());
        }
        return 0;
    }
     
    class product_relation_plugin::aligned_union_fn : public relation_union_fn {
        relation_manager & m_rmgr;
        product_relation_plugin& m_plugin;
        bool m_is_widen;

        //m_union[i][j] is union between i-th and j-th relation.
        //It can be zero which means that particular union should be skipped.
        vector<ptr_vector<relation_union_fn> > m_unions;

        void mk_union_fn(unsigned i, unsigned j, relation_base const& r1, relation_base const& r2,
                const relation_base* delta) {
            relation_manager& rmgr = r1.get_manager();
            relation_union_fn* u = 0;
            if (m_is_widen) {
                u = rmgr.mk_widen_fn(r1, r2, delta);
            }
            else {
                u = rmgr.mk_union_fn(r1, r2, delta);
            }
            TRACE("dl_verbose", tout << r1.get_plugin().get_name() << " " << r2.get_plugin().get_name() << " " << (u?"found":"not found") << "\n";); 
            m_unions.back().push_back(u);
        }

        void init(const relation_vector & tgts, const relation_vector & srcs, const relation_vector * deltas) {
            SASSERT(tgts.size()==srcs.size());
            unsigned num = tgts.size();
            for (unsigned i = 0; i < num; ++i) {
                relation_base& r1 = *tgts[i];
                relation_base* delta = deltas ? (*deltas)[i] : 0;
                m_unions.push_back(ptr_vector<relation_union_fn>());  
                for (unsigned j = 0; j < num; ++j) {
                    relation_base& r2 = *srcs[j];
                    mk_union_fn(i, j, r1, r2, delta);
                }
            }
        }

        bool can_do_inner_union(unsigned tgt_idx, unsigned src_idx) {
            return m_unions[tgt_idx][src_idx] != 0;
        }

        void do_inner_union(unsigned tgt_idx, unsigned src_idx, relation_base& tgt, 
                            relation_base& src, relation_base * delta) {
            SASSERT(m_unions[tgt_idx][src_idx]);
            (*m_unions[tgt_idx][src_idx])(tgt, src, delta);
        }
        
        /**
           If tgt is zero, it is assumed to be a full relation.
        */
        void do_destructive_intersection(scoped_rel<relation_base>& tgt, scoped_rel<relation_base>& src) {
            if(!src) {
                return;
            }
            if(!tgt) {
                tgt=src.release();
                return;
            }
            do_intersection(*tgt, *src);
            src = 0;
        }

        void do_intersection(relation_base& tgt, relation_base& src) {
            scoped_ptr<relation_intersection_filter_fn> intersect_fun = 
                m_rmgr.mk_filter_by_intersection_fn(tgt, src);
            if (!intersect_fun) {
                TRACE("dl", tgt.display(tout << "tgt\n"); src.display(tout << "src\n");); 
                warning_msg("intersection does not exist");
                return;
            }
            (*intersect_fun)(tgt, src);
        }
        void do_delta_union(unsigned rel_idx, relation_base& tgt, relation_base& src) {
            scoped_ptr<relation_union_fn> union_fun = m_rmgr.mk_union_fn(tgt, src);
            SASSERT(union_fun);
            (*union_fun)(tgt, src);
        }
    public:
        aligned_union_fn(
            product_relation const& tgt, 
            product_relation const& src, 
            product_relation const* delta, 
            bool is_widen) :
                m_rmgr(tgt.get_manager()),
                m_plugin(tgt.get_plugin()),
                m_is_widen(is_widen) {
            SASSERT(vectors_equal(tgt.m_spec, src.m_spec));
            SASSERT(!delta || vectors_equal(tgt.m_spec, delta->m_spec));
            init(tgt.m_relations, src.m_relations, delta ? &delta->m_relations : 0);
        }

        ~aligned_union_fn() {
            unsigned sz = m_unions.size();
            for(unsigned i=0; i<sz; i++) {
                dealloc_ptr_vector_content(m_unions[i]);
            }
        }

        virtual void operator()(relation_base& _tgt, const relation_base& _src, relation_base* _delta) {
            TRACE("dl", _tgt.display(tout << "dst:\n"); _src.display(tout  << "src:\n"););
            SASSERT(m_plugin.check_kind(_tgt));
            SASSERT(m_plugin.check_kind(_src));
            SASSERT(!_delta || m_plugin.check_kind(*_delta));
            product_relation& tgt = get(_tgt);
            product_relation const& src = get(_src);
            product_relation* delta = get(_delta);
            SASSERT(tgt.size()==src.size()); //moreover, we want the subrelations of the two relations to be aligned
            unsigned num = tgt.size();
            ptr_vector<relation_base> side_results;
            ptr_vector<relation_base> side_deltas;

            for (unsigned i = 0; i < num; ++i) {
                relation_base& itgt = tgt[i];
                relation_base* idelta = delta ? &(*delta)[i] : 0;

                scoped_rel<relation_base> fresh_delta = idelta ? idelta->get_plugin().mk_empty(*idelta) : 0;
                scoped_rel<relation_base> side_result;
                scoped_rel<relation_base> side_delta;

                //compute the side unions with which we will intersect the result of the basic one
                for (unsigned j = 0; j < num; ++j) {
                    if (i == j) {
                        continue; //this is the basic union which we will perform later
                    }
                    if (can_do_inner_union(i, j) && can_do_inner_union(j, i)) {
                        TRACE("dl", itgt.display(tout << "tgt:\n"); src[j].display(tout << "src:\n"););
                        // union[i][j]
                        scoped_rel<relation_base> one_side_union = itgt.clone();
                        scoped_rel<relation_base> one_side_delta = fresh_delta ? fresh_delta->clone() : 0;
                        TRACE("dl", one_side_union->display(tout << "union 1:\n"); src[j].display(tout););
                        do_inner_union(i, j, *one_side_union, src[j], one_side_delta.get());
                        TRACE("dl", one_side_union->display(tout << "union:\n"););
                        do_destructive_intersection(side_result, one_side_union);                        
                        TRACE("dl", 
                              side_result->display(tout << "inner-union: " << i << " " << j << "\n");
                              itgt.display(tout << "tgt:\n"););
                        if (one_side_delta) {
                            do_destructive_intersection(side_delta, one_side_delta);
                        }

                        // union[j][i]
                        one_side_union = src[i].clone();
                        one_side_delta = fresh_delta ? fresh_delta->clone() : 0;
                        TRACE("dl", one_side_union->display(tout << "union 2:\n"); tgt[j].display(tout););
                        do_inner_union(i, j, *one_side_union, tgt[j], one_side_delta.get());
                        TRACE("dl", one_side_union->display(tout << "union:\n"););
                        do_destructive_intersection(side_result, one_side_union);
                        TRACE("dl", 
                              side_result->display(tout << "inner-union: " << i << " " << j << "\n");
                              itgt.display(tout << "tgt:\n"););
                        if (one_side_delta) {
                            do_destructive_intersection(side_delta, one_side_delta);
                        }
                    }
                }
                side_results.push_back(side_result.release());
                side_deltas.push_back(side_delta.release());
            }
            for (unsigned i = 0; i < num; ++i) {
                relation_base& itgt = tgt[i];
                relation_base* idelta = delta ? &(*delta)[i] : 0;
                scoped_rel<relation_base> fresh_delta = idelta ? idelta->get_plugin().mk_empty(*idelta) : 0;      
                scoped_rel<relation_base> side_result(side_results[i]);
                scoped_rel<relation_base> side_delta(side_deltas[i]);

                // perform the basic union                
                // assume a relation can always perform union with the relation of the same type
                VERIFY(can_do_inner_union(i,i));
                do_inner_union(i, i, itgt, src[i], fresh_delta.get());
                
                if (side_result) {
                    do_intersection(itgt, *side_result);
                    TRACE("dl", side_result->display(tout << "inner-union-end: " << i << "\n"););
                }
                if (fresh_delta) {
                    do_destructive_intersection(fresh_delta,side_delta);
                    SASSERT(idelta);
                    do_delta_union(i, *idelta, *fresh_delta);
                }
            }
            if (num == 0) {
                //we need to handle product relation of no relations separately
                if (!src.m_default_empty && tgt.m_default_empty) {
                    tgt.m_default_empty = false;
                    if (delta) {
                        delta->m_default_empty = false;
                    }
                }
            }
            TRACE("dl", _tgt.display(tout << "dst':\n"); 
                  if (_delta)  _delta->display(tout  << "delta:\n"); ;);
        }
    };

    class product_relation_plugin::unaligned_union_fn : public relation_union_fn {
        bool m_is_widen;
        rel_spec m_common_spec;
        scoped_ptr<relation_union_fn> m_aligned_union_fun;
    public:
        unaligned_union_fn(product_relation const& tgt, product_relation const& src, 
                product_relation const* delta, bool is_widen) : m_is_widen(is_widen) {
            ptr_vector<const product_relation> rels;
            rels.push_back(&tgt);
            rels.push_back(&src);
            if(delta) {
                rels.push_back(delta);
            }
            get_common_spec(rels, m_common_spec);
        }


        virtual void operator()(relation_base& _tgt, const relation_base& _src, relation_base* _delta) {
            TRACE("dl_verbose", _tgt.display(tout << "dst:\n"); _src.display(tout  << "src:\n"););
            product_relation& tgt = get(_tgt);
            product_relation const& src0 = get(_src);
            product_relation* delta = _delta ? get(_delta) : 0;

            tgt.convert_spec(m_common_spec);
            if(delta) {
                delta->convert_spec(m_common_spec);
            }
            scoped_rel<product_relation> src_scoped;
            if(src0.get_kind()!=tgt.get_kind()) {
                src_scoped = src0.clone();
                src_scoped->convert_spec(m_common_spec);
            }
            product_relation const& src = src_scoped ? *src_scoped : src0;

            if(!m_aligned_union_fun) {
                m_aligned_union_fun = alloc(aligned_union_fn, tgt, src, delta, m_is_widen);
                SASSERT(m_aligned_union_fun);
            }
            (*m_aligned_union_fun)(tgt, src, delta);
            TRACE("dl", _tgt.display(tout << "dst':\n"); 
                        if (_delta) _delta->display(tout  << "delta:\n"););
        }
    };

    class product_relation_plugin::single_non_transparent_src_union_fn : public relation_union_fn {
        unsigned m_single_rel_idx;
        scoped_ptr<relation_union_fn> m_inner_union_fun;
    public:
        single_non_transparent_src_union_fn(unsigned single_rel_idx, relation_union_fn* inner_union_fun) 
                : m_single_rel_idx(single_rel_idx),
                m_inner_union_fun(inner_union_fun) {}

        virtual void operator()(relation_base& tgt, const relation_base& _src, relation_base* delta) {
            TRACE("dl", tgt.display(tout); _src.display(tout); );
            product_relation const& src = get(_src);
            (*m_inner_union_fun)(tgt, src[m_single_rel_idx], delta);
        }
    };

    relation_union_fn * product_relation_plugin::mk_union_w_fn(const relation_base & tgt, const relation_base & src,
        const relation_base * delta, bool is_widen) {
        if (check_kind(tgt) && check_kind(src) && (!delta || check_kind(*delta))) {
            if(are_aligned(get(tgt), get(src)) && (!delta || are_aligned(get(tgt), *get(delta)))) {
                return alloc(aligned_union_fn, get(tgt), get(src), get(delta), is_widen);
            }
            return alloc(unaligned_union_fn, get(tgt), get(src), get(delta), is_widen);
        }
        if (check_kind(src)) {
            TRACE("dl", tgt.display(tout << "different kinds"); src.display(tout););
            const product_relation & p_src = get(src);
            unsigned single_idx;
            if(p_src.try_get_single_non_transparent(single_idx)) {
                relation_union_fn * inner;
                if(is_widen) {
                    inner = get_manager().mk_widen_fn(tgt, p_src[single_idx], delta);
                }
                else {
                    inner = get_manager().mk_union_fn(tgt, p_src[single_idx], delta);
                }
                if (inner) {
                    return alloc(single_non_transparent_src_union_fn, single_idx, inner);
                }
            }
        }
        return 0;
    }

    relation_union_fn * product_relation_plugin::mk_union_fn(const relation_base & tgt, const relation_base & src,
        const relation_base * delta) {
        return mk_union_w_fn(tgt, src, delta, false);
    }

    relation_union_fn * product_relation_plugin::mk_widen_fn(
        const relation_base & tgt, const relation_base & src, const relation_base * delta) {
        return mk_union_w_fn(tgt, src, delta, true);
    }

    class product_relation_plugin::mutator_fn : public relation_mutator_fn {
        ptr_vector<relation_mutator_fn> m_mutators;
    public:
        mutator_fn(unsigned sz, relation_mutator_fn** muts):
          m_mutators(sz, muts) {}

       ~mutator_fn() { dealloc_ptr_vector_content(m_mutators); }

        virtual void operator()(relation_base & _r) {
            TRACE("dl", _r.display(tout););
            product_relation& r = get(_r);
            SASSERT(m_mutators.size() == r.size());
            for (unsigned i = 0; i < r.size(); ++i) {
                relation_mutator_fn* m = m_mutators[i];
                if (m) {
                    (*m)(r[i]);
                }
            }
            TRACE("dl", _r.display(tout););
        }
    };


    relation_mutator_fn * product_relation_plugin::mk_filter_identical_fn(
        const relation_base & _t, unsigned col_cnt, const unsigned * identical_cols) {
        
        if(is_product_relation(_t)) {
            bool found = false;
            product_relation const& r = get(_t);
            ptr_vector<relation_mutator_fn> mutators;
            for (unsigned i = 0; i < r.size(); ++i) {
                relation_mutator_fn* m = get_manager().mk_filter_identical_fn(r[i], col_cnt, identical_cols);
                mutators.push_back(m);
                if (m) found = true;
            }
            if (found) {
                return alloc(mutator_fn, mutators.size(), mutators.c_ptr());
            }
        }
        return 0;
    }

    relation_mutator_fn * product_relation_plugin::mk_filter_equal_fn(const relation_base & _t, 
        const relation_element & value, unsigned col) {
        if(is_product_relation(_t)) {
            product_relation const& r = get(_t);
            ptr_vector<relation_mutator_fn> mutators;
            bool found = false;
            for (unsigned i = 0; i < r.size(); ++i) {
                relation_mutator_fn* m = get_manager().mk_filter_equal_fn(r[i], value, col);
                mutators.push_back(m);  
                if (m) found = true;
            }
            if (found) {
                return alloc(mutator_fn, mutators.size(), mutators.c_ptr());
            }
        }
        return 0;
    }

    class product_relation_plugin::filter_interpreted_fn : public relation_mutator_fn {
        ptr_vector<relation_mutator_fn> m_mutators;
        svector<std::pair<unsigned, unsigned> > m_attach;
    public:

        filter_interpreted_fn(product_relation const& r, app* cond) {            
            for (unsigned i = 0; i < r.size(); ++i) {
                m_mutators.push_back(r.get_manager().mk_filter_interpreted_fn(r[i], cond));
            }
            for (unsigned i = 0; i < r.size(); ++i) {
                relation_mutator_fn& m1 = *(m_mutators[i]);
                for (unsigned j = i + 1; j < r.size(); ++j) {
                    relation_mutator_fn& m2 = *(m_mutators[j]);  
                    if (m1.supports_attachment(r[j])) {
                        m_attach.push_back(std::make_pair(i,j));
                    }
                    if (m2.supports_attachment(r[i])) {
                        m_attach.push_back(std::make_pair(j,i));
                    }
                }
            }
        }

        ~filter_interpreted_fn() { dealloc_ptr_vector_content(m_mutators); }

        void operator()(relation_base& _r) {
            TRACE("dl", _r.display(tout););
            product_relation const& r = get(_r);
            for (unsigned i = 0; i < m_attach.size(); ++i) {
                m_mutators[m_attach[i].first]->attach(r[m_attach[i].second]);
            }
            for (unsigned i = 0; i < m_mutators.size(); ++i) {
                (*m_mutators[i])(r[i]);
            }
            TRACE("dl", _r.display(tout););
        }      
    };

    relation_mutator_fn * product_relation_plugin::mk_filter_interpreted_fn(const relation_base & t, app * condition) {
        return alloc(filter_interpreted_fn, get(t), condition);
    }      


    // -----------------------------------
    //
    // product_relation
    //
    // -----------------------------------

    product_relation::product_relation(product_relation_plugin& p, relation_signature const& s):
        relation_base(p, s), 
        m_default_empty(true) {
        ensure_correct_kind();
    }

    product_relation::product_relation(product_relation_plugin& p, relation_signature const& s, unsigned num_relations, relation_base** relations) :
        relation_base(p, s),
        m_default_empty(true) {
        for (unsigned i = 0; i < num_relations; ++i) {
            SASSERT(relations[i]->get_signature()==s);
            m_relations.push_back(relations[i]);
        }
        ensure_correct_kind();
    }

    product_relation::~product_relation() {
        unsigned num_relations = m_relations.size();
        for (unsigned i = 0; i < num_relations; ++i) {
            m_relations[i]->deallocate();
        }
    }

    product_relation_plugin& product_relation::get_plugin() const {
        return dynamic_cast<product_relation_plugin&>(relation_base::get_plugin());
    }        

    void product_relation::ensure_correct_kind() {
        unsigned rel_cnt = m_relations.size();
        //the rel_cnt==0 part makes us to update the kind also when the relation is newly created
        bool spec_changed = rel_cnt != m_spec.size() || rel_cnt==0;
        if (spec_changed) {
            m_spec.resize(rel_cnt);
        }
        for (unsigned i = 0; i < rel_cnt; i++) {
            family_id rkind = m_relations[i]->get_kind();
            spec_changed |= (m_spec[i] != rkind);
            m_spec[i] = rkind;
        }
        if (spec_changed) {
            set_kind(get_plugin().get_relation_kind(*this));
        }
    }

    void product_relation::convert_spec(const rel_spec & spec) {

        func_decl* p = 0;
        const relation_signature & sig = get_signature();
        family_id new_kind = get_plugin().get_relation_kind(sig, spec);
        if (new_kind == get_kind()) {
            return;
        }

        TRACE("dl", {
                ast_manager& m = get_ast_manager_from_rel_manager(get_manager());
                sig.output(m, tout); tout << "\n";
                for (unsigned i = 0; i < spec.size(); ++i) {
                    tout << spec[i] << " ";
                }
                tout << "\n";
            }
            );

        unsigned old_sz = size();
        unsigned new_sz = spec.size();
        unsigned old_remain = old_sz;
        relation_vector new_rels;

        //the loop is quadratic with the number of relations, maybe we want to fix it
        for(unsigned i=0; i<new_sz; i++) {
            family_id ikind = spec[i];
            relation_base * irel = 0;
            //we try to find the relation for the new specification among those we already have
            for(unsigned j=0; j<old_sz; j++) {
                if(m_relations[j] && m_relations[j]->get_kind()==ikind) {
                    irel = m_relations[j];
                    m_relations[j] = 0;
                    old_remain--;
                    break;
                }
            }
            if(!irel) {
                if(old_sz == 0 && m_default_empty) {
                    //The relation didn't contain any inner relations but it was empty,
                    //so we make the newly added relations empty as well.
                    irel = get_manager().mk_empty_relation(sig, ikind);
                }
                else {
                    irel = get_manager().mk_full_relation(sig, p, ikind);
                }
            }
            new_rels.push_back(irel);
        }
        SASSERT(old_remain==0); //the new specification must be a superset of the old one
        m_relations = new_rels;

        set_kind(new_kind);
        m_spec = spec;
        SASSERT(get_kind() == new_kind);        
    }

    bool product_relation::try_get_single_non_transparent(unsigned & idx) const {
        unsigned sz = size();
        bool found = false;
        unsigned candidate;
        for(unsigned i=0; i<sz; i++) {
            relation_base & r = (*this)[i];
            if(r.get_plugin().is_sieve_relation()) {
                sieve_relation & sr = sieve_relation_plugin::get(r);
                if(sr.no_inner_columns()) {
                    continue;
                }
            }
            if(found) {
                return false; //we have more than one non-transparent
            }
            found = true;
            candidate = i;
        }
        if(found) {
            idx = candidate;
            return true;
        }
        return false; //there is no non-transparent
    }



    void product_relation::add_fact(const relation_fact & f) {  
        for (unsigned i = 0; i < size(); ++i) {
            (*this)[i].add_fact(f);
        }
    }

    bool product_relation::contains_fact(const relation_fact & f) const {
        for (unsigned i = 0; i < size(); ++i) {
            if (!(*this)[i].contains_fact(f)) {
                return false;
            }
        }
        return true;
    }

    product_relation * product_relation::clone() const {
        ptr_vector<relation_base> relations;
        for (unsigned i = 0; i < size(); ++i) {
            relations.push_back((*this)[i].clone());
        }
        product_relation_plugin& p = get_plugin();
        return alloc(product_relation, p, get_signature(), relations.size(), relations.c_ptr());
    }

    product_relation * product_relation::complement(func_decl*) const {
        if(m_relations.empty()) {
            product_relation * res = clone();
            res->m_default_empty = !m_default_empty;
            return res;
        }
        UNREACHABLE();
        return 0;
    }

    bool product_relation::empty() const {
        if(m_relations.empty()) {
            return m_default_empty;
        }
        for (unsigned i = 0; i < m_relations.size(); ++i) {
            if (m_relations[i]->empty()) {
                return true;
            }
        }
        return false;
    }

    void product_relation::to_formula(expr_ref& fml) const {
        ast_manager& m = fml.get_manager();
        expr_ref_vector conjs(m);
        expr_ref tmp(m);
        for (unsigned i = 0; i < m_relations.size(); ++i) {
            m_relations[i]->to_formula(tmp);
            conjs.push_back(tmp);
        }
        bool_rewriter(m).mk_and(conjs.size(), conjs.c_ptr(), fml);
    }

    void product_relation::display(std::ostream & out) const {
        if (m_relations.empty()) {
            out << "{}\n";
            return;
        }
        out << "Product of the following relations:\n";
        for (unsigned i = 0; i < m_relations.size(); ++i) {
            m_relations[i]->display(out);
        }
    }

};



