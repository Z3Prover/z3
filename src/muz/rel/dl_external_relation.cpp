/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_external_relation.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2010-05-10

Revision History:

--*/

#include "util/debug.h"
#include "ast/ast_pp.h"
#include "muz/base/dl_context.h"
#include "muz/rel/dl_external_relation.h"
#include "ast/dl_decl_plugin.h"

namespace datalog {
       
    external_relation::external_relation(external_relation_plugin & p, const relation_signature & s, expr* r) 
        : relation_base(p, s),
          m_rel(r, p.get_ast_manager()),
          m_select_fn(p.get_ast_manager()),
          m_store_fn(p.get_ast_manager()),
          m_is_empty_fn(p.get_ast_manager())
    {
    }

    external_relation::~external_relation() {
    }

    void external_relation::mk_accessor(decl_kind k, func_decl_ref& fn, const relation_fact& f, bool destructive, expr_ref& res) const {
        ast_manager& m = m_rel.get_manager();
        family_id fid = get_plugin().get_family_id();
        ptr_vector<expr> args;
        args.push_back(m_rel);
        for (unsigned i = 0; i < f.size(); ++i) {
            args.push_back(f[i]);
        }
        if (!fn.get()) {
           fn = m.mk_func_decl(fid, k, 0, nullptr, args.size(), args.data());
        }        
        if (destructive) {
            get_plugin().reduce_assign(fn, args.size(), args.data(), 1, args.data());
            res = m_rel;
        }
        else {
            get_plugin().reduce(fn, args.size(), args.data(), res);
        }
    }

    bool external_relation::empty() const {
        ast_manager& m = m_rel.get_manager();
        expr* r = m_rel.get();
        expr_ref res(m);
        if (!m_is_empty_fn.get()) {
            family_id fid = get_plugin().get_family_id();
            const_cast<func_decl_ref&>(m_is_empty_fn) = m.mk_func_decl(fid, OP_RA_IS_EMPTY, 0, nullptr, 1, &r);
        }
        get_plugin().reduce(m_is_empty_fn, 1, &r, res);
        return m.is_true(res);
    }
    
    void external_relation::add_fact(const relation_fact & f) {
        mk_accessor(OP_RA_STORE, m_store_fn, f, true, m_rel);
    }
    
    bool external_relation::contains_fact(const relation_fact & f) const {
        ast_manager& m = get_plugin().get_ast_manager();
        expr_ref res(m);
        mk_accessor(OP_RA_SELECT, const_cast<func_decl_ref&>(m_select_fn), f, false, res);
        return !m.is_false(res);
    }
    
    external_relation * external_relation::clone() const {
        ast_manager& m = m_rel.get_manager();
        family_id fid = get_plugin().get_family_id();
        expr* rel = m_rel.get();
        expr_ref res(m.mk_fresh_const("T", rel->get_sort()), m);
        expr* rel_out = res.get();
        func_decl_ref fn(m.mk_func_decl(fid, OP_RA_CLONE,0,nullptr, 1, &rel), m);
        get_plugin().reduce_assign(fn, 1, &rel, 1, &rel_out);
        return alloc(external_relation, get_plugin(), get_signature(), res);
    }

    external_relation * external_relation::complement(func_decl* p) const {
        ast_manager& m = m_rel.get_manager();
        family_id fid = get_plugin().get_family_id();
        expr_ref res(m);
        expr* rel = m_rel;
        func_decl_ref fn(m.mk_func_decl(fid, OP_RA_COMPLEMENT,0,nullptr, 1, &rel), m);
        get_plugin().reduce(fn, 1, &rel, res);
        return alloc(external_relation, get_plugin(), get_signature(), res);
    }
            
    void external_relation::display(std::ostream & out) const {
        out << mk_pp(m_rel, m_rel.get_manager()) << "\n";
    }
    
    void external_relation::display_tuples(func_decl & pred, std::ostream & out) const {
        display(out);
    }


    external_relation_plugin & external_relation::get_plugin() const {
        return static_cast<external_relation_plugin &>(relation_base::get_plugin());
    }


    // -----------------------------------
    //
    // external_relation_plugin
    //
    // -----------------------------------


    external_relation_plugin::external_relation_plugin(external_relation_context& ctx, relation_manager & m) 
        : relation_plugin(external_relation_plugin::get_name(), m), m_ext(ctx) {}

    external_relation const & external_relation_plugin::get(relation_base const& r) {
        return dynamic_cast<external_relation const&>(r);
    }

    external_relation & external_relation_plugin::get(relation_base & r) { 
        return dynamic_cast<external_relation&>(r);
    }

    relation_base * external_relation_plugin::mk_empty(const relation_signature & s) {
        ast_manager& m = get_ast_manager();        
        sort* r_sort = get_relation_sort(s);
        parameter param(r_sort);
        family_id fid = get_family_id();
        expr_ref e(m.mk_fresh_const("T", r_sort), m);
        expr* args[1] = { e.get() };
        func_decl_ref empty_decl(m.mk_func_decl(fid, OP_RA_EMPTY, 1, &param, 0, (sort*const*)nullptr), m);
        reduce_assign(empty_decl, 0, nullptr, 1, args);
        return alloc(external_relation, *this, s, e);
    }
    
    sort* external_relation_plugin::get_relation_sort(relation_signature const& sig) {
        vector<parameter> sorts;
        ast_manager& m = get_ast_manager();
        family_id fid = get_family_id();
        for (unsigned i = 0; i < sig.size(); ++i) {
            sorts.push_back(parameter(sig[i]));
        }
        return m.mk_sort(fid, DL_RELATION_SORT, sorts.size(), sorts.data());
    }
    
    sort* external_relation_plugin::get_column_sort(unsigned col, sort* s) {
        SASSERT(s->get_num_parameters() > col);
        SASSERT(s->get_parameter(col).is_ast());
        SASSERT(is_sort(s->get_parameter(col).get_ast()));
        return to_sort(s->get_parameter(col).get_ast());
    }
            
    family_id external_relation_plugin::get_family_id() {
        return m_ext.get_family_id();
    }


    void external_relation_plugin::mk_filter_fn(sort* s, app* condition, func_decl_ref& f) {
        ast_manager& m = get_ast_manager();
        family_id fid  = get_family_id();
        parameter param(condition);
        f = m.mk_func_decl(fid, OP_RA_FILTER, 1, &param, 1, &s);
    }

    class external_relation_plugin::join_fn : public convenient_relation_join_fn {
        external_relation_plugin& m_plugin;
        func_decl_ref             m_join_fn;
        expr*                     m_args[2];
    public:
        join_fn(external_relation_plugin& p, const relation_signature & o1_sig, const relation_signature & o2_sig, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
            : convenient_relation_join_fn(o1_sig, o2_sig, col_cnt, cols1, cols2),
              m_plugin(p),
              m_join_fn(p.get_ast_manager()) {
                  ast_manager& m = p.get_ast_manager();
                  family_id fid = p.get_family_id();
            vector<parameter> params;
            for (unsigned i = 0; i < col_cnt; ++i) {
                params.push_back(parameter(cols1[i]));
                params.push_back(parameter(cols2[i]));
            }
            sort* domain[2] = { p.get_relation_sort(o1_sig), p.get_relation_sort(o2_sig) };
            m_join_fn = m.mk_func_decl(fid, OP_RA_JOIN, params.size(), params.data(), 2, domain);
        }

        relation_base * operator()(const relation_base & r1, const relation_base & r2) override {
            expr_ref res(m_plugin.get_ast_manager());
            m_args[0] = get(r1).get_relation();
            m_args[1] = get(r2).get_relation();
            m_plugin.reduce(m_join_fn, 2, m_args, res); 
            return alloc(external_relation, m_plugin, get_result_signature(), res);
        }
    };

    relation_join_fn * external_relation_plugin::mk_join_fn(const relation_base & r1, const relation_base & r2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
        if (!check_kind(r1) || !check_kind(r2)) {
            return nullptr;
        }
        return alloc(join_fn, *this, r1.get_signature(), r2.get_signature() , col_cnt, cols1, cols2);
    }


    class external_relation_plugin::project_fn : public convenient_relation_project_fn {
        external_relation_plugin& m_plugin;
        func_decl_ref             m_project_fn;
    public:
        project_fn(external_relation_plugin& p, sort* relation_sort, 
                   const relation_signature & orig_sig, unsigned removed_col_cnt, const unsigned * removed_cols) 
            : convenient_relation_project_fn(orig_sig, removed_col_cnt, removed_cols),
              m_plugin(p),
              m_project_fn(p.get_ast_manager()) {
            vector<parameter> params;
            ast_manager& m = p.get_ast_manager();
            family_id fid = p.get_family_id();
            for (unsigned i = 0; i < removed_col_cnt; ++i) {
                params.push_back(parameter(removed_cols[i]));
            }            
            m_project_fn = m.mk_func_decl(fid, OP_RA_PROJECT, params.size(), params.data(), 1, &relation_sort);
        }

        relation_base * operator()(const relation_base & r) override {
            expr_ref res(m_plugin.get_ast_manager());
            expr* rel = get(r).get_relation();
            m_plugin.reduce(m_project_fn, 1, &rel, res); 
            return alloc(external_relation, m_plugin, get_result_signature(), to_app(res));
        }
    };

    relation_transformer_fn * external_relation_plugin::mk_project_fn(const relation_base & r, 
            unsigned col_cnt, const unsigned * removed_cols) {
        return alloc(project_fn, *this, get(r).get_sort(), r.get_signature(), col_cnt, removed_cols);
    }


    class external_relation_plugin::rename_fn : public convenient_relation_rename_fn {
        external_relation_plugin& m_plugin;
        func_decl_ref             m_rename_fn;    
        expr*                     m_args[2];
    public:
        rename_fn(external_relation_plugin& p, sort* relation_sort, const relation_signature & orig_sig, unsigned cycle_len, const unsigned * cycle) 
            : convenient_relation_rename_fn(orig_sig, cycle_len, cycle),
              m_plugin(p),
              m_rename_fn(p.get_ast_manager()) {

            ast_manager& m = p.get_ast_manager();
            family_id fid  = p.get_family_id();
            vector<parameter> params;
            for (unsigned i = 0; i < cycle_len; ++i) {
                SASSERT(cycle[i] < orig_sig.size());
                params.push_back(parameter(cycle[i]));
            }
            m_rename_fn = m.mk_func_decl(fid, OP_RA_RENAME, params.size(), params.data(), 1, &relation_sort);
        }

        relation_base * operator()(const relation_base & r) override {
            expr* rel = get(r).get_relation();
            expr_ref res(m_plugin.get_ast_manager());
            m_args[0] = rel;
            m_plugin.reduce(m_rename_fn, 1, &rel, res); 
            return alloc(external_relation, m_plugin, get_result_signature(), res);
        }
    };

    relation_transformer_fn * external_relation_plugin::mk_rename_fn(const relation_base & r, 
            unsigned cycle_len, const unsigned * permutation_cycle) {
        if(!check_kind(r)) {
            return nullptr;
        }
        return alloc(rename_fn, *this, get(r).get_sort(), r.get_signature(), cycle_len, permutation_cycle);
    }


    class external_relation_plugin::union_fn : public relation_union_fn {
        external_relation_plugin& m_plugin;
        func_decl_ref             m_union_fn;        
        expr*                     m_args[2];
        expr*                     m_outs[2];
        
    public:
        union_fn(external_relation_plugin& p, decl_kind k, sort* relation_sort):
            m_plugin(p),
            m_union_fn(p.get_ast_manager()) {            
            ast_manager& m = p.get_ast_manager();
            sort* domain[2] = { relation_sort, relation_sort };
            m_union_fn = m.mk_func_decl(p.get_family_id(), k, 0, nullptr, 2, domain);
        }

        void operator()(relation_base & r, const relation_base & src, relation_base * delta) override {
            ast_manager& m = m_plugin.get_ast_manager();
            expr_ref_vector res(m);
            m_args[0] = get(r).get_relation();
            m_args[1] = get(src).get_relation();
            m_outs[0] = m_args[0];
            unsigned num_out = 1;
            if (delta) {
                m_outs[1] = get(*delta).get_relation();
                ++num_out;
            }
            m_plugin.reduce_assign(m_union_fn, 2, m_args, num_out, m_outs);
        }
    };

    relation_union_fn * external_relation_plugin::mk_union_fn(const relation_base & tgt, const relation_base & src,
        const relation_base * delta) {
        if (!check_kind(tgt) || !check_kind(src) || (delta && !check_kind(*delta))) {
            return nullptr;
        }
        return alloc(union_fn, *this, OP_RA_UNION, get(src).get_sort());
    }

    relation_union_fn * external_relation_plugin::mk_widen_fn(const relation_base & tgt, const relation_base & src,
        const relation_base * delta) {
        if (!check_kind(tgt) || !check_kind(src) || (delta && !check_kind(*delta))) {
            return nullptr;
        }
        return alloc(union_fn, *this, OP_RA_WIDEN, get(src).get_sort());
    }

    class external_relation_plugin::filter_interpreted_fn : public relation_mutator_fn {
        external_relation_plugin& m_plugin;
        app_ref                 m_condition;
        func_decl_ref           m_filter_fn;
    public:
        filter_interpreted_fn(external_relation_plugin& p, sort* relation_sort, app * condition) 
            : m_plugin(p),
              m_condition(condition, p.get_ast_manager()),
              m_filter_fn(p.get_ast_manager()) {
            p.mk_filter_fn(relation_sort, condition, m_filter_fn);
            SASSERT(p.get_ast_manager().is_bool(condition));
        }

        void operator()(relation_base & r) override {
            SASSERT(m_plugin.check_kind(r));
            expr* arg = get(r).get_relation();
            m_plugin.reduce_assign(m_filter_fn, 1, &arg, 1, &arg);
        }
    };

    relation_mutator_fn * external_relation_plugin::mk_filter_interpreted_fn(const relation_base & r, app * condition) {
        if(!check_kind(r)) {
            return nullptr;
        }
        return alloc(filter_interpreted_fn, *this, get(r).get_sort(), condition);
    }

    relation_mutator_fn * external_relation_plugin::mk_filter_equal_fn(const relation_base & r, 
        const relation_element & value, unsigned col) {
        if(!check_kind(r)) {
            return nullptr;
        }
        ast_manager& m = get_ast_manager();
        app_ref condition(m);
        expr_ref var(m);
        sort* relation_sort = get(r).get_sort();
        sort* column_sort = get_column_sort(col, relation_sort);
        var = m.mk_var(col, column_sort);
        condition = m.mk_eq(var, value);
        return mk_filter_interpreted_fn(r, condition);
    }

    class external_relation_plugin::filter_identical_fn : public relation_mutator_fn {
        external_relation_plugin& m_plugin;
        func_decl_ref_vector      m_filter_fn;
    public:
        filter_identical_fn(external_relation_plugin& p, sort* relation_sort, 
                            unsigned col_cnt, const unsigned * identical_cols) 
            : m_plugin(p), m_filter_fn(p.get_ast_manager()) {
            ast_manager& m = p.get_ast_manager();
            func_decl_ref fn(m);
            app_ref eq(m);
            if (col_cnt <= 1) {
                return;
            }
            unsigned col = identical_cols[0];
            sort* s = p.get_column_sort(col, relation_sort);
            var* v0 = m.mk_var(col, s);
            for (unsigned i = 1; i < col_cnt; ++i) {
                col = identical_cols[i];
                s = p.get_column_sort(col, relation_sort);                                            
                eq = m.mk_eq(v0, m.mk_var(col, s));
                p.mk_filter_fn(relation_sort, eq.get(), fn);
                m_filter_fn.push_back(fn);
            }
        }

        void operator()(relation_base & r) override {
            expr* r0 = get(r).get_relation();
            for (unsigned i = 0; i < m_filter_fn.size(); ++i) {
                m_plugin.reduce_assign(m_filter_fn[i].get(), 1, &r0, 1, &r0);                  
            }
        }
    };

    relation_mutator_fn * external_relation_plugin::mk_filter_identical_fn(const relation_base & r, 
        unsigned col_cnt, const unsigned * identical_cols) {
        if (!check_kind(r)) {
            return nullptr;
        }
        return alloc(filter_identical_fn, *this, get(r).get_sort(), col_cnt, identical_cols);
    }


    class external_relation_plugin::negation_filter_fn : public convenient_relation_negation_filter_fn {
        external_relation_plugin& m_plugin;
        func_decl_ref m_negated_filter_fn;
        expr* m_args[2];
    public:
        negation_filter_fn(external_relation_plugin& p, 
                           const relation_base & tgt, const relation_base & neg_t, 
                           unsigned joined_col_cnt, const unsigned * t_cols, const unsigned * negated_cols) : 
            convenient_negation_filter_fn(tgt, neg_t, joined_col_cnt, t_cols, negated_cols),
            m_plugin(p),
            m_negated_filter_fn(p.get_ast_manager()) 
        {
            ast_manager& m = p.get_ast_manager();
            family_id fid  = p.get_family_id();
            vector<parameter> params;
            for (unsigned i = 0; i < joined_col_cnt; ++i) {
                params.push_back(parameter(t_cols[i]));
                params.push_back(parameter(negated_cols[i]));
            }
            sort* domain[2] = { get(tgt).get_sort(), get(neg_t).get_sort() };
            m_negated_filter_fn = m.mk_func_decl(fid, OP_RA_NEGATION_FILTER, params.size(), params.data(), 2, domain);            
        }

        void operator()(relation_base & t, const relation_base & negated_obj) override {
            m_args[0] = get(t).get_relation();
            m_args[1] = get(negated_obj).get_relation();
            m_plugin.reduce_assign(m_negated_filter_fn.get(), 2, m_args, 1, m_args);                       
        }
    };

    relation_intersection_filter_fn * external_relation_plugin::mk_filter_by_negation_fn(const relation_base & t, 
            const relation_base & negated_obj, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * negated_cols) {
        if (!check_kind(t) || !check_kind(negated_obj)) {
            return nullptr;
        }
        return alloc(negation_filter_fn, *this, t, negated_obj, joined_col_cnt, t_cols, negated_cols);
    }

};
