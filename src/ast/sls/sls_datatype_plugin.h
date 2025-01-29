/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_datatype_plugin.h

Abstract:

    Algebraic Datatypes for SLS
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-14
    
--*/
#pragma once

#include "ast/sls/sls_context.h"
#include "ast/datatype_decl_plugin.h"
#include "util/top_sort.h"

namespace sls {

    class euf_plugin;
    
    class datatype_plugin : public plugin {
        struct stats {
            unsigned m_num_occurs = 0;
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        struct parent_t {
            expr*        parent;
            expr_ref     condition; 
        };
        euf_plugin& euf;
        scoped_ptr<euf::egraph>& g;
        obj_map<sort, ptr_vector<expr>> m_dts;
        obj_map<expr, vector<parent_t>> m_parents;
        
        bool m_axiomatic_mode = true;
        mutable datatype_util dt;
        expr_ref_vector m_axioms, m_values, m_eval;
        model_ref m_model;
        stats m_stats;

        void collect_path_axioms();
        void add_edge(expr* child, expr* parent, expr* cond);
        void add_path_axioms();
        void add_path_axioms(ptr_vector<expr>& children, sat::literal_vector& lits, vector<parent_t> const& parents);
        void add_axioms();
        
        void init_values();
        void add_dep(euf::enode* n, top_sort<euf::enode>& dep);

        euf::enode* get_constructor(euf::enode* n) const;

        // f -> v_t -> val 
        // e = A(t)
        // val(t) <- val
        // 
        typedef obj_hashtable<expr> expr_set;
        obj_map<func_decl, obj_map<expr, expr*>> m_eval_accessor;
        obj_map<func_decl, expr_set> m_occurs;
        expr_ref eval1(expr* e);
        expr_ref eval0(euf::enode* n);
        expr_ref eval0(expr* n);
        expr_ref eval0rec(expr* n);
        expr_ref eval_accessor(func_decl* f, expr* t);
        void update_eval_accessor(app* e, expr* t, expr* value);
        void del_eval_accessor();
        void set_eval0(expr* e, expr* val);

        void repair_down_constructor(app* e, expr* v0, expr* v1);
        void repair_down_accessor(app* e, expr* t, expr* v1);
        void repair_down_recognizer(app* e, expr* t);
        void repair_down_eq(app* e, expr* s, expr* t);
        void repair_down_distinct(app* e);
        void repair_up_accessor(app* e, expr* t, expr* v0);
        void propagate_literal_model_building(sat::literal lit);

    public:
        datatype_plugin(context& c);
        ~datatype_plugin() override;
        family_id fid() override { return m_fid; }
        expr_ref get_value(expr* e) override;
        void initialize() override;
        void start_propagation() override;
        void propagate_literal(sat::literal lit) override;
        bool propagate() override;       
        bool is_sat() override;
        void register_term(expr* e) override;

        bool set_value(expr* e, expr* v) override { return false; }
        void repair_literal(sat::literal lit) override {}
        bool include_func_interp(func_decl* f) const override;
        bool check_ackerman(func_decl* f) const override;

        bool repair_down(app* e) override;
        void repair_up(app* e) override;

        std::ostream& display(std::ostream& out) const override;
        void collect_statistics(statistics& st) const override;
        void reset_statistics() override;
        
    };
    
}
