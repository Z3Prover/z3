/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    elim_unconstrained.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

--*/


#pragma once

#include "util/heap.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/converters/expr_inverter.h"


class elim_unconstrained : public dependent_expr_simplifier {

    struct node {
        unsigned         m_refcount = 0;
        expr*            m_term = nullptr;
        expr*            m_orig = nullptr;
        ptr_vector<expr> m_parents;
    };
    struct var_lt {
        elim_unconstrained& s;
        var_lt(elim_unconstrained& s) : s(s) {}
        bool operator()(int v1, int v2) const {
            return s.is_var_lt(v1, v2);
        }
    };
    struct stats {
        unsigned m_num_eliminated = 0;
        void reset() { m_num_eliminated = 0; }
    };
    expr_inverter            m_inverter;
    vector<node>             m_nodes;
    var_lt                   m_lt;
    heap<var_lt>             m_heap;
    expr_ref_vector          m_trail;
    ptr_vector<expr>         m_args;
    expr_mark                m_frozen;
    stats                    m_stats;
    unsigned_vector          m_root;

    bool is_var_lt(int v1, int v2) const;
    node& get_node(unsigned n) { return m_nodes[n]; }
    node const& get_node(unsigned n) const { return m_nodes[n]; }
    node& get_node(expr* t) { return m_nodes[root(t)]; }
    unsigned root(expr* t) const { return m_root[t->get_id()]; }
    node const& get_node(expr* t) const { return m_nodes[root(t)]; }
    unsigned get_refcount(expr* t) const { return get_node(t).m_refcount; }
    void inc_ref(expr* t) { ++get_node(t).m_refcount; if (is_uninterp_const(t)) m_heap.increased(root(t)); }
    void dec_ref(expr* t) { --get_node(t).m_refcount; if (is_uninterp_const(t)) m_heap.decreased(root(t)); }
    void gc(expr* t);
    expr* get_parent(unsigned n) const;
    void init_terms(expr_ref_vector const& terms);
    void init_nodes();
    void eliminate();
    void reconstruct_terms();
    void assert_normalized(vector<dependent_expr>& old_fmls);
    void update_model_trail(generic_model_converter& mc, vector<dependent_expr> const& old_fmls);
    
public:

    elim_unconstrained(ast_manager& m, dependent_expr_state& fmls);

    void reduce() override;

    void collect_statistics(statistics& st) const override { st.update("elim-unconstrained", m_stats.m_num_eliminated); }

    void reset_statistics() override { m_stats.reset(); }
};
