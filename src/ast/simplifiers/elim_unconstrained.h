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

    friend class seq_simplifier;
    
    class node {
        expr_ref         m_term;
        proof_ref        m_proof;
        bool             m_dirty = false;
        ptr_vector<node> m_parents;
        node*            m_root = nullptr;
        bool             m_top = false;
    public:

        node(ast_manager& m, expr* t) :
            m_term(t, m),
            m_proof(m),
            m_root(this) { 
        }

        void set_top() { m_top = true; }
        bool is_top() const { return m_top; }

        void set_dirty() { m_dirty = true; }
        void set_clean() { m_dirty = false; }
        bool is_dirty() const { return m_dirty; }

        unsigned num_parents() const { return m_parents.size(); }
        ptr_vector<node> const& parents() const { return m_parents; }
        void add_parent(node& p) { m_parents.push_back(&p); }
        void add_parents(ptr_vector<node> const& ps) { m_parents.append(ps); }
        node& parent() const { SASSERT(num_parents() == 1); return *m_parents[0]; }

        bool is_root() const { return m_root == this; }
        node& root() { node* r = m_root; while (!r->is_root()) r = r->m_root; return *r; }
        node const& root() const { node* r = m_root; while (!r->is_root()) r = r->m_root; return *r; }
        void set_root(node& r) { 
            SASSERT(r.is_root());
            m_root = &r; 
            SASSERT(term()->get_sort() == r.term()->get_sort());
        }

        void set_proof(proof* p) { m_proof = p; }
        proof* get_proof() const { return m_proof; }

        expr* term() const { return m_term; }
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
    ptr_vector<node>         m_nodes;
    var_lt                   m_lt;
    heap<var_lt>             m_heap;
    expr_ref_vector          m_trail;
    expr_ref_vector          m_args;
    stats                    m_stats;
    bool                     m_created_compound = false;
    bool                     m_enable_proofs = false;

    bool is_var_lt(int v1, int v2) const;
    node& get_node(unsigned n) const { return *m_nodes[n]; }
    node& get_node(expr* t);
    node& root(expr* t) { return get_node(t).root(); }
    void set_root(node& n, node& r);
    void invalidate_parents(node& n);
    bool is_child(node const& ch, node const& p);

    void init_nodes();
    void reset_nodes();
    void eliminate();
    void reconstruct_terms();
    expr* reconstruct_term(node& n);
    void assert_normalized(vector<dependent_expr>& old_fmls);
    void update_model_trail(generic_model_converter& mc, vector<dependent_expr> const& old_fmls);

        
public:

    elim_unconstrained(ast_manager& m, dependent_expr_state& fmls);

    ~elim_unconstrained() override;

    char const* name() const override { return "elim-unconstrained"; }

    void reduce() override;

    void collect_statistics(statistics& st) const override { st.update("elim-unconstrained", m_stats.m_num_eliminated); }

    void reset_statistics() override { m_stats.reset(); }
};
