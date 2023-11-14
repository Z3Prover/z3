/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_ac_plugin.h

Abstract:

    plugin structure for ac functions

Author:

    Nikolaj Bjorner (nbjorner) 2023-11-11

ex:
xyz -> xy, then xyzz -> xy by repeated rewriting

monomials = [0 |-> xyz, 1 |-> xy, 2 |-> xyzz]
parents(x) = [0, 1, 2]
parents(z) = [0, 1]
for p in parents(xyzz):
    p != xyzz
    p' := simplify_using(xyzz, p)
    if p != p':
       repeat reduction using p := p'

--*/

#pragma once

#include "ast/euf/euf_plugin.h"

namespace euf {

    class ac_plugin : public plugin {

        // enode structure for AC equivalenes
        struct node {
            enode* n;        // associated enode
            node* root;      // path compressed root
            node* next;      // next in equaivalence class
            justification j; // justification for equality
            node* target = nullptr;    // justified next
            unsigned_vector shared;    // shared occurrences
            unsigned_vector lhs;       // left hand side of equalities
            unsigned_vector rhs;       // left side of equalities

            unsigned root_id() const { return root->n->get_id(); }
            ~node() {}
            static node* mk(region& r, enode* n);
        };

        class equiv {
            node& n;
        public:
            class iterator {
                node* m_first;
                node* m_last;
            public:
                iterator(node* n, node* m) : m_first(n), m_last(m) {}
                node* operator*() { return m_first; }
                iterator& operator++() { if (!m_last) m_last = m_first; m_first = m_first->next; return *this; }
                iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
                bool operator==(iterator const& other) const { return m_last == other.m_last && m_first == other.m_first; }
                bool operator!=(iterator const& other) const { return !(*this == other); }
            };
            equiv(node& _n) :n(_n) {}
            equiv(node* _n) :n(*_n) {}
            iterator begin() const { return iterator(&n, nullptr); }
            iterator end() const { return iterator(&n, &n); }
        };

        // represent equalities added by merge_eh and by superposition
        struct eq {
            unsigned l, r;              // refer to monomials
            bool is_processed = false;  // true if the equality is in the processed set
            justification j;            // justification for equality
        };

        // represent shared enodes that use the AC symbol.
        struct shared {
            enode* n;         // original shared enode
            unsigned m;       // monomial index
            justification j;  // justification for current simplification of monomial
        };

        using monomial_t = ptr_vector<node>;

        struct monomial_hash {
            ac_plugin& p;
            monomial_hash(ac_plugin& p) :p(p) {}
            unsigned operator()(unsigned i) const {
                unsigned h = 0;
                auto& m = p.monomial(i);
                if (!p.is_sorted(m))
                    p.sort(m);
                for (auto* n : m)
                    h = combine_hash(h, n->root_id());
                return h;
            }
        };

        struct monomial_eq {
            ac_plugin& p;
            monomial_eq(ac_plugin& p) :p(p) {}
            bool operator()(unsigned i, unsigned j) const {
                auto const& m1 = p.monomial(i);
                auto const& m2 = p.monomial(j);
                if (m1.size() != m2.size()) return false;
                for (unsigned k = 0; k < m1.size(); ++k)
                    if (m1[k]->root_id() != m2[k]->root_id())
                        return false;
                return true;
            }
        };

        unsigned                 m_fid;
        unsigned                 m_op;
        vector<eq>               m_eqs;
        ptr_vector<node>         m_nodes;
        vector<monomial_t>       m_monomials;
        svector<shared>          m_shared;
        justification::dependency_manager m_dep_manager;
        tracked_uint_set         m_to_simplify_todo;
        tracked_uint_set         m_shared_todo;


        monomial_hash m_hash;
        monomial_eq   m_eq;
        map<unsigned, shared, monomial_hash, monomial_eq> m_monomial_table;
        

        // backtrackable state
        enum undo_kind {
            is_add_eq,
            is_add_monomial,
            is_add_node,
            is_merge_node,
            is_update_eq,
            is_add_shared,
            is_register_shared,
            is_update_shared
        };
        svector<undo_kind>       m_undo;
        ptr_vector<node>         m_node_trail;

        svector<std::pair<unsigned, shared>> m_update_shared_trail;
        svector<std::tuple<node*, unsigned, unsigned, unsigned>> m_merge_trail;
        svector<std::pair<unsigned, eq>> m_update_eq_trail;



        node* mk_node(enode* n);
        void merge(node* r1, node* r2, justification j);

        bool is_op(enode* n) const { auto d = n->get_decl(); return d && m_fid == d->get_family_id() && m_op == d->get_decl_kind(); }

        std::function<void(void)> m_undo_notify;
        void push_undo(undo_kind k);
        enode_vector m_todo;
        unsigned to_monomial(enode* n);
        unsigned to_monomial(enode* n, monomial_t const& ms);
        monomial_t const& monomial(unsigned i) const { return m_monomials[i]; }
        monomial_t& monomial(unsigned i) { return m_monomials[i]; }
        void sort(monomial_t& monomial);
        bool is_sorted(monomial_t const& monomial) const;

        void init_equation(eq const& e);
        bool orient_equation(eq& e);
        void set_processed(unsigned eq_id, bool f);
        unsigned pick_next_eq();

        void forward_simplify(unsigned eq_id, unsigned using_eq);
        void backward_simplify(unsigned eq_id, unsigned using_eq);
        void superpose(unsigned src_eq, unsigned dst_eq);

        monomial_t m_src_r, m_src_l, m_dst_r;
        unsigned_vector m_src_ids, m_src_count, m_dst_ids, m_dst_count;
        unsigned_vector m_lhs_eqs;
        bool_vector m_eq_seen;
        bool m_backward_simplified = false;

        unsigned_vector const& forward_iterator(unsigned eq);
        unsigned_vector const& superpose_iterator(unsigned eq);
        unsigned_vector const& backward_iterator(unsigned eq);
        void init_ids_counts(monomial_t const& monomial, unsigned_vector& ids, unsigned_vector& counts);
        void reset_ids_counts(unsigned_vector& ids, unsigned_vector& counts);
        void init_overlap_iterator(unsigned eq, monomial_t const& m);
        bool is_subset(monomial_t const& dst);
        unsigned rewrite(monomial_t const& src_r, monomial_t const& dst_r);

        bool is_to_simplify(unsigned eq) const { return !m_eqs[eq].is_processed; }
        bool is_processed(unsigned eq) const { return m_eqs[eq].is_processed; }

        justification justify_rewrite(unsigned eq1, unsigned eq2);
        justification::dependency* justify_equation(unsigned eq);
        justification::dependency* justify_monomial(justification::dependency* d, ptr_vector<node> const& m);

        void propagate_shared();
        void simplify_shared(unsigned idx, shared s);

        std::ostream& display_monomial(std::ostream& out, ptr_vector<node> const& m) const;
        std::ostream& display_equation(std::ostream& out, eq const& e) const;

    public:

        ac_plugin(egraph& g, unsigned fid, unsigned op);

        ~ac_plugin() override {}
        
        unsigned get_id() const override { return m_fid; }

        void register_node(enode* n) override;

        void register_shared(enode* n) override;

        void merge_eh(enode* n1, enode* n2, justification j) override;

        void diseq_eh(enode* n1, enode* n2) override {}

        void undo() override;

        void propagate() override;
        
        std::ostream& display(std::ostream& out) const override;

        void set_undo(std::function<void(void)> u) { m_undo_notify = u; }
    };
}
