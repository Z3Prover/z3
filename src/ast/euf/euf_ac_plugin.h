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

#include <iostream>
#include "ast/euf/euf_plugin.h"

namespace euf {

    class ac_plugin : public plugin {

        struct stats {
            unsigned m_num_superpositions = 0;// number of superpositions
        };

        // enode structure for AC equivalences
        struct node {
            enode* n;                  // associated enode
            unsigned_vector shared;    // shared occurrences
            unsigned_vector eqs;       // equality occurrences
            bool is_zero = false;
            
            unsigned id() const { return n->get_id(); }
            static node* mk(region& r, enode* n);
        };

        struct bloom {
            uint64_t m_tick = 0;
            uint64_t m_filter = 0;
        };

        enum eq_status {
            is_processed_eq, is_passive_eq, is_to_simplify_eq, is_reducing_eq, is_dead_eq
        };

        // represent equalities added by merge_eh and by superposition
        struct eq {
            eq(unsigned l, unsigned r, justification j):
                l(l), r(r), j(j) {}
            unsigned l, r;              // refer to monomials
            eq_status status = is_to_simplify_eq;
            justification j;            // justification for equality
        };

        // represent shared enodes that use the AC symbol.
        struct shared {
            enode* n;         // original shared enode
            unsigned m;       // monomial index
            justification j;  // justification for current simplification of monomial
        };

        struct monomial_t {
            ptr_vector<node> m_nodes;
            bloom m_bloom;
            enode* m_src = nullptr;
            node* operator[](unsigned i) const { return m_nodes[i]; }
            unsigned size() const { return m_nodes.size(); }
            void set(ptr_vector<node> const& ns) { m_nodes.reset(); m_nodes.append(ns); m_bloom.m_tick = 0; }
            node* const* begin() const { return m_nodes.begin(); }
            node* const* end() const { return m_nodes.end(); }
            node* * begin() { return m_nodes.begin(); }
            node* * end() { return m_nodes.end(); }            
        };


        struct monomial_hash {
            ac_plugin& p;
            monomial_hash(ac_plugin& p) :p(p) {}
            unsigned operator()(unsigned i) const {
                unsigned h = 0;
                auto& m = p.monomial(i);
                if (!p.is_sorted(m))
                    p.sort(m);
                for (auto* n : m)
                    h = combine_hash(h, n->id());
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
                    if (m1[k]->id() != m2[k]->id())
                        return false;
                return true;
            }
        };

        theory_id                m_fid = 0;
        decl_kind                m_op = null_decl_kind;
        func_decl*               m_decl = nullptr;
        bool                     m_is_injective = false;
        vector<eq>               m_active, m_passive;
        enode_pair_vector        m_queued;
        ptr_vector<node>         m_nodes;
        bool_vector              m_shared_nodes;
        vector<monomial_t>       m_monomials;
        svector<shared>          m_shared;
        justification::dependency_manager m_dep_manager;
        tracked_uint_set         m_to_simplify_todo;
        tracked_uint_set         m_shared_todo;
        uint64_t                 m_tick = 1;
        symbol                   m_name;
        unsigned                 m_fuel = 0;
        unsigned                 m_fuel_inc = 3;
        stats                    m_stats;
        mutable symbol           m_superposition_stats, m_eqs_stats;
        


        monomial_hash m_hash;
        monomial_eq   m_eq;
        map<unsigned, shared, monomial_hash, monomial_eq> m_monomial_table;
        

        // backtrackable state
        enum undo_kind {
            is_queue_eq,
            is_add_monomial,
            is_add_node,
            is_add_shared_index,
            is_add_eq_index,
            is_register_shared,
            is_update_shared,
            is_push_scope
        };
        svector<undo_kind>       m_undo;
        ptr_vector<node>         m_node_trail;
        unsigned                 m_queue_head = 0;

        svector<std::pair<unsigned, shared>> m_update_shared_trail;
        svector<std::tuple<node*, unsigned, unsigned>> m_merge_trail;



        node* mk_node(enode* n);
        void merge(node* r1, node* r2, justification j);

        bool is_op(enode* n) const { auto d = n->get_decl(); return d && (d == m_decl || (m_fid == d->get_family_id() && m_op == d->get_decl_kind())); }

        std::function<void(void)> m_undo_notify;
        void push_undo(undo_kind k);
        enode_vector m_todo;
        unsigned to_monomial(enode* n);
        unsigned to_monomial(enode* n, ptr_vector<node> const& ms);
        unsigned to_monomial(ptr_vector<node> const& ms) { return to_monomial(nullptr, ms); }
        enode* from_monomial(ptr_vector<node> const& m);
        monomial_t const& monomial(unsigned i) const { return m_monomials[i]; }
        monomial_t& monomial(unsigned i) { return m_monomials[i]; }
        
        void sort(monomial_t& monomial);
        bool is_sorted(monomial_t const& monomial) const;
        uint64_t filter(monomial_t& m);
        bool can_be_subset(monomial_t& subset, monomial_t& superset);
        bool can_be_subset(monomial_t& subset, ptr_vector<node> const& m, bloom& b);
        bool are_equal(ptr_vector<node> const& a, ptr_vector<node> const& b);
        bool are_equal(monomial_t& a, monomial_t& b);
        bool are_equal(eq const& a, eq const& b)  {
            return are_equal(monomial(a.l), monomial(b.l)) && are_equal(monomial(a.r), monomial(b.r));
        }
        bool bloom_filter_is_correct(ptr_vector<node> const& m, bloom const& b) const;
        bool well_formed(eq const& e) const;
        bool is_reducing(eq const& e) const;
        void backward_reduce(unsigned eq_id);
        void backward_reduce(eq const& eq, unsigned dst);
        bool backward_reduce_monomial(eq const& src, eq & dst, monomial_t& m);
        void forward_subsume_new_eqs();
        bool is_forward_subsumed(unsigned dst_eq);
        bool forward_subsumes(unsigned src_eq, unsigned dst_eq);
        bool backward_subsumes(unsigned src_eq, unsigned dst_eq);

        enode_vector m_units;
        enode* get_unit(enode* n) const {
            for (auto u : m_units) {
                if (u->get_sort() == n->get_sort())
                    return u;
            }
            UNREACHABLE();
            return nullptr;
        }
       
        bool init_equation(eq e, bool is_active);
        void push_equation(enode* l, enode* r);
        void pop_equation(enode* l, enode* r);
        bool orient_equation(eq& e);
        void set_status(unsigned eq_id, eq_status s);
        unsigned pick_next_eq();

        unsigned_vector m_new_eqs;
        void backward_simplify(unsigned eq_id, unsigned using_eq);
        bool forward_simplify(unsigned eq_id, unsigned using_eq);
        bool superpose(unsigned src_eq, unsigned dst_eq);
        void deduplicate(monomial_t& a, monomial_t& b);
        void deduplicate(ptr_vector<node>& a, ptr_vector<node>& b);
        
        ptr_vector<node> m_src_r, m_src_l, m_dst_r, m_dst_l;

        struct ref_counts {
            unsigned_vector ids;
            unsigned_vector counts;
            void reset() { for (auto idx : ids) counts[idx] = 0; ids.reset(); }
            unsigned operator[](unsigned idx) const { return counts.get(idx, 0); }
            void inc(unsigned idx, unsigned amount) { counts.reserve(idx + 1, 0); ids.push_back(idx);  counts[idx] += amount; }
            void dec(unsigned idx, unsigned amount) { counts.reserve(idx + 1, 0); ids.push_back(idx);  counts[idx] -= amount; }
            unsigned const* begin() const { return ids.begin(); }
            unsigned const* end() const { return ids.end(); }
        };
        ref_counts m_src_l_counts, m_dst_l_counts, m_src_r_counts, m_dst_r_counts, m_eq_counts, m_m_counts;
        unsigned_vector m_eq_occurs;
        bool_vector m_eq_seen;

        unsigned_vector const& backward_iterator(unsigned eq);
        unsigned_vector const& superpose_iterator(unsigned eq);
        unsigned_vector const& forward_iterator(unsigned eq);
        void init_ref_counts(monomial_t const& monomial, ref_counts& counts) const;
        void init_ref_counts(ptr_vector<node> const& monomial, ref_counts& counts) const;
        void init_overlap_iterator(unsigned eq, monomial_t const& m);
        void init_subset_iterator(unsigned eq, monomial_t const& m);
        void compress_eq_occurs(unsigned eq_id);
        // check that src is a subset of dst, where dst_counts are precomputed
        bool is_subset(ref_counts const& dst_counts, ref_counts& src_counts, monomial_t const& src);
        bool is_equation_oriented(eq const& e) const;

        // check that dst is a superset of dst, where src_counts are precomputed
        bool is_superset(ref_counts const& src_counts, ref_counts& dst_counts, monomial_t const& dst);
        void rewrite1(ref_counts const& src_l, monomial_t const& src_r, ref_counts& dst_r_counts, ptr_vector<node>& dst_r);
        bool reduce(ptr_vector<node>& m, justification& j);
        void index_new_r(unsigned eq, monomial_t const& old_r, monomial_t const& new_r);

        bool is_to_simplify(unsigned eq) const { return m_active[eq].status == eq_status::is_to_simplify_eq; }
        bool is_processed(unsigned eq) const { return m_active[eq].status == eq_status::is_processed_eq; }
        bool is_reducing(unsigned eq) const { return m_active[eq].status == eq_status::is_reducing_eq; }
        bool is_active(unsigned eq) const { return m_active[eq].status != eq_status::is_dead_eq; }

        justification justify_rewrite(unsigned eq1, unsigned eq2);
        justification::dependency* justify_equation(unsigned eq);
        justification join(justification j1, unsigned eq);
        justification join(justification j1, eq const& eq);

        bool is_correct_ref_count(monomial_t const& m, ref_counts const& counts) const;
        bool is_correct_ref_count(ptr_vector<node> const& m, ref_counts const& counts) const;
        
        void register_shared(enode* n);
        void propagate_shared();
        void simplify_shared(unsigned idx, shared s);

        std::ostream& display_monomial(std::ostream& out, monomial_t const& m) const { return display_monomial(out, m.m_nodes); }
        std::ostream& display_monomial(std::ostream& out, ptr_vector<node> const& m) const;
        std::ostream& display_equation(std::ostream& out, eq const& e) const;
        std::ostream& display_monomial_ll(std::ostream& out, monomial_t const& m) const { return display_monomial_ll(out, m.m_nodes); }
        std::ostream& display_monomial_ll(std::ostream& out, ptr_vector<node> const& m) const;
        std::ostream& display_equation_ll(std::ostream& out, eq const& e) const;
        std::ostream& display_status(std::ostream& out, eq_status s) const;


    public:

        ac_plugin(egraph& g, char const* name, unsigned fid, unsigned op);

        ac_plugin(egraph& g, func_decl* f);

        void set_injective() { m_is_injective = true; }

        void add_unit(enode*);

        void add_zero(enode*);
        
        theory_id get_id() const override { return m_fid; }

        void register_node(enode* n) override;

        void merge_eh(enode* n1, enode* n2) override;

        void diseq_eh(enode* eq) override;

        void undo() override;

        void push_scope_eh() override;

        void propagate() override;
        
        std::ostream& display(std::ostream& out) const override;

        void collect_statistics(statistics& st) const override;

        void set_undo(std::function<void(void)> u) { m_undo_notify = u; }

        struct eq_pp {
            ac_plugin const& p; eq const& e; 
            eq_pp(ac_plugin const& p, eq const& e) : p(p), e(e) {}; 
            eq_pp(ac_plugin const& p, unsigned eq_id): p(p), e(p.m_active[eq_id]) {}
            std::ostream& display(std::ostream& out) const { return p.display_equation(out, e); }
        };

        struct eq_pp_ll {
            ac_plugin const& p; eq const& e;
            eq_pp_ll(ac_plugin const& p, eq const& e) : p(p), e(e) {};
            eq_pp_ll(ac_plugin const& p, unsigned eq_id) : p(p), e(p.m_active[eq_id]) {}
            std::ostream& display(std::ostream& out) const { return p.display_equation_ll(out, e); }
        };

        struct m_pp { 
            ac_plugin const& p; ptr_vector<node> const& m; 
            m_pp(ac_plugin const& p, monomial_t const& m) : p(p), m(m.m_nodes) {} 
            m_pp(ac_plugin const& p, ptr_vector<node> const& m) : p(p), m(m) {}
            std::ostream& display(std::ostream& out) const { return p.display_monomial(out, m); }
        };

        struct m_pp_ll {
            ac_plugin const& p; ptr_vector<node> const& m;
            m_pp_ll(ac_plugin const& p, monomial_t const& m) : p(p), m(m.m_nodes) {}
            m_pp_ll(ac_plugin const& p, ptr_vector<node> const& m) : p(p), m(m) {}
            std::ostream& display(std::ostream& out) const { return p.display_monomial_ll(out, m); }
        };
    };

    inline std::ostream& operator<<(std::ostream& out, ac_plugin::eq_pp const& d) { return d.display(out); }
    inline std::ostream& operator<<(std::ostream& out, ac_plugin::eq_pp_ll const& d) { return d.display(out); }
    inline std::ostream& operator<<(std::ostream& out, ac_plugin::m_pp const& d) { return d.display(out); }
    inline std::ostream& operator<<(std::ostream& out, ac_plugin::m_pp_ll const& d) { return d.display(out); }
}
