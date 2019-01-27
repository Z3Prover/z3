/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_bdd

Abstract:

    Simple BDD package modeled after BuDDy, which is modeled after CUDD.

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-13

Revision History:

--*/
#ifndef SAT_BDD_H_
#define SAT_BDD_H_

#include "util/vector.h"
#include "util/map.h"
#include "util/small_object_allocator.h"

namespace sat {

    class bdd;

    class bdd_manager {
        friend bdd;

        typedef unsigned BDD;

        const BDD null_bdd = UINT_MAX;

        enum bdd_op {
            bdd_and_op = 2,
            bdd_or_op = 3,
            bdd_xor_op = 4,
            bdd_not_op = 5,
            bdd_and_proj_op = 6,
            bdd_or_proj_op = 7,
            bdd_no_op = 8,
        };

        struct bdd_node {
            bdd_node(unsigned level, BDD lo, BDD hi):
                m_refcount(0),
                m_level(level),
                m_lo(lo),
                m_hi(hi),
                m_index(0)
            {}
            bdd_node(): m_refcount(0), m_level(0), m_lo(0), m_hi(0), m_index(0) {}
            unsigned m_refcount : 10;
            unsigned m_level : 22;
            BDD      m_lo;
            BDD      m_hi;
            unsigned m_index;
            unsigned hash() const { return mk_mix(m_level, m_lo, m_hi); }
            bool is_internal() const { return m_lo == 0 && m_hi == 0; }
            void set_internal() { m_lo = 0; m_hi = 0; }
        };

        enum cost_metric {
            cnf_cost,
            dnf_cost,
            bdd_cost
        };

        struct hash_node {
            unsigned operator()(bdd_node const& n) const { return n.hash(); }
        };

        struct eq_node {
            bool operator()(bdd_node const& a, bdd_node const& b) const {
                return a.m_lo == b.m_lo && a.m_hi == b.m_hi && a.m_level == b.m_level;
            }
        };
        
        typedef hashtable<bdd_node, hash_node, eq_node> node_table;

        struct op_entry {
            op_entry(BDD l, BDD r, BDD op):
                m_bdd1(l),
                m_bdd2(r),
                m_op(op),
                m_result(0)
            {}

            BDD      m_bdd1;
            BDD      m_bdd2;
            BDD      m_op;
            BDD      m_result;
            unsigned hash() const { return mk_mix(m_bdd1, m_bdd2, m_op); }
        };

        struct hash_entry {
            unsigned operator()(op_entry* e) const { return e->hash(); }
        };

        struct eq_entry {
            bool operator()(op_entry * a, op_entry * b) const { 
                return a->m_bdd1 == b->m_bdd2 && a->m_bdd2 == b->m_bdd2 && a->m_op == b->m_op;
            }
        };

        typedef ptr_hashtable<op_entry, hash_entry, eq_entry> op_table;

        svector<bdd_node>          m_nodes;
        op_table                   m_op_cache;
        node_table                 m_node_table;
        unsigned_vector            m_apply_const;
        svector<BDD>               m_bdd_stack;
        op_entry*                  m_spare_entry;
        svector<BDD>               m_var2bdd;
        unsigned_vector            m_var2level, m_level2var;
        unsigned_vector            m_free_nodes;
        small_object_allocator     m_alloc;
        mutable svector<unsigned>  m_mark;
        mutable unsigned           m_mark_level;
        mutable svector<double>    m_count;
        mutable svector<BDD>       m_todo;
        bool                       m_disable_gc;
        bool                       m_is_new_node;
        unsigned                   m_max_num_bdd_nodes;
        unsigned_vector            m_S, m_T, m_to_free;  // used for reordering
        vector<unsigned_vector>    m_level2nodes;
        unsigned_vector            m_reorder_rc;
        cost_metric                m_cost_metric;
        BDD                        m_cost_bdd;

        BDD make_node(unsigned level, BDD l, BDD r);
        bool is_new_node() const { return m_is_new_node; }

        BDD apply_const(BDD a, BDD b, bdd_op op);
        BDD apply(BDD arg1, BDD arg2, bdd_op op);
        BDD mk_quant(unsigned n, unsigned const* vars, BDD b, bdd_op op);

        BDD apply_rec(BDD arg1, BDD arg2, bdd_op op);
        BDD mk_not_rec(BDD b);
        BDD mk_ite_rec(BDD a, BDD b, BDD c);
        BDD mk_quant_rec(unsigned lvl, BDD b, bdd_op op);

        void push(BDD b);
        void pop(unsigned num_scopes);
        BDD read(unsigned index);

        op_entry* pop_entry(BDD l, BDD r, BDD op);
        void push_entry(op_entry* e);
        bool check_result(op_entry*& e1, op_entry const* e2, BDD a, BDD b, BDD c);
        
        double count(BDD b, unsigned z);

        void alloc_free_nodes(unsigned n);
        void init_mark();
        void set_mark(unsigned i) { m_mark[i] = m_mark_level; }
        bool is_marked(unsigned i) { return m_mark[i] == m_mark_level; }

        void init_reorder();
        void reorder_incref(unsigned n);
        void reorder_decref(unsigned n);
        void sift_up(unsigned level);
        void sift_var(unsigned v);
        double current_cost();
        bool is_bad_cost(double new_cost, double best_cost) const;

        static const BDD false_bdd = 0;
        static const BDD true_bdd = 1;
        static const unsigned max_rc = (1 << 10) - 1;

        inline bool is_true(BDD b) const { return b == true_bdd; }
        inline bool is_false(BDD b) const { return b == false_bdd; }
        inline bool is_const(BDD b) const { return b <= 1; }
        inline unsigned level(BDD b) const { return m_nodes[b].m_level; }
        inline unsigned var(BDD b) const { return m_level2var[level(b)]; }
        inline BDD lo(BDD b) const { return m_nodes[b].m_lo; }
        inline BDD hi(BDD b) const { return m_nodes[b].m_hi; }
        inline void inc_ref(BDD b) { if (m_nodes[b].m_refcount != max_rc) m_nodes[b].m_refcount++; VERIFY(!m_free_nodes.contains(b)); }
        inline void dec_ref(BDD b) { if (m_nodes[b].m_refcount != max_rc) m_nodes[b].m_refcount--; VERIFY(!m_free_nodes.contains(b)); }
        inline BDD level2bdd(unsigned l) const { return m_var2bdd[m_level2var[l]]; }

        double dnf_size(BDD b) { return count(b, 0); }
        double cnf_size(BDD b) { return count(b, 1); }
        unsigned bdd_size(bdd const& b);

        bdd mk_not(bdd b);
        bdd mk_and(bdd const& a, bdd const& b);
        bdd mk_or(bdd const& a, bdd const& b);
        bdd mk_xor(bdd const& a, bdd const& b);

        void reserve_var(unsigned v);
        bool well_formed();

    public:
        struct mem_out {};

        bdd_manager(unsigned nodes);
        ~bdd_manager();

        void set_max_num_nodes(unsigned n) { m_max_num_bdd_nodes = n; }

        bdd mk_var(unsigned i);
        bdd mk_nvar(unsigned i);

        bdd mk_true();
        bdd mk_false();

        bdd mk_exists(unsigned n, unsigned const* vars, bdd const & b);
        bdd mk_forall(unsigned n, unsigned const* vars, bdd const & b);
        bdd mk_exists(unsigned v, bdd const& b);
        bdd mk_forall(unsigned v, bdd const& b);
        bdd mk_ite(bdd const& c, bdd const& t, bdd const& e);

        std::ostream& display(std::ostream& out);
        std::ostream& display(std::ostream& out, bdd const& b);

        void gc();
        void try_reorder();
        void try_cnf_reorder(bdd const& b);
    };

    class bdd {
        friend class bdd_manager;
        unsigned     root;
        bdd_manager* m;
        bdd(unsigned root, bdd_manager* m): root(root), m(m) { m->inc_ref(root); }
    public:
        bdd(bdd & other): root(other.root), m(other.m) { m->inc_ref(root); }
        bdd(bdd && other): root(0), m(other.m) { std::swap(root, other.root); }
        bdd& operator=(bdd const& other);
        ~bdd() { m->dec_ref(root); }
        bdd lo() const { return bdd(m->lo(root), m); }
        bdd hi() const { return bdd(m->hi(root), m); }
        unsigned var() const { return m->var(root); }

        bool is_true() const { return root == bdd_manager::true_bdd; }
        bool is_false() const { return root == bdd_manager::false_bdd; }        

        bdd operator!() { return m->mk_not(*this); }
        bdd operator&&(bdd const& other) { return m->mk_and(*this, other); }
        bdd operator||(bdd const& other) { return m->mk_or(*this, other); }
        bdd operator^(bdd const& other) { return m->mk_xor(*this, other); }
        bdd operator|=(bdd const& other) { return *this = *this || other; }
        bdd operator&=(bdd const& other) { return *this = *this && other; }
        std::ostream& display(std::ostream& out) const { return m->display(out, *this); }
        bool operator==(bdd const& other) const { return root == other.root; }
        bool operator!=(bdd const& other) const { return root != other.root; }
        double cnf_size() const { return m->cnf_size(root); }
        double dnf_size() const { return m->dnf_size(root); }
        unsigned bdd_size() const { return m->bdd_size(*this); }
    };

    std::ostream& operator<<(std::ostream& out, bdd const& b);

}


#endif
