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

    struct bdd_pair {
        int*      m_bdd;
        int       m_last;
        int       m_id;
        bdd_pair* m_next;
    };

    class bdd_manager;

    class bdd {
        friend class bdd_manager;
        int          root;
        bdd_manager* m;
        bdd(int root, bdd_manager* m);
    public:
        bdd(bdd & other);
        ~bdd();        
        // bdd operator!() { return m->mk_not(*this); }
    };

    class bdd_manager {
        friend bdd;

        typedef int BDD;

        enum bdd_op {
            bdd_and_op = 0,
            bdd_or_op,
            bdd_iff_op,
            bdd_not_op,
            bdd_no_op
        };

        struct bdd_node {
            bdd_node(unsigned level, int lo, int hi):
                m_refcount(0),
                m_level(level),
                m_lo(lo),
                m_hi(hi)
            {}
            unsigned m_refcount : 10;
            unsigned m_level : 22;
            int      m_lo;
            int      m_hi;
            //unsigned m_hash;
            //unsigned m_next;
        };
        
        struct cache_entry {
            cache_entry(unsigned hash):
                m_bdd1(0),
                m_bdd2(0),
                m_op(bdd_no_op),
                m_result(0),
                m_hash(hash)
            {}

            BDD      m_bdd1;
            BDD      m_bdd2;
            bdd_op   m_op;
            BDD      m_result;
            unsigned m_hash;
        };

        struct hash_entry {
            unsigned operator()(cache_entry* e) const { return e->m_hash; }
        };

        struct eq_entry {
            bool operator()(cache_entry * a, cache_entry * b) const { 
                return a->m_hash == b->m_hash; 
            }
        };

        svector<bdd_node> m_nodes;
        ptr_hashtable<cache_entry, hash_entry, eq_entry> m_cache;
        unsigned_vector    m_apply_const;
        svector<BDD>       m_bdd_stack;
        cache_entry*       m_spare_entry;
        svector<BDD>       m_var2bdd;
        unsigned_vector    m_var2level, m_level2var;
        small_object_allocator m_alloc;

        BDD make_node(unsigned level, BDD l, BDD r);

        BDD apply_const(BDD a, BDD b, bdd_op op);
        BDD apply(BDD arg1, BDD arg2, bdd_op op);
        BDD apply_rec(BDD arg1, BDD arg2, bdd_op op);

        void push(BDD b);
        void pop(unsigned num_scopes);
        BDD read(unsigned index);

        cache_entry* pop_entry(unsigned hash);
        void push_entry(cache_entry* e);
        
        // void bdd_reorder(int);

        BDD mk_not_rec(BDD b);

        unsigned hash1(BDD b, bdd_op op) const { return hash2(b, b, op); }
        unsigned hash2(BDD a, BDD b, bdd_op op) const;
        unsigned hash3(BDD a, BDD b, BDD c, bdd_op op) const;

        static const BDD false_bdd = 0;
        static const BDD true_bdd = 1;
        static const unsigned max_rc = (1 << 10) - 1;

        inline bool is_true(BDD b) const { return b == true_bdd; }
        inline bool is_false(BDD b) const { return b == false_bdd; }
        inline bool is_const(BDD b) const { return 0 <= b && b <= 1; }

        unsigned level(BDD b) const { return m_nodes[b].m_level; }
        BDD lo(BDD b) const { return m_nodes[b].m_lo; }
        BDD hi(BDD b) const { return m_nodes[b].m_hi; }
        void inc_ref(BDD b) { if (m_nodes[b].m_refcount != max_rc) m_nodes[b].m_refcount++; }
        void dec_ref(BDD b) { if (m_nodes[b].m_refcount != max_rc && m_nodes[b].m_refcount > 0) m_nodes[b].m_refcount--; }

        BDD mk_true() { return 1; }
        BDD mk_false() { return 0; }

    public:
        bdd_manager(unsigned nodes, unsigned cache_size);
        
        bdd mk_var(unsigned i);
        bdd mk_nvar(unsigned i);

        bdd mk_not(bdd b);
        bdd mk_exist(bdd vars, bdd b);
        bdd mk_forall(bdd vars, bdd b);
        bdd mk_and(bdd a, bdd b) { return bdd(apply(a.root, b.root, bdd_and_op), this); }
        bdd mk_or(bdd a, bdd b) { return bdd(apply(a.root, b.root, bdd_or_op), this); }
        bdd mk_iff(bdd a, bdd b) { return bdd(apply(a.root, b.root, bdd_iff_op), this); }
        bdd mk_ite(bdd c, bdd t, bdd e);

        double path_count(bdd b);

        std::ostream& display(std::ostream& out, bdd b);
        std::ostream& display(std::ostream& out);
    };
}

#endif
