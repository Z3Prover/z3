/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_bdd.cpp

Abstract:

    Simple BDD package modeled after BuDDy, which is modeled after CUDD.

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-13

Revision History:

--*/

#include "sat/sat_bdd.h"

namespace sat {

    bdd_manager::bdd_manager(unsigned num_vars, unsigned cache_size) {
        for (BDD a = 0; a < 2; ++a) {
            for (BDD b = 0; b < 2; ++b) {
                for (unsigned op = bdd_and_op; op < bdd_no_op; ++op) {                
                    unsigned index = a + 2*b + 4*op;
                    m_apply_const.reserve(index+1);
                    m_apply_const[index] = apply_const(a, b, static_cast<bdd_op>(op));
                }
            }
        }
        // add two dummy nodes for true_bdd and false_bdd
        m_nodes.push_back(bdd_node(0,0,0));
        m_nodes.push_back(bdd_node(0,0,0));
        m_nodes[0].m_refcount = max_rc;
        m_nodes[1].m_refcount = max_rc;
        
        // add variables
        for (unsigned i = 0; i < num_vars; ++i) {
            m_var2bdd.push_back(make_node(i, false_bdd, true_bdd));
            m_var2bdd.push_back(make_node(i, true_bdd, false_bdd));
            m_nodes[m_var2bdd[2*i]].m_refcount = max_rc;
            m_nodes[m_var2bdd[2*i+1]].m_refcount = max_rc;
            m_var2level.push_back(i);
            m_level2var.push_back(i);
        }    
        
        m_spare_entry = nullptr;
    }
    
    bdd_manager::BDD bdd_manager::apply_const(BDD a, BDD b, bdd_op op) {
        switch (op) {
        case bdd_and_op:
            return (a == 1 && b == 1) ? 1 : 0;
        case bdd_or_op:
            return (a == 1 || b == 1) ? 1 : 0;
        case bdd_iff_op:
            return (a == b) ? 1 : 0;
        default:
            UNREACHABLE();
            return 0;
        }
    }


    bdd_manager::BDD bdd_manager::apply(BDD arg1, BDD arg2, bdd_op op) {
        return apply_rec(arg1, arg2, op);
    }

    bdd_manager::BDD bdd_manager::apply_rec(BDD a, BDD b, bdd_op op) {
        switch (op) {
        case bdd_and_op:
            if (a == b) return a;
            if (is_false(a) || is_false(b)) return false_bdd;
            if (is_true(a)) return b;
            if (is_true(b)) return a;
            break;
        case bdd_or_op:
            if (a == b) return a;
            if (is_false(a)) return b;
            if (is_false(b)) return a;
            if (is_true(a) || is_true(b)) return true_bdd;
            break;
        case bdd_iff_op:
            if (a == b) return true_bdd;
            if (is_true(a)) return b;
            if (is_true(b)) return a;
            break;
        default:
            UNREACHABLE();
            break;
        }
        if (is_const(a) && is_const(b)) {
            return m_apply_const[a + 2*b + 4*op];
        }
        cache_entry * e1 = pop_entry(hash2(a, b, op));
        cache_entry const* e2 = m_cache.insert_if_not_there(e1);
        if (e2->m_op == op && e2->m_bdd1 == a && e2->m_bdd2 == b) {
            push_entry(e1);
            return e2->m_result;
        }
        BDD r;
        if (level(a) == level(b)) {
            push(apply_rec(lo(a), lo(b), op));
            push(apply_rec(hi(a), hi(b), op));
            r = make_node(level(a), read(2), read(1));
        }
        else if (level(a) < level(b)) {
            push(apply_rec(lo(a), b, op));
            push(apply_rec(hi(a), b, op));
            r = make_node(level(a), read(2), read(1));
        }
        else {
            push(apply_rec(a, lo(b), op));
            push(apply_rec(a, hi(b), op));
            r = make_node(level(b), read(2), read(1));
        }
        e1->m_result = r;
        e1->m_bdd1 = a;
        e1->m_bdd2 = b;
        e1->m_op = op;
        return r;
    }

    void bdd_manager::push(BDD b) {
        m_bdd_stack.push_back(b);
    }

    void bdd_manager::pop(unsigned num_scopes) {
        m_bdd_stack.shrink(m_bdd_stack.size() - num_scopes);
    }

    bdd_manager::BDD bdd_manager::read(unsigned index) {
        return m_bdd_stack[m_bdd_stack.size() - index];
    }


    bdd_manager::cache_entry* bdd_manager::pop_entry(unsigned hash) {
        cache_entry* result = 0;
        if (m_spare_entry) {
            result = m_spare_entry;
            m_spare_entry = 0;
            result->m_hash = hash;
        }
        else {
            void * mem = m_alloc.allocate(sizeof(cache_entry));
            result = new (mem) cache_entry(hash);
        }
        return result;
    }

    void bdd_manager::push_entry(cache_entry* e) {
        SASSERT(!m_spare_entry);
        m_spare_entry = e;
    }


    bdd_manager::BDD bdd_manager::make_node(unsigned level, BDD l, BDD r) {
        if (l == r) {
            return l;
        }
#if 0
        // TBD
        unsigned hash = node_hash(level, l, r);
        bdd result = m_
#endif
        int sz = m_nodes.size();
        m_nodes.push_back(bdd_node(level, l, r));        
        return sz;
    }

#if 0
    void bdd_manager::bdd_reorder(int) {
        
    }
#endif

    bdd bdd_manager::mk_var(unsigned i) {
        return bdd(m_var2bdd[2*i+1], this);        
    }

    bdd bdd_manager::mk_nvar(unsigned i) {
        return bdd(m_var2bdd[2*i+1], this);
    }

    unsigned bdd_manager::hash2(BDD a, BDD b, bdd_op op) const {
        return mk_mix(a, b, op);
    }

    bdd bdd_manager::mk_not(bdd b) {
        return bdd(mk_not_rec(b.root), this);
    }

    bdd_manager::BDD bdd_manager::mk_not_rec(BDD b) {
        if (is_true(b)) return false_bdd;
        if (is_false(b)) return true_bdd;
        cache_entry* e1 = pop_entry(hash1(b, bdd_not_op));
        cache_entry const* e2 = m_cache.insert_if_not_there(e1);
        if (e2->m_bdd1 == b && e2->m_op == bdd_not_op) {
            push_entry(e1);
            return e2->m_result;
        }
        push(mk_not_rec(lo(b)));
        push(mk_not_rec(hi(b)));
        BDD r = make_node(level(b), read(2), read(1));
        pop(2);
        e1->m_bdd1 = b;
        e1->m_bdd2 = b;
        e1->m_op = bdd_not_op;
        e1->m_result = r;
        return r;
    }

#if 0
    bdd bdd_manager::mk_exists(bdd vars, bdd b) {

    }

    bdd bdd_manager::mk_forall(bdd vars, bdd b) {

    }

    bdd bdd_manager::mk_ite(bdd c, bdd t, bdd e) {

    }

    double bdd_manager::path_count(bdd b) {

    }

#endif

    std::ostream& bdd_manager::display(std::ostream& out, bdd b) {
    
        return out;
    }

    std::ostream& bdd_manager::display(std::ostream& out) {

        return out;
    }

    bdd::bdd(int root, bdd_manager* m):
        root(root), m(m) { 
        m->inc_ref(root); 
    }

    bdd::bdd(bdd & other): root(other.root), m(other.m) { m->inc_ref(root); }


    bdd::~bdd() {
        m->dec_ref(root);
    }

#if 0
#endif

}
