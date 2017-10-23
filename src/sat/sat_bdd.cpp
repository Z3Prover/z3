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
#include "util/trace.h"
#include "util/stopwatch.h"

namespace sat {

    bdd_manager::bdd_manager(unsigned num_vars) {
        m_cost_metric = bdd_cost;
        m_cost_bdd = 0;
        for (BDD a = 0; a < 2; ++a) {
            for (BDD b = 0; b < 2; ++b) {
                for (unsigned op = bdd_and_op; op < bdd_not_op; ++op) {                
                    unsigned index = a + 2*b + 4*op;
                    m_apply_const.reserve(index+1);
                    m_apply_const[index] = apply_const(a, b, static_cast<bdd_op>(op));
                }
            }
        }

        // add dummy nodes for operations, and true, false bdds.
        for (unsigned i = 0; i <= bdd_no_op + 2; ++i) {
            m_nodes.push_back(bdd_node(0,0,0));
            m_nodes.back().m_refcount = max_rc;
            m_nodes.back().m_index = m_nodes.size()-1;
        }

        m_spare_entry = nullptr;
        m_max_num_bdd_nodes = 1 << 24; // up to 16M nodes
        m_mark_level = 0;
        alloc_free_nodes(1024 + num_vars);
        m_disable_gc = false;
        m_is_new_node = false;
        
        // add variables
        for (unsigned i = 0; i < num_vars; ++i) {
            reserve_var(i);
        }            
    }

    bdd_manager::~bdd_manager() {
        if (m_spare_entry) {
            m_alloc.deallocate(sizeof(*m_spare_entry), m_spare_entry);
        }
        for (auto* e : m_op_cache) {
            SASSERT(e != m_spare_entry);
            m_alloc.deallocate(sizeof(*e), e);
        }
    }
    
    bdd_manager::BDD bdd_manager::apply_const(BDD a, BDD b, bdd_op op) {
        SASSERT(is_const(a) && is_const(b));
        switch (op) {
        case bdd_and_op:
            return (a == true_bdd && b == true_bdd) ? true_bdd : false_bdd;
        case bdd_or_op:
            return (a == true_bdd || b == true_bdd) ? true_bdd : false_bdd;
        case bdd_xor_op:
            return (a == b) ? false_bdd : true_bdd;
        default:
            return false_bdd;
        }
    }

    bdd_manager::BDD bdd_manager::apply(BDD arg1, BDD arg2, bdd_op op) {
        bool first = true;
        SASSERT(well_formed());
        while (true) {
            try {
                return apply_rec(arg1, arg2, op);
            }
            catch (mem_out) {
                try_reorder();
                if (!first) throw;
                first = false;
            }
        }
        SASSERT(well_formed());
    }


    bdd bdd_manager::mk_true() { return bdd(true_bdd, this); }
    bdd bdd_manager::mk_false() { return bdd(false_bdd, this); }
    bdd bdd_manager::mk_and(bdd const& a, bdd const& b) { return bdd(apply(a.root, b.root, bdd_and_op), this); }
    bdd bdd_manager::mk_or(bdd const& a, bdd const& b) { return bdd(apply(a.root, b.root, bdd_or_op), this); }
    bdd bdd_manager::mk_xor(bdd const& a, bdd const& b) { return bdd(apply(a.root, b.root, bdd_xor_op), this); }
    bdd bdd_manager::mk_exists(unsigned v, bdd const& b) { return mk_exists(1, &v, b); }
    bdd bdd_manager::mk_forall(unsigned v, bdd const& b) { return mk_forall(1, &v, b); }


    bool bdd_manager::check_result(op_entry*& e1, op_entry const* e2, BDD a, BDD b, BDD c) {
        if (e1 != e2) {
            SASSERT(e2->m_result != -1);
            push_entry(e1);
            e1 = nullptr;
            return true;            
        }
        else {
            e1->m_bdd1 = a;
            e1->m_bdd2 = b;
            e1->m_op = c;
            SASSERT(e1->m_result == -1);
            return false;        
        }
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
        case bdd_xor_op:
            if (a == b) return false_bdd;
            if (is_false(a)) return b;
            if (is_false(b)) return a;
            break;
        default:
            UNREACHABLE();
            break;
        }
        if (is_const(a) && is_const(b)) {
            return m_apply_const[a + 2*b + 4*op];
        }
        op_entry * e1 = pop_entry(a, b, op);
        op_entry const* e2 = m_op_cache.insert_if_not_there(e1);
        if (check_result(e1, e2, a, b, op)) {
            SASSERT(!m_free_nodes.contains(e2->m_result));
            return e2->m_result;
        }
        // SASSERT(well_formed());
        BDD r;
        if (level(a) == level(b)) {
            push(apply_rec(lo(a), lo(b), op));
            push(apply_rec(hi(a), hi(b), op));
            r = make_node(level(a), read(2), read(1));
        }
        else if (level(a) > level(b)) {
            push(apply_rec(lo(a), b, op));
            push(apply_rec(hi(a), b, op));
            r = make_node(level(a), read(2), read(1));
        }
        else {
            push(apply_rec(a, lo(b), op));
            push(apply_rec(a, hi(b), op));
            r = make_node(level(b), read(2), read(1));
        }
        pop(2);
        e1->m_result = r;
        // SASSERT(well_formed());
        SASSERT(!m_free_nodes.contains(r));
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

    bdd_manager::op_entry* bdd_manager::pop_entry(BDD l, BDD r, BDD op) {
        op_entry* result = nullptr;
        if (m_spare_entry) {
            result = m_spare_entry;
            m_spare_entry = nullptr;
            result->m_bdd1 = l;
            result->m_bdd2 = r;
            result->m_op = op;
        }
        else {
            void * mem = m_alloc.allocate(sizeof(op_entry));
            result = new (mem) op_entry(l, r, op);
        }
        result->m_result = -1;
        return result;
    }

    void bdd_manager::push_entry(op_entry* e) {
        SASSERT(!m_spare_entry);
        m_spare_entry = e;
    }

    bdd_manager::BDD bdd_manager::make_node(unsigned lvl, BDD l, BDD h) {
        m_is_new_node = false;
        if (l == h) {
            return l;
        }
        SASSERT(is_const(l) || level(l) < lvl);
        SASSERT(is_const(h) || level(h) < lvl);

        bdd_node n(lvl, l, h);
        node_table::entry* e = m_node_table.insert_if_not_there2(n);
        if (e->get_data().m_index != 0) {
            unsigned result = e->get_data().m_index;
            return result;
        }
        e->get_data().m_refcount = 0;
        bool do_gc = m_free_nodes.empty();
        if (do_gc && !m_disable_gc) {
            gc();
            e = m_node_table.insert_if_not_there2(n);
            e->get_data().m_refcount = 0;
        }
        if (do_gc && m_free_nodes.size()*3 < m_nodes.size()) {
            if (m_nodes.size() > m_max_num_bdd_nodes) {
                throw mem_out();
            }
            alloc_free_nodes(m_nodes.size()/2);
        }

        SASSERT(!m_free_nodes.empty());
        unsigned result = m_free_nodes.back();
        m_free_nodes.pop_back();
        e->get_data().m_index = result;
        m_nodes[result] = e->get_data();
        m_is_new_node = true;        
        SASSERT(!m_free_nodes.contains(result));
        SASSERT(m_nodes[result].m_index == result); 
        return result;
    }

    void bdd_manager::try_cnf_reorder(bdd const& b) {
        m_cost_bdd = b.root;
        m_cost_metric = cnf_cost;
        try_reorder();
        m_cost_metric = bdd_cost;
        m_cost_bdd = 0;
    }    

    void bdd_manager::try_reorder() {
        gc();        
        for (auto* e : m_op_cache) {
            m_alloc.deallocate(sizeof(*e), e);
        }
        m_op_cache.reset();
        init_reorder();
        for (unsigned i = 0; i < m_var2level.size(); ++i) {
            sift_var(i);
        }
        SASSERT(m_op_cache.empty());
        SASSERT(well_formed());
    }

    double bdd_manager::current_cost() {
        switch (m_cost_metric) {
        case bdd_cost: 
            return m_nodes.size() - m_free_nodes.size();
        case cnf_cost:
            return cnf_size(m_cost_bdd);
        case dnf_cost:
            return dnf_size(m_cost_bdd);
        default:
            UNREACHABLE();
            return 0;
        }
    }

    bool bdd_manager::is_bad_cost(double current_cost, double best_cost) const {
        return current_cost > 1.1 * best_cost;
    }

    void bdd_manager::sift_var(unsigned v) {
        unsigned lvl = m_var2level[v];
        unsigned start = lvl;
        double best_cost = current_cost();
        bool first = true;
        unsigned max_lvl = m_level2nodes.size()-1;
        if (lvl*2 < max_lvl) {
            goto go_down;
        }
    go_up:
        TRACE("bdd", tout << "sift up " << lvl << "\n";);
        while (lvl < max_lvl) {
            sift_up(lvl++);
            double cost = current_cost();
            if (is_bad_cost(cost, best_cost)) break;
            best_cost = std::min(cost, best_cost);
        }
        if (first) {
            first = false;
            while (lvl != start) {
                sift_up(--lvl);
            }
            goto go_down;
        }
        else {
            while (current_cost() != best_cost) {
                sift_up(--lvl);
            }
            return;
        }
    go_down:
        TRACE("bdd", tout << "sift down " << lvl << "\n";);
        while (lvl > 0) {
            sift_up(--lvl);
            double cost = current_cost();
            if (is_bad_cost(cost, best_cost)) break;
            best_cost = std::min(cost, best_cost);
        }
        if (first) {
            first = false;
            while (lvl != start) {
                sift_up(lvl++);
            }
            goto go_up;
        }
        else {
            while (current_cost() != best_cost) {
                sift_up(lvl++);
            }
            return;
        }
    }

    void bdd_manager::sift_up(unsigned lvl) {
        if (m_level2nodes[lvl].empty()) return;
        // SASSERT(well_formed());
        // exchange level and level + 1.
        m_S.reset();
        m_T.reset();
        m_to_free.reset();
        m_disable_gc = true;

        for (unsigned n : m_level2nodes[lvl + 1]) {
            BDD l = lo(n);
            BDD h = hi(n);
            if (l == 0 && h == 0) continue;
            if ((is_const(l) || level(l) != lvl) &&
                (is_const(h) || level(h) != lvl)) {
                m_S.push_back(n);
            }
            else {
                reorder_decref(l);            
                reorder_decref(h);            
                m_T.push_back(n);
            }
            TRACE("bdd", tout << "remove " << n << "\n";);
            m_node_table.remove(m_nodes[n]);
        }
        m_level2nodes[lvl + 1].reset();
        m_level2nodes[lvl + 1].append(m_T);

        for (unsigned n : m_level2nodes[lvl]) {
            bdd_node& node = m_nodes[n];
            m_node_table.remove(node);
            node.m_level = lvl + 1;
            if (m_reorder_rc[n] == 0) {
                m_to_free.push_back(n);
            }
            else {
                TRACE("bdd", tout << "set level " << n << " to " << lvl + 1 << "\n";);
                m_node_table.insert(node);
                m_level2nodes[lvl + 1].push_back(n);
            }
        }
        m_level2nodes[lvl].reset();
        m_level2nodes[lvl].append(m_S);
    
        for (unsigned n : m_S) {
            m_nodes[n].m_level = lvl;
            m_node_table.insert(m_nodes[n]);
        }

        for (unsigned n : m_T) {
            BDD l = lo(n);
            BDD h = hi(n);
            if (l == 0 && h == 0) continue;
            BDD a, b, c, d;
            if (level(l) == lvl + 1) { 
                a = lo(l);
                b = hi(l);
            }
            else {
                a = b = l;
            }
            if (level(h) == lvl + 1) { 
                c = lo(h);
                d = hi(h);
            }
            else {
                c = d = h;
            }

            unsigned ac = make_node(lvl, a, c);
            if (is_new_node()) {
                m_level2nodes[lvl].push_back(ac);
                m_reorder_rc.reserve(ac+1);
                reorder_incref(a);
                reorder_incref(c);
            }
            unsigned bd = make_node(lvl, b, d);
            if (is_new_node()) {
                m_level2nodes[lvl].push_back(bd);
                m_reorder_rc.reserve(bd+1);
                reorder_incref(b);
                reorder_incref(d);
            }
            m_nodes[n].m_lo = ac;
            m_nodes[n].m_hi = bd;
            reorder_incref(ac);
            reorder_incref(bd);
            TRACE("bdd", tout << "transform " << n << " " << " " << a << " " << b << " " << c << " " << d << " " << ac << " " << bd << "\n";);
            m_node_table.insert(m_nodes[n]);
        }
        unsigned v = m_level2var[lvl];
        unsigned w = m_level2var[lvl+1];
        std::swap(m_level2var[lvl], m_level2var[lvl+1]);
        std::swap(m_var2level[v], m_var2level[w]);
        m_disable_gc = false;

        // add orphaned nodes to free-list
        for (unsigned i = 0; i < m_to_free.size(); ++i) {
            unsigned n = m_to_free[i];
            bdd_node& node = m_nodes[n];
            if (!node.is_internal()) {
                SASSERT(!m_free_nodes.contains(n));
                SASSERT(node.m_refcount == 0);
                m_free_nodes.push_back(n);
                m_node_table.remove(node);
                BDD l = lo(n);
                BDD h = hi(n);
                node.set_internal();

                reorder_decref(l);
                if (!m_nodes[l].is_internal() && m_reorder_rc[l] == 0) {
                    m_to_free.push_back(l);
                }
                reorder_decref(h);
                if (!m_nodes[h].is_internal() && m_reorder_rc[h] == 0) {
                    m_to_free.push_back(h);
                }
            }
        }
        TRACE("bdd", tout << "sift " << lvl << "\n"; display(tout); );
        DEBUG_CODE(
            for (unsigned i = 0; i < m_level2nodes.size(); ++i) {
                for (unsigned n : m_level2nodes[i]) {
                    bdd_node const& node = m_nodes[n];
                    SASSERT(node.m_level == i);
                }
            });
        
        TRACE("bdd", 
              for (unsigned i = 0; i < m_nodes.size(); ++i) {
                if (m_reorder_rc[i] != 0) {
                    tout << i << " " << m_reorder_rc[i] << "\n";
                }});
        
        // SASSERT(well_formed());
    }

    void bdd_manager::init_reorder() {
        m_level2nodes.reset();
        unsigned sz = m_nodes.size();
        m_reorder_rc.fill(sz, 0);
        for (unsigned i = 0; i < sz; ++i) {
            if (m_nodes[i].m_refcount > 0) 
                m_reorder_rc[i] = UINT_MAX;
        }
        for (unsigned i = 0; i < sz; ++i) {
            bdd_node const& n = m_nodes[i];
            if (n.is_internal()) continue;
            unsigned lvl = n.m_level;
            SASSERT(i == m_nodes[i].m_index);
            m_level2nodes.reserve(lvl + 1);
            m_level2nodes[lvl].push_back(i);
            reorder_incref(n.m_lo);
            reorder_incref(n.m_hi);
        }
        TRACE("bdd",
              display(tout);
              for (unsigned i = 0; i < sz; ++i) {
                  bdd_node const& n = m_nodes[i];
                  if (n.is_internal()) continue;
                  unsigned lvl = n.m_level;
                  tout << i << " lvl: " << lvl << " rc: " << m_reorder_rc[i] << " lo " << n.m_lo << " hi " << n.m_hi << "\n";
              }
              );
    }

    void bdd_manager::reorder_incref(unsigned n) {
        if (m_reorder_rc[n] != UINT_MAX) m_reorder_rc[n]++;
    }

    void bdd_manager::reorder_decref(unsigned n) {
        if (m_reorder_rc[n] != UINT_MAX) m_reorder_rc[n]--;
    }

    void bdd_manager::reserve_var(unsigned i) {
        while (m_var2level.size() <= i) {
            unsigned v = m_var2level.size();
            m_var2bdd.push_back(make_node(v, false_bdd, true_bdd));
            m_var2bdd.push_back(make_node(v, true_bdd, false_bdd));
            m_nodes[m_var2bdd[2*v]].m_refcount = max_rc;
            m_nodes[m_var2bdd[2*v+1]].m_refcount = max_rc;
            m_var2level.push_back(v);
            m_level2var.push_back(v);
        }
    }

    bdd bdd_manager::mk_var(unsigned i) {
        reserve_var(i);
        return bdd(m_var2bdd[2*i], this);        
    }

    bdd bdd_manager::mk_nvar(unsigned i) {
        reserve_var(i);
        return bdd(m_var2bdd[2*i+1], this);
    }

    bdd bdd_manager::mk_not(bdd b) {
        bool first = true;
        while (true) {
            try {
                return bdd(mk_not_rec(b.root), this);
            }
            catch (mem_out) {
                try_reorder();
                if (!first) throw;
                first = false;
            }
        }
    }

    bdd_manager::BDD bdd_manager::mk_not_rec(BDD b) {
        if (is_true(b)) return false_bdd;
        if (is_false(b)) return true_bdd;
        op_entry* e1 = pop_entry(b, b, bdd_not_op);
        op_entry const* e2 = m_op_cache.insert_if_not_there(e1);
        if (check_result(e1, e2, b, b, bdd_not_op)) 
            return e2->m_result;
        push(mk_not_rec(lo(b)));
        push(mk_not_rec(hi(b)));
        BDD r = make_node(level(b), read(2), read(1));
        pop(2);
        e1->m_result = r;
        return r;
    }
    
    bdd bdd_manager::mk_ite(bdd const& c, bdd const& t, bdd const& e) {         
        bool first = true;
        while (true) {
            try {
                return bdd(mk_ite_rec(c.root, t.root, e.root), this); 
            }
            catch (mem_out) {
                try_reorder();
                if (!first) throw;
                first = false;
            }
        }
    }

    bdd_manager::BDD bdd_manager::mk_ite_rec(BDD a, BDD b, BDD c) {
        if (is_true(a)) return b;
        if (is_false(a)) return c;
        if (b == c) return b;
        if (is_true(b)) return apply(a, c, bdd_or_op);
        if (is_false(c)) return apply(a, b, bdd_and_op);
        if (is_false(b)) return apply(mk_not_rec(a), c, bdd_and_op);
        if (is_true(c)) return apply(mk_not_rec(a), b, bdd_or_op);
        SASSERT(!is_const(a) && !is_const(b) && !is_const(c));
        op_entry * e1 = pop_entry(a, b, c);
        op_entry const* e2 = m_op_cache.insert_if_not_there(e1);
        if (check_result(e1, e2, a, b, c)) 
            return e2->m_result;
        unsigned la = level(a), lb = level(b), lc = level(c);
        BDD r;
        BDD a1, b1, c1, a2, b2, c2;
        unsigned lvl = la;
        if (la >= lb && la >= lc) {
            a1 = lo(a), a2 = hi(a);
            lvl = la;
        }
        else {
            a1 = a, a2 = a;
        }
        if (lb >= la && lb >= lc) {
            b1 = lo(b), b2 = hi(b);
            lvl = lb;
        }
        else {
            b1 = b, b2 = b;
        }
        if (lc >= la && lc >= lb) {
            c1 = lo(c), c2 = hi(c);
            lvl = lc;
        }
        else {
            c1 = c, c2 = c;
        }
        push(mk_ite_rec(a1, b1, c1));
        push(mk_ite_rec(a2, b2, c2));
        r = make_node(lvl, read(2), read(1));
        pop(2);          
        e1->m_result = r;
        return r;
    }

    bdd bdd_manager::mk_exists(unsigned n, unsigned const* vars, bdd const& b) {
        // SASSERT(well_formed());
        return bdd(mk_quant(n, vars, b.root, bdd_or_op), this);
    }

    bdd bdd_manager::mk_forall(unsigned n, unsigned const* vars, bdd const& b) {
        return bdd(mk_quant(n, vars, b.root, bdd_and_op), this);
    }

    bdd_manager::BDD bdd_manager::mk_quant(unsigned n, unsigned const* vars, BDD b, bdd_op op) {
        BDD result = b;
        for (unsigned i = 0; i < n; ++i) {
            result = mk_quant_rec(m_var2level[vars[i]], result, op);
        }
        return result;
    }

    bdd_manager::BDD bdd_manager::mk_quant_rec(unsigned l, BDD b, bdd_op op) {
        unsigned lvl = level(b);
        BDD r;
        if (is_const(b)) {
            r = b;
        }
        else if (lvl == l) {
            r = apply(lo(b), hi(b), op);
        }
        else if (lvl < l) {
            r = b;
        }
        else {
            BDD a = level2bdd(l);
            bdd_op q_op = op == bdd_and_op ? bdd_and_proj_op : bdd_or_proj_op;
            op_entry * e1 = pop_entry(a, b, q_op);
            op_entry const* e2 = m_op_cache.insert_if_not_there(e1);
            if (check_result(e1, e2, a, b, q_op)) {
                r = e2->m_result;
            }
            else {
                SASSERT(e1->m_result == -1);
                push(mk_quant_rec(l, lo(b), op));
                push(mk_quant_rec(l, hi(b), op));
                r = make_node(lvl, read(2), read(1));
                pop(2);
                e1->m_result = r;
            }
        }
        SASSERT(r != UINT_MAX);
        return r;
    }

    double bdd_manager::count(BDD b, unsigned z) {
        init_mark();
        m_count.resize(m_nodes.size());
        m_count[0] = z;
        m_count[1] = 1-z;
        set_mark(0);
        set_mark(1);
        m_todo.push_back(b);
        while (!m_todo.empty()) {
            BDD r = m_todo.back();
            if (is_marked(r)) {
                m_todo.pop_back();
            }
            else if (!is_marked(lo(r))) {
                SASSERT (is_const(r) || r != lo(r));
                m_todo.push_back(lo(r));
            }
            else if (!is_marked(hi(r))) {
                SASSERT (is_const(r) || r != hi(r));
                m_todo.push_back(hi(r));
            }
            else {
                m_count[r] = m_count[lo(r)] + m_count[hi(r)];
                set_mark(r);
                m_todo.pop_back();
            }
        }
        return m_count[b];
    }

    unsigned bdd_manager::bdd_size(bdd const& b) {
        init_mark();
        set_mark(0);
        set_mark(1);
        unsigned sz = 0;
        m_todo.push_back(b.root);
        while (!m_todo.empty()) {
            BDD r = m_todo.back();
            m_todo.pop_back();
            if (!is_marked(r)) {
                ++sz;
                set_mark(r);
                if (!is_marked(lo(r))) {
                    m_todo.push_back(lo(r));
                }
                if (!is_marked(hi(r))) {
                    m_todo.push_back(hi(r));
                }
            }
        }
        return sz;
    }

    void bdd_manager::alloc_free_nodes(unsigned n) {
        for (unsigned i = 0; i < n; ++i) {
            m_free_nodes.push_back(m_nodes.size());
            m_nodes.push_back(bdd_node());
            m_nodes.back().m_index = m_nodes.size() - 1;
        }
        m_free_nodes.reverse();
    }

    void bdd_manager::gc() {
        m_free_nodes.reset();
        IF_VERBOSE(13, verbose_stream() << "(bdd :gc " << m_nodes.size() << ")\n";);
        svector<bool> reachable(m_nodes.size(), false);
        for (unsigned i = m_bdd_stack.size(); i-- > 0; ) {
            reachable[m_bdd_stack[i]] = true;
            m_todo.push_back(m_bdd_stack[i]);
        }
        for (unsigned i = m_nodes.size(); i-- > 2; ) {
            if (m_nodes[i].m_refcount > 0) {
                reachable[i] = true;
                m_todo.push_back(i);
            }
        }
        while (!m_todo.empty()) {
            BDD b = m_todo.back();
            m_todo.pop_back();
            SASSERT(reachable[b]);
            if (is_const(b)) continue;
            if (!reachable[lo(b)]) {
                reachable[lo(b)] = true;
                m_todo.push_back(lo(b));
            }
            if (!reachable[hi(b)]) {
                reachable[hi(b)] = true;
                m_todo.push_back(hi(b));
            }
        }
        for (unsigned i = m_nodes.size(); i-- > 2; ) {
            if (!reachable[i]) {
                m_nodes[i].set_internal();
                SASSERT(m_nodes[i].m_refcount == 0);
                m_free_nodes.push_back(i);                
            }
        }
        // sort free nodes so that adjacent nodes are picked in order of use
        std::sort(m_free_nodes.begin(), m_free_nodes.end());
        m_free_nodes.reverse();

        ptr_vector<op_entry> to_delete, to_keep;
        for (auto* e : m_op_cache) {            
            if (e->m_result != -1) {
                to_delete.push_back(e);
            }
            else {
                to_keep.push_back(e);
            }
        }
        m_op_cache.reset();
        for (op_entry* e : to_delete) {
            m_alloc.deallocate(sizeof(*e), e);
        }
        for (op_entry* e : to_keep) {
            m_op_cache.insert(e);
        }

        m_node_table.reset();
        // re-populate node cache
        for (unsigned i = m_nodes.size(); i-- > 2; ) {
            if (reachable[i]) {
                SASSERT(m_nodes[i].m_index == i);
                m_node_table.insert(m_nodes[i]);
            }
        }
        SASSERT(well_formed());
    }

    void bdd_manager::init_mark() {
        m_mark.resize(m_nodes.size());
        ++m_mark_level;
        if (m_mark_level == 0) {
            m_mark.fill(0);
            ++m_mark_level;
        }
    }

    std::ostream& bdd_manager::display(std::ostream& out, bdd const& b) {
        init_mark();
        m_todo.push_back(b.root);
        m_reorder_rc.reserve(m_nodes.size());
        while (!m_todo.empty()) {
            BDD r = m_todo.back();
            if (is_marked(r)) {
                m_todo.pop_back();
            }
            else if (lo(r) == 0 && hi(r) == 0) {
                set_mark(r);
                m_todo.pop_back();
            }
            else if (!is_marked(lo(r))) {
                m_todo.push_back(lo(r));
            }
            else if (!is_marked(hi(r))) {
                m_todo.push_back(hi(r));
            }
            else {
                out << r << " : " << var(r) << " @ " << level(r) << " " << lo(r) << " " << hi(r) << " " << m_reorder_rc[r] << "\n";
                set_mark(r);
                m_todo.pop_back();
            }
        }
        return out;
    }

    bool bdd_manager::well_formed() {
        bool ok = true;
        for (unsigned n : m_free_nodes) {
            ok &= (lo(n) == 0 && hi(n) == 0 && m_nodes[n].m_refcount == 0);
            if (!ok) {
                IF_VERBOSE(0, 
                           verbose_stream() << "free node is not internal " << n << " " << lo(n) << " " << hi(n) << " " << m_nodes[n].m_refcount << "\n";
                           display(verbose_stream()););
                UNREACHABLE();
                return false;
            }
        }
        for (bdd_node const& n : m_nodes) {
            if (n.is_internal()) continue;
            unsigned lvl = n.m_level;
            BDD lo = n.m_lo;
            BDD hi = n.m_hi;
            ok &= is_const(lo) || level(lo) < lvl;
            ok &= is_const(hi) || level(hi) < lvl;
            ok &= is_const(lo) || !m_nodes[lo].is_internal();
            ok &= is_const(hi) || !m_nodes[hi].is_internal();
            if (!ok) {
                IF_VERBOSE(0, display(verbose_stream() << n.m_index << " lo " << lo << " hi " << hi << "\n"););
                UNREACHABLE();
                return false;
            }
        }
        return ok;
    }

    std::ostream& bdd_manager::display(std::ostream& out) {
        m_reorder_rc.reserve(m_nodes.size());
        for (unsigned i = 0; i < m_nodes.size(); ++i) {
            bdd_node const& n = m_nodes[i];
            if (n.is_internal()) continue;
            out << i << " : v" << m_level2var[n.m_level] << " " << n.m_lo << " " << n.m_hi << " rc " << m_reorder_rc[i] << "\n";
        }
        for (unsigned i = 0; i < m_level2nodes.size(); ++i) {
            out << "level: " << i << " : " << m_level2nodes[i] << "\n";
        }
        return out;
    }

    bdd& bdd::operator=(bdd const& other) { unsigned r1 = root; root = other.root; m->inc_ref(root); m->dec_ref(r1); return *this; }
    std::ostream& operator<<(std::ostream& out, bdd const& b) { return b.display(out); }

}
