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

    bdd_manager::bdd_manager(unsigned num_vars) {
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
        
        // add variables
        for (unsigned i = 0; i < num_vars; ++i) {
            m_var2bdd.push_back(make_node(i, false_bdd, true_bdd));
            m_var2bdd.push_back(make_node(i, true_bdd, false_bdd));
            m_nodes[m_var2bdd[2*i]].m_refcount = max_rc;
            m_nodes[m_var2bdd[2*i+1]].m_refcount = max_rc;
            m_var2level.push_back(i);
            m_level2var.push_back(i);
        }            
    }

    bdd_manager::~bdd_manager() {
        if (m_spare_entry) {
            m_alloc.deallocate(sizeof(*m_spare_entry), m_spare_entry);
        }
        for (auto* e : m_op_cache) {
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
        case bdd_iff_op:
            return (a == b) ? true_bdd : false_bdd;
        default:
            return false_bdd;
        }
    }

    bdd_manager::BDD bdd_manager::apply(BDD arg1, BDD arg2, bdd_op op) {
        bool first = true;
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
    }


    bdd bdd_manager::mk_true() { return bdd(true_bdd, this); }
    bdd bdd_manager::mk_false() { return bdd(false_bdd, this); }
    bdd bdd_manager::mk_and(bdd const& a, bdd const& b) { return bdd(apply(a.root, b.root, bdd_and_op), this); }
    bdd bdd_manager::mk_or(bdd const& a, bdd const& b) { return bdd(apply(a.root, b.root, bdd_or_op), this); }
    bdd bdd_manager::mk_iff(bdd const& a, bdd const& b) { return bdd(apply(a.root, b.root, bdd_iff_op), this); }
    bdd bdd_manager::mk_exists(unsigned v, bdd const& b) { return mk_exists(1, &v, b); }
    bdd bdd_manager::mk_forall(unsigned v, bdd const& b) { return mk_forall(1, &v, b); }


    bool bdd_manager::check_result(op_entry*& e1, op_entry const* e2, BDD a, BDD b, BDD c) {
        if (e1 != e2) {
            push_entry(e1);
            if (e2->m_bdd1 == a && e2->m_bdd2 == b && e2->m_op == c) {
                return true;
            }
            e1 = const_cast<op_entry*>(e2);
        }
        e1->m_bdd1 = a;
        e1->m_bdd2 = b;
        e1->m_op = c;
        return false;        
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
        op_entry * e1 = pop_entry(a, b, op);
        op_entry const* e2 = m_op_cache.insert_if_not_there(e1);
        if (check_result(e1, e2, a, b, op)) {
            return e2->m_result;
        }
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

    bdd_manager::BDD bdd_manager::make_node(unsigned level, BDD l, BDD r) {
        if (l == r) {
            return l;
        }

        bdd_node n(level, l, r);
        node_table::entry* e = m_node_table.insert_if_not_there2(n);
        if (e->get_data().m_index != 0) {
            return e->get_data().m_index;
        }
        e->get_data().m_refcount = 0;
        bool do_gc = m_free_nodes.empty();
        if (do_gc) {
            gc();
            e = m_node_table.insert_if_not_there2(n);
            e->get_data().m_refcount = 0;
        }
        if (do_gc && m_free_nodes.size()*3 < m_nodes.size()) {
            if (m_nodes.size() > m_max_num_bdd_nodes) {
                throw mem_out();
            }
            e->get_data().m_index = m_nodes.size();
            m_nodes.push_back(e->get_data());
            alloc_free_nodes(m_nodes.size()/2);
        }
        else {
            e->get_data().m_index = m_free_nodes.back();
            m_nodes[e->get_data().m_index] = e->get_data();
            m_free_nodes.pop_back();
        }
        return e->get_data().m_index;
    }

    void bdd_manager::try_reorder() {
        // TBD
    }

    void bdd_manager::sift_up(unsigned level) {
        // exchange level and level + 1.
        
    }

    bdd bdd_manager::mk_var(unsigned i) {
        return bdd(m_var2bdd[2*i], this);        
    }

    bdd bdd_manager::mk_nvar(unsigned i) {
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
            if (check_result(e1, e2, a, b, q_op)) 
                r = e2->m_result;
            else {
                push(mk_quant_rec(l, lo(b), op));
                push(mk_quant_rec(l, hi(b), op));
                r = make_node(lvl, read(2), read(1));
                pop(2);
                e1->m_result = r;
            }
        }
        return r;
    }

    double bdd_manager::count(bdd const& b, unsigned z) {
        init_mark();
        m_count.resize(m_nodes.size());
        m_count[0] = z;
        m_count[1] = 1-z;
        set_mark(0);
        set_mark(1);
        m_todo.push_back(b.root);
        while (!m_todo.empty()) {
            BDD r = m_todo.back();
            if (is_marked(r)) {
                m_todo.pop_back();
            }
            else if (!is_marked(lo(r))) {
                m_todo.push_back(lo(r));
            }
            else if (!is_marked(hi(r))) {
                m_todo.push_back(hi(r));
            }
            else {
                m_count[r] = m_count[lo(r)] + m_count[hi(r)];
                set_mark(r);
                m_todo.pop_back();
            }
        }
        return m_count[b.root];
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
        IF_VERBOSE(3, verbose_stream() << "(bdd :gc " << m_nodes.size() << ")\n";);
        SASSERT(m_free_nodes.empty());
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
                m_free_nodes.push_back(i);                
            }
        }
        for (auto* e : m_op_cache) {
            m_alloc.deallocate(sizeof(*e), e);
        }
        m_op_cache.reset();
        m_node_table.reset();
        // re-populate node cache
        for (unsigned i = m_nodes.size(); i-- > 2; ) {
            if (reachable[i]) {
                SASSERT(m_nodes[i].m_index == i);
                m_node_table.insert(m_nodes[i]);
            }
        }
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
                out << r << " : " << var(r) << " " << lo(r) << " " << hi(r) << "\n";
                set_mark(r);
                m_todo.pop_back();
            }
        }
        return out;
    }

    std::ostream& bdd_manager::display(std::ostream& out) {
        for (unsigned i = 0; i < m_nodes.size(); ++i) {
            bdd_node const& n = m_nodes[i];
            if (n.m_lo == 0 && n.m_hi == 0) continue;
            out << i << " : " << m_level2var[n.m_level] << " " << n.m_lo << " " << n.m_hi << "\n";
        }
        return out;
    }

    bdd::bdd(unsigned root, bdd_manager* m): root(root), m(m) { m->inc_ref(root); }
    bdd::bdd(bdd & other): root(other.root), m(other.m) { m->inc_ref(root); }
    bdd::bdd(bdd && other): root(0), m(other.m) { std::swap(root, other.root); }
    bdd::~bdd() { m->dec_ref(root); }
    bdd bdd::lo() const { return bdd(m->lo(root), m); }
    bdd bdd::hi() const { return bdd(m->hi(root), m); }
    unsigned bdd::var() const { return m->var(root); }
    bool bdd::is_true() const { return root == bdd_manager::true_bdd; }
    bool bdd::is_false() const { return root == bdd_manager::false_bdd; }
    bdd bdd::operator!() { return m->mk_not(*this); }
    bdd bdd::operator&&(bdd const& other) { return m->mk_and(*this, other); }
    bdd bdd::operator||(bdd const& other) { return m->mk_or(*this, other); }
    bdd& bdd::operator=(bdd const& other) { unsigned r1 = root; root = other.root; m->inc_ref(root); m->dec_ref(r1); return *this; }
    std::ostream& bdd::display(std::ostream& out) const { return m->display(out, *this); }
    std::ostream& operator<<(std::ostream& out, bdd const& b) { return b.display(out); }
    double bdd::cnf_size() const { return m->cnf_size(*this); }
    double bdd::dnf_size() const { return m->dnf_size(*this); }

}
