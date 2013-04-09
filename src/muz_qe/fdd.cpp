/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    fdd.cpp

Abstract:

    Finite decision diagram trie.

Author:

    Nikolaj Bjorner (nbjorner) 2013-07-03.

Revision History:

 
--*/

#include "fdd.h"
#include "hash.h"
#include "bit_vector.h"
#include "trace.h"

#define OFFSET_OF(th, ty, field) (unsigned char*)(&((ty*)(th))->field) - (unsigned char*)(ty*)(th)

using namespace fdd;

unsigned node::get_hash() const {
    return string_hash((char*)this, static_cast<unsigned>(OFFSET_OF(this, node, m_ref_count)), 11);
}

bool node::operator==(node const& other) const {
    return 
        m_var == other.m_var &&
        m_lo == other.m_lo &&
        m_hi == other.m_hi;
}


// ------------------------------------------
// manager

manager::manager() :
    m_alloc_node(2),  
    m_false(0),
    m_true(1),
    m_root(m_false)
{
    m_nodes.push_back(node()); // false
    m_nodes.push_back(node()); // true
    inc_ref(m_false);
    inc_ref(m_true);
    alloc_node(); // pre-allocate a node.
}

manager::~manager() {
}

void manager::alloc_node() {
    unsigned index;
    while (!m_free.empty()) {
        index = m_free.back();
        node& n = m_nodes[index];
        m_free.pop_back();
        if (n.get_ref_count() == 0) {                
            if (!is_leaf(n.lo())) {
                m_free.push_back(n.lo());
            }
            if (!is_leaf(n.hi())) {
                m_free.push_back(n.hi());
            }
            m_alloc_node = index;
            m_table.erase(n);
            return;
        }
    }
    index = m_nodes.size();
    m_nodes.push_back(node());
    m_alloc_node = index;
}

node_id manager::mk_node(unsigned var, node_id lo, node_id hi) {
    if (lo == hi) {
        return lo;
    }
    node n(var, lo, hi);    
    unsigned index = m_alloc_node;

    node_id result = m_table.insert_if_not_there(n, index).m_value;

    if (result == index) {
        alloc_node();
        m_nodes[result] = n;
        inc_ref(lo);
        inc_ref(hi);
    }
    
    TRACE("fdd", tout << "mk_node: " << var << " " << lo << " " << hi << " -> " << result << "\n";);

    return result;
}


void manager::inc_ref(node_id n) {
    TRACE("fdd", tout << "incref: " << n << "\n";);
    if (!is_leaf(n)) {
        m_nodes[n].inc_ref();
    }
}

void manager::dec_ref(node_id n) {
    if (!is_leaf(n) && 0 == m_nodes[n].dec_ref()) {
        m_free.push_back(n);
    }
}

void manager::setup_keys(Key const* keys) {
    for (unsigned i = 0; i < m_num_keys; ++i) {
        m_keys[i] = (uint64)keys[i];
        m_sign[i] = keys[i] < 0;
    }

}

void manager::insert(Key const* keys) {
    setup_keys(keys);
    m_insert_cache.reset();
    node_id result = insert_sign(m_num_idx + m_num_keys, m_root);
    inc_ref(result);
    dec_ref(m_root);
    m_root = result;
}

node_id manager::insert_sign(unsigned idx, node_id n) {
    if (idx > m_num_idx) {
        --idx;
        bool s = idx2sign(idx);
        node nd = m_nodes[n];
        if (!is_leaf(n) && nd.var() == idx) {
            if (s) {
                return mk_node(idx, insert_sign(idx, nd.lo()), nd.hi());
            }
            else {
                return mk_node(idx, nd.lo(), insert_sign(idx, nd.hi()));
            }
        }
        else {
            if (s) {
                return mk_node(idx, insert_sign(idx, n), n);
            }
            else {
                return mk_node(idx, n, insert_sign(idx, n));
            }
        }
    }
    SASSERT(m_num_idx == idx);
    return insert(idx, n);
}

node_id manager::insert(unsigned idx, node_id n) {
    node_id result;
    SASSERT(0 <= idx && idx <= m_num_idx);
    TRACE("fdd", tout << "insert: " << idx << " " << n << "\n";);
    if (is_leaf(n)) {
        while (idx > 0) {
            --idx;
            if (idx2bit(idx) && !is_dont_care(idx2key(idx))) {
                return mk_node(idx, n, insert(idx, n));
            }
        }
        return m_true;
    }

    SASSERT(0 < idx);
    --idx;

    config c(m_dont_cares, idx, n);
    if (m_insert_cache.find(c, result)) {
        return result;
    }

    node nd = m_nodes[n];
    SASSERT(idx >= nd.var());
    while (idx > nd.var()) {
        if (idx2bit(idx) && !is_dont_care(idx2key(idx))) {
            return mk_node(idx, n, insert(idx, n));
        }
        --idx;
    }
    SASSERT(nd.var() == idx);
    unsigned key = idx2key(idx);
    if (is_dont_care(key)) {
        result = mk_node(idx, insert(idx, nd.lo()), insert(idx, nd.hi()));
    }
    else {
        bool bit = idx2bit(idx);
        node_id lo, hi;
        if (bit) {
            hi = insert(idx, nd.hi());
            lo = nd.lo();
        }
        else {
            lo = insert(idx, nd.lo());
            scoped_dont_cares _set(*this, key);
            hi = insert(idx, nd.hi());
        }
        result = mk_node(idx, lo, hi);
    }
    m_insert_cache.insert(c, result);
    return result;
}

void manager::set_dont_care(unsigned key) {
    SASSERT(!is_dont_care(key));
    m_dont_cares |= (1ull << key);
}

void manager::unset_dont_care(unsigned key) {
    m_dont_cares &= ~(1ull << key);
}

bool manager::is_dont_care(unsigned key) const {
    return 0 != (m_dont_cares & (1ull << key));
}

void manager::collect_statistics(statistics& st) const {
    st.update("fdd.num_nodes", m_nodes.size());
}
        

void manager::reset(unsigned num_keys) {
    m_num_keys = num_keys;
    m_num_idx  = m_num_keys * m_num_bits;
    m_dont_cares = 0;
    m_sign.resize(num_keys);
    m_keys.resize(num_keys);
    SASSERT(num_keys <= 8*sizeof(m_dont_cares));
}



bool manager::find_le(Key const* keys) {
    setup_keys(keys);
    unsigned idx = m_num_idx + m_num_keys;
    node_id n = m_root;
    node nc = m_nodes[n];
    while (n > 1 && idx > m_num_idx) {
        --idx;
        if (nc.var() == idx) {
            if (idx2sign(idx)) {
                n = nc.lo();
            }
            else {
                n = nc.hi();
            }
            nc = m_nodes[n];
        }        
    }
    while (n > 1) {
        SASSERT(idx > 0);
        --idx;
        while (nc.var() < idx) {
            if (idx2bit(idx) && is_dont_care(idx2key(idx))) {
                set_dont_care(idx2key(idx));
            }
            --idx;
        }
        SASSERT(nc.var() == idx);
        if (is_dont_care(idx2key(idx)) || idx2bit(idx)) {
            n = nc.hi();
        }
        else {
            n = nc.lo();
        }
        nc = m_nodes[n];
    }
    m_dont_cares = 0;
    return n == 1;
}


std::ostream& manager::display(std::ostream& out, node_id n) const{
    svector<bool> mark;
    svector<node_id> nodes;
    nodes.push_back(n);
    while (!nodes.empty()) {
        n = nodes.back();
        nodes.pop_back();
        if (mark.size() <= n) {
            mark.resize(n+1, false);
        }
        node const& nc = m_nodes[n];
        if (is_leaf(n) || mark[n]) {
            continue;
        }
        nodes.push_back(nc.lo());
        nodes.push_back(nc.hi());
        mark[n] = true;

        if (nc.var() >= m_num_idx) {
            out << n << " if " << idx2key(nc.var()) << " then " << nc.hi() << " else " << nc.lo() << "\n";
        }
        else {
            out << n << " if " << idx2key(nc.var()) << ":" << idx2bitnum(nc.var()) << " then " << nc.hi() << " else " << nc.lo() << "\n";
        }
    }
    return out;
}

