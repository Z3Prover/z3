/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    fdd.h

Abstract:

    Finite decision diagram.

Author:

    Nikolaj Bjorner (nbjorner) 2013-07-03.

Revision History:


--*/

#ifndef __FDD_H__
#define __FDD_H__

#include "hashtable.h"
#include "hash.h"
#include "map.h"
#include "vector.h"
#include "statistics.h"

namespace fdd {


    typedef unsigned node_id;

    class node {
        unsigned   m_var;
        node_id    m_lo;
        node_id    m_hi;
        unsigned   m_ref_count;
        void reset();
    public:
        node() : m_var(0), m_lo(0), m_hi(0), m_ref_count(0) {}
        node(unsigned var, node_id l, node_id h): m_var(var), m_lo(l), m_hi(h), m_ref_count(0) {}

        unsigned get_hash() const;        
        bool operator==(node const& other) const;

        void inc_ref()     { ++m_ref_count; }
        unsigned dec_ref() { return --m_ref_count; }
	unsigned get_ref_count() const { return m_ref_count; }
        node_id lo()   const { return m_lo; }
        node_id hi()   const { return m_hi; }
        unsigned var() const { return m_var; }
    
        struct hash { unsigned operator()(node const& n) const { return n.get_hash(); } };
        struct eq { bool operator()(node const& l, node const& r) const { return l == r; } };
        std::ostream& display(std::ostream& out) const { return out << m_var << " " << m_lo << " " << m_hi << ""; }
    };

    inline std::ostream& operator<<(std::ostream& out, node const& n) { return n.display(out); }

    class config {
        uint64   m_dont_cares;
        unsigned m_idx;
        node_id  m_node;        
    public:

        config(): m_dont_cares(0), m_idx(0), m_node(0) {}

        config(uint64 dont_cares, unsigned idx, node_id n):
            m_dont_cares(dont_cares),
            m_idx(idx),
            m_node(n)
        {}

        struct hash {
            unsigned operator()(config const& c) const {
                return string_hash((char*)&c, sizeof(c), 12);
            };
        };

        struct eq {
            bool operator()(config const& a, config const& b) const {
                return 
                    a.m_dont_cares == b.m_dont_cares &&
                    a.m_idx == b.m_idx &&
                    a.m_node == b.m_node;
            }
        };
    };

			
    class manager {
    public:
        typedef int64 Key;
        typedef node::hash node_hash;
        typedef node::eq node_eq;
        typedef config::hash config_hash;
        typedef config::eq config_eq;
    private:
        typedef map<node, unsigned, node_hash, node_eq>      node_table;
        typedef map<config, node_id, config_hash, config_eq> insert_cache;
        node_table             m_table;
        insert_cache           m_insert_cache;
        svector<node>          m_nodes;
        unsigned_vector        m_free;
        unsigned               m_alloc_node;
        node_id                m_false;  
        node_id                m_true; 
        node_id                m_root;

        static const unsigned  m_num_bits = 64;
        unsigned               m_num_keys;
        unsigned               m_num_idx; // = m_num_keys * m_num_bits

        // state associated with insert.
        svector<uint64>        m_keys;
        svector<bool>          m_sign;

        uint64                 m_dont_cares;

    public:
        manager();        
        ~manager();                

        void reset(unsigned num_keys);

        void insert(Key const* keys);

        bool find_le(Key const* keys);        

        void collect_statistics(statistics& st) const;
        void reset_statistics() {}
        unsigned size() const { return m_nodes.size(); }    
    
        void display(std::ostream& out) const { display(out, m_root); }

    private:                
        void dec_ref(node_id n);        
        void inc_ref(node_id n);
        node_id mk_node(unsigned var, node_id lo, node_id hi);                            
        inline unsigned get_ref_count(node_id n) { return m_nodes[n].get_ref_count(); }

        std::ostream& display(std::ostream& out, node_id n) const;

        void setup_keys(Key const* keys);
        node_id insert(unsigned idx, node_id n);
        node_id insert_sign(unsigned idx, node_id n);
        bool is_dont_care(unsigned idx) const;

        void set_dont_care(unsigned key);
        void unset_dont_care(unsigned key);

        struct scoped_dont_cares {
            manager& m;
            unsigned m_key;
            scoped_dont_cares(manager& m, unsigned key):m(m), m_key(key) { m.set_dont_care(key); }
            ~scoped_dont_cares() { m.unset_dont_care(m_key); }
        };

        void alloc_node();

        unsigned idx2key(unsigned i) const { return i % m_num_keys; }
        unsigned idx2bitnum(unsigned i) const { SASSERT(i < m_num_idx); return (i / m_num_keys); }
        bool idx2bit(unsigned i) const { return 0 != (m_keys[idx2key(i)] & (1LL << idx2bitnum(i))); }
        bool idx2sign(unsigned i) const { return m_sign[idx2key(i)]; }
        
        bool is_leaf(node_id n) const { return n <= 1; }
        
    };
};

#endif
