/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    heap_trie.h

Abstract:

    Heap trie structure.

    Structure that lets you retrieve point-wise smaller entries
    of a tuple. A lookup is to identify entries whose keys
    are point-wise dominated by the lookup key.

Author:

    Nikolaj Bjorner (nbjorner) 2013-02-15.

Notes:

    tries are unordered vectors of keys. This could be enhanced to use either
    heaps or sorting. The problem with using the heap implementation directly is that there is no way to
    retrieve elements less or equal to a key that is not already in the heap.
    If nodes have only a few elements, then this would also be a bloated data-structure to maintain.

    Nodes are not de-allocated. Their reference count indicates if they are valid.
    Possibly, add garbage collection.

    Maintaining sorted ranges for larger domains is another option.

--*/

#ifndef _HEAP_TRIE_H_
#define _HEAP_TRIE_H_

#include "map.h"
#include "vector.h"
#include "statistics.h"


template<typename Key, typename Value>
class heap_trie {

    struct stats {
        unsigned m_num_inserts;
        unsigned m_num_removes;
        unsigned m_num_find_eq;
        unsigned m_num_find_le;
        unsigned m_num_find_le_nodes;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };

    enum node_t { 
        trie_t,
        leaf_t
    };

    class node {
        node_t   m_type;
        unsigned m_ref;
    public:
        node(node_t t): m_type(t), m_ref(0) {}
        virtual ~node() {}
        node_t type() const { return m_type; }
        void inc_ref() { ++m_ref; }
        void dec_ref() { SASSERT(m_ref > 0); --m_ref; }
        unsigned ref_count() const { return m_ref; }
        virtual void display(std::ostream& out, unsigned indent) const = 0;
        virtual unsigned size() const = 0;
    };

    class leaf : public node {
        Value m_value;
    public:
        leaf(): node(leaf_t) {}
        virtual ~leaf() {}
        Value const& get_value() const { return m_value; }
        void set_value(Value const& v) { m_value = v; }
        virtual void display(std::ostream& out, unsigned indent) const {
            out << " value: " << m_value;
        }
        virtual unsigned size() const { return 1; }
    };

    // lean trie node
    class trie : public node {
        vector<std::pair<Key,node*> > m_nodes;
    public:
        trie(): node(trie_t) {}

        virtual ~trie() {
            for (unsigned i = 0; i < m_nodes.size(); ++i) {
                dealloc(m_nodes[i].second);
            }
        }

        node* find_or_insert(Key k, node* n) {
            for (unsigned i = 0; i < m_nodes.size(); ++i) {
                if (m_nodes[i].first == k) {
                    return m_nodes[i].second;
                }
            }
            m_nodes.push_back(std::make_pair(k, n));
            return n;
        }
        
        bool find(Key k, node*& n) const {
            for (unsigned i = 0; i < m_nodes.size(); ++i) {
                if (m_nodes[i].first == k) {
                    n = m_nodes[i].second;
                    return n->ref_count() > 0;
                }
            }
            return false;
        }
        
        // push nodes whose keys are <= key into vector.
        void find_le(Key key, ptr_vector<node>& nodes) {
            for (unsigned i = 0; i < m_nodes.size(); ++i) {
                if (m_nodes[i].first <= key) {
                    node* n = m_nodes[i].second;
                    if (n->ref_count() > 0){
                        nodes.push_back(n);
                    }
                }
            }
        }

        virtual void display(std::ostream& out, unsigned indent) const {
            for (unsigned j = 0; j < m_nodes.size(); ++j) {
                out << "\n";
                for (unsigned i = 0; i < indent; ++i) {
                    out << " ";
                }
                node* n = m_nodes[j].second;
                out << m_nodes[j].first << " count: " << n->ref_count();
                n->display(out, indent + 1);
            }
        }

        virtual unsigned size() const {
            unsigned sz = 1;
            for (unsigned j = 0; j < m_nodes.size(); ++j) {
                sz += m_nodes[j].second->size();
            }
            return sz;
        }

    private:
        bool contains(Key k) {
            for (unsigned j = 0; j < m_nodes.size(); ++j) {
                if (m_nodes[j].first == k) {
                    return true;
                }
            }
            return false;
        }

    };

    unsigned m_num_keys;
    node*    m_root;
    stats    m_stats;
    node*    m_spare_leaf;
    node*    m_spare_trie;
    vector<ptr_vector<node> > m_children;
public:

    heap_trie():         
        m_num_keys(0),
        m_root(0),
        m_spare_leaf(0),
        m_spare_trie(0)
    {}

    ~heap_trie() {
        dealloc(m_root);
        dealloc(m_spare_leaf);
        dealloc(m_spare_trie);
    }

    unsigned size() const {
        return m_root->size();
    }

    void reset(unsigned num_keys) {
        dealloc(m_root);
        dealloc(m_spare_leaf);
        dealloc(m_spare_trie);
        m_num_keys = num_keys;
        m_root = mk_trie();
        m_spare_trie = mk_trie();
        m_spare_leaf = mk_leaf();
    }

    void insert(Key const* keys, Value const& val) {
        ++m_stats.m_num_inserts;
        insert(m_root, num_keys(), keys, val);
    }

    bool find_eq(Key const* keys, Value& value) {
        ++m_stats.m_num_find_eq;
        node* n = m_root;
        node* m;
        for (unsigned i = 0; i < num_keys(); ++i) {
            if (!to_trie(n)->find(keys[i], m)) {
                return false;
            }            
            n = m;
        }
        value = to_leaf(n)->get_value();
        return true;
    }

    void find_le(Key const* keys, vector<Value>& values) {
        ++m_stats.m_num_find_le;
        ptr_vector<node> todo[2];
        todo[0].push_back(m_root);
        bool index = false;
        for (unsigned i = 0; i < num_keys(); ++i) {
            for (unsigned j = 0; j < todo[index].size(); ++j) {
                ++m_stats.m_num_find_le_nodes;
                to_trie(todo[index][j])->find_le(keys[i], todo[!index]);
            }
            todo[index].reset();
            index = !index;
        }
        for (unsigned j = 0; j < todo[index].size(); ++j) {
            values.push_back(to_leaf(todo[index][j])->get_value());
        }
    }


    // callback based find function
    class check_value {
    public:
        virtual bool operator()(Value const& v) = 0;
    };

    bool find_le(Key const* keys, check_value& check) {
        ++m_stats.m_num_find_le;
        if (m_children.size() < num_keys()) {
            m_children.resize(num_keys());
        }
        return find_le(m_root, 0, keys, check);
    }

    bool find_le(node* n, unsigned index, Key const* keys, check_value& check) {
        ++m_stats.m_num_find_le_nodes;
        if (index == num_keys()) {
            SASSERT(n->ref_count() > 0);
            return check(to_leaf(n)->get_value());
        }
        else {
            m_children[index].reset();
            to_trie(n)->find_le(keys[index], m_children[index]);
            for (unsigned i = 0; i < m_children[index].size(); ++i) {
                if (find_le(m_children[index][i], index + 1, keys, check)) {
                    return true;
                }
            }
            return false;
        }
    }

    void remove(Key const* keys) {
        ++m_stats.m_num_removes;
        // assumption: key is in table.
        node* n = m_root;
        node* m;
        for (unsigned i = 0; i < num_keys(); ++i) {
            n->dec_ref();
            VERIFY (to_trie(n)->find(keys[i], m));
            n = m;
        }           
        n->dec_ref();
    }

    void reset_statistics() {
        m_stats.reset();
    }

    void collect_statistics(statistics& st) const {
        st.update("heap_trie.num_inserts", m_stats.m_num_inserts);
        st.update("heap_trie.num_removes", m_stats.m_num_removes);
        st.update("heap_trie.num_find_eq", m_stats.m_num_find_eq);
        st.update("heap_trie.num_find_le", m_stats.m_num_find_le);
        st.update("heap_trie.num_find_le_nodes", m_stats.m_num_find_le_nodes);
    }

    void display(std::ostream& out) {
        m_root->display(out, 0);
        out << "\n";
    }

private:

    unsigned num_keys() const { 
        return m_num_keys;
    }
    
    void insert(node* n, unsigned num_keys, Key const* keys, Value const& val) {
        // assumption: key is not in table.

        while (true) {
            n->inc_ref();
            if (num_keys == 0) {
                to_leaf(n)->set_value(val);
                SASSERT(n->ref_count() == 1);
                break;
            }
            else {
                n = insert_key(to_trie(n), (num_keys == 1), keys[0]);
                --num_keys;
                ++keys;       
            } 
        }
    }

    node* insert_key(trie* n, bool is_leaf, Key const& key) {
        node* m1 = is_leaf?m_spare_leaf:m_spare_trie;
        node* m2 = n->find_or_insert(key, m1);
        if (m1 == m2) {
            if (is_leaf) {
                m_spare_leaf = mk_leaf();
            }
            else {
                m_spare_trie = mk_trie();
            }
        }
        return m2;
    }       

    leaf* mk_leaf() {
        return alloc(leaf);
    }

    trie* mk_trie() {
        return alloc(trie);
    }

    trie* to_trie(node* n) {
        SASSERT(n->type() == trie_t);
        return static_cast<trie*>(n);
    }

    leaf* to_leaf(node* n) {
        SASSERT(n->type() == leaf_t);
        return static_cast<leaf*>(n);
    }
};

#endif 
