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

    Another possible enhancement is to resplay the tree. 
    Keep current key index in the nodes.

--*/

#ifndef HEAP_TRIE_H_
#define HEAP_TRIE_H_

#include "map.h"
#include "vector.h"
#include "buffer.h"
#include "statistics.h"
#include "small_object_allocator.h"


template<typename Key, typename KeyLE, typename KeyHash, typename Value>
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
        virtual unsigned num_nodes() const = 0;
        virtual unsigned num_leaves() const = 0;
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
        virtual unsigned num_nodes() const { return 1; }
        virtual unsigned num_leaves() const { return this->ref_count()>0?1:0; }
    };

    typedef buffer<std::pair<Key,node*>, true, 2> children_t;

    // lean trie node
    class trie : public node {
        children_t m_nodes;
    public:
        trie(): node(trie_t) {}

        virtual ~trie() {
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
        void find_le(KeyLE& le, Key key, ptr_vector<node>& nodes) {
            for (unsigned i = 0; i < m_nodes.size(); ++i) {
                if (le.le(m_nodes[i].first, key)) {
                    node* n = m_nodes[i].second;
                    if (n->ref_count() > 0){
                        nodes.push_back(n);
                    }
                }
            }
        }

        children_t const& nodes() const { return m_nodes; }
        children_t & nodes() { return m_nodes; }

        virtual void display(std::ostream& out, unsigned indent) const {
            for (unsigned j = 0; j < m_nodes.size(); ++j) {
                if (j != 0 || indent > 0) {
                    out << "\n";
                }
                for (unsigned i = 0; i < indent; ++i) {
                    out << " ";
                }
                node* n = m_nodes[j].second;
                out << m_nodes[j].first << " refs: " << n->ref_count();
                n->display(out, indent + 1);
            }
        }

        virtual unsigned num_nodes() const {
            unsigned sz = 1;
            for (unsigned j = 0; j < m_nodes.size(); ++j) {
                sz += m_nodes[j].second->num_nodes();
            }
            return sz;
        }

        virtual unsigned num_leaves() const {
            unsigned sz = 0;
            for (unsigned j = 0; j < m_nodes.size(); ++j) {
                sz += m_nodes[j].second->num_leaves();
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

    small_object_allocator m_alloc;
    KeyLE&   m_le;
    unsigned m_num_keys;
    unsigned_vector m_keys;
    unsigned m_do_reshuffle;
    node*    m_root;
    stats    m_stats;
    node*    m_spare_leaf;
    node*    m_spare_trie;

public:

    heap_trie(KeyLE& le):    
        m_alloc("heap_trie"),
        m_le(le),
        m_num_keys(0),
        m_do_reshuffle(4),
        m_root(0),
        m_spare_leaf(0),
        m_spare_trie(0)
    {}

    ~heap_trie() {
        del_node(m_root);
        del_node(m_spare_leaf);
        del_node(m_spare_trie);
    }

    unsigned size() const {
        return m_root?m_root->num_leaves():0;
    }

    void reset(unsigned num_keys) {
        del_node(m_root);
        del_node(m_spare_leaf);
        del_node(m_spare_trie);
        m_num_keys = num_keys;
        m_keys.resize(num_keys);
        for (unsigned i = 0; i < num_keys; ++i) {
            m_keys[i] = i;
        }
        m_root = mk_trie();
        m_spare_trie = mk_trie();
        m_spare_leaf = mk_leaf();
    }

    void insert(Key const* keys, Value const& val) {
        ++m_stats.m_num_inserts;
        insert(m_root, num_keys(), keys, m_keys.c_ptr(), val);
#if 0
        if (m_stats.m_num_inserts == (1 << m_do_reshuffle)) {
            m_do_reshuffle++;
            reorder_keys();
        }
#endif
    }

    bool find_eq(Key const* keys, Value& value) {
        ++m_stats.m_num_find_eq;
        node* n = m_root;
        node* m;
        for (unsigned i = 0; i < num_keys(); ++i) {
            if (!to_trie(n)->find(get_key(keys, i), m)) {
                return false;
            }            
            n = m;
        }
        value = to_leaf(n)->get_value();
        return true;
    }

    void find_all_le(Key const* keys, vector<Value>& values) {
        ++m_stats.m_num_find_le;
        ptr_vector<node> todo[2];
        todo[0].push_back(m_root);
        bool index = false;
        for (unsigned i = 0; i < num_keys(); ++i) {
            for (unsigned j = 0; j < todo[index].size(); ++j) {
                ++m_stats.m_num_find_le_nodes;
                to_trie(todo[index][j])->find_le(m_le, get_key(keys, i), todo[!index]);
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
        ++m_stats.m_num_find_le_nodes;
        return find_le(m_root, 0, keys, check);
    }

    void remove(Key const* keys) {
        ++m_stats.m_num_removes;
        // assumption: key is in table.
        node* n = m_root;
        node* m = 0;
        for (unsigned i = 0; i < num_keys(); ++i) {
            n->dec_ref();
            VERIFY (to_trie(n)->find(get_key(keys, i), m));
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
        if (m_root) st.update("heap_trie.num_nodes", m_root->num_nodes());
        unsigned_vector nums;
        ptr_vector<node> todo;
        if (m_root) todo.push_back(m_root);
        while (!todo.empty()) {
            node* n = todo.back();
            todo.pop_back();
            if (is_trie(n)) {
                trie* t = to_trie(n);
                unsigned sz = t->nodes().size();
                if (nums.size() <= sz) {
                    nums.resize(sz+1);
                }
                ++nums[sz];
                for (unsigned i = 0; i < sz; ++i) {
                    todo.push_back(t->nodes()[i].second);
                }
            }
        }
        if (nums.size() < 16) nums.resize(16);
        st.update("heap_trie.num_1_children", nums[1]);
        st.update("heap_trie.num_2_children", nums[2]);
        st.update("heap_trie.num_3_children", nums[3]);
        st.update("heap_trie.num_4_children", nums[4]);
        st.update("heap_trie.num_5_children", nums[5]);
        st.update("heap_trie.num_6_children", nums[6]);
        st.update("heap_trie.num_7_children", nums[7]);
        st.update("heap_trie.num_8_children", nums[8]);
        st.update("heap_trie.num_9_children", nums[9]);
        st.update("heap_trie.num_10_children", nums[10]);
        st.update("heap_trie.num_11_children", nums[11]);
        st.update("heap_trie.num_12_children", nums[12]);
        st.update("heap_trie.num_13_children", nums[13]);
        st.update("heap_trie.num_14_children", nums[14]);
        st.update("heap_trie.num_15_children", nums[15]);
        unsigned sz = 0;
        for (unsigned i = 16; i < nums.size(); ++i) {
            sz += nums[i];
        }
        st.update("heap_trie.num_16+_children", sz);
    }

    void display(std::ostream& out) const {
        m_root->display(out, 0);
        out << "\n";
    }

    class iterator {
        ptr_vector<node> m_path;
        unsigned_vector  m_idx;
        vector<Key>      m_keys;
        unsigned         m_count;
    public:
        iterator(node* n) {
            if (!n) {
                m_count = UINT_MAX;
            }
            else {
                m_count = 0;
                first(n);
            }
        }
        Key const* keys() {
            return m_keys.c_ptr();
        }

        Value const& value() const {
            return to_leaf(m_path.back())->get_value();
        }
        iterator& operator++() { fwd(); return *this; }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        bool operator==(iterator const& it) const {return m_count == it.m_count; }
        bool operator!=(iterator const& it) const {return m_count != it.m_count; }

    private:
        void first(node* r) {
            SASSERT(r->ref_count() > 0);
            while (is_trie(r)) {
                trie* t = to_trie(r);
                m_path.push_back(r);
                unsigned sz = t->nodes().size();
                for (unsigned i = 0; i < sz; ++i) {
                    r = t->nodes()[i].second;
                    if (r->ref_count() > 0) {
                        m_idx.push_back(i);
                        m_keys.push_back(t->nodes()[i].first);                        
                        break;
                    }
                }
            }
            SASSERT(is_leaf(r));
            m_path.push_back(r);
        }

        void fwd() {
            if (m_path.empty()) {
                m_count = UINT_MAX;
                return;
            }
            m_path.pop_back();
            while (!m_path.empty()) {
                trie* t = to_trie(m_path.back());
                unsigned idx = m_idx.back();                   
                unsigned sz = t->nodes().size();
                m_idx.pop_back();
                m_keys.pop_back();
                for (unsigned i = idx+1; i < sz; ++i) {
                    node* r = t->nodes()[i].second;
                    if (r->ref_count() > 0) {
                        m_idx.push_back(i);
                        m_keys.push_back(t->nodes()[i].first);
                        first(r);
                        ++m_count;
                        return;
                    }
                }
                m_path.pop_back();
            }
            m_count = UINT_MAX;
        }
    };

    iterator begin() const { 
        return iterator(m_root);
    }

    iterator end() const { 
        return iterator(0);
    }


private:

    inline unsigned num_keys() const { 
        return m_num_keys;
    }

    inline Key const& get_key(Key const* keys, unsigned i) const {
        return keys[m_keys[i]];
    }

    struct KeyEq {
        bool operator()(Key const& k1, Key const& k2) const {
            return k1 == k2;
        }
    };


    typedef hashtable<Key, KeyHash, KeyEq> key_set;

    struct key_info {
        unsigned m_index;
        unsigned m_index_size;
        key_info(unsigned i, unsigned sz):
            m_index(i),
            m_index_size(sz)
        {}

        bool operator<(key_info const& other) const {
            return 
                (m_index_size < other.m_index_size) ||
                ((m_index_size == other.m_index_size) && 
                 (m_index < other.m_index));
        }
    };

    void reorder_keys() {
        vector<key_set> weights;
        weights.resize(num_keys());
        unsigned_vector depth;
        ptr_vector<node> nodes;
        depth.push_back(0);
        nodes.push_back(m_root);
        while (!nodes.empty()) {
            node* n = nodes.back();
            unsigned d = depth.back();
            nodes.pop_back();
            depth.pop_back();
            if (is_trie(n)) {
                trie* t = to_trie(n);
                unsigned sz = t->nodes().size();
                for (unsigned i = 0; i < sz; ++i) {
                    nodes.push_back(t->nodes()[i].second);
                    depth.push_back(d+1);
                    weights[d].insert(t->nodes()[i].first);
                }
            }
        }
        SASSERT(weights.size() == num_keys());
        svector<key_info> infos;
        unsigned sz = 0;
        bool is_sorted = true;
        for (unsigned i = 0; i < weights.size(); ++i) {
            unsigned sz2 = weights[i].size();
            if (sz > sz2) {
                is_sorted = false;
            }
            sz = sz2;
            infos.push_back(key_info(i, sz));
        }
        if (is_sorted) {
            return;
        }
        std::sort(infos.begin(), infos.end());
        unsigned_vector sorted_keys, new_keys;
        for (unsigned i = 0; i < num_keys(); ++i) {
            unsigned j = infos[i].m_index;
            sorted_keys.push_back(j);
            new_keys.push_back(m_keys[j]);
        } 
        // m_keys:    i |-> key_index
        // new_keys:  i |-> new_key_index
        // permutation: key_index |-> new_key_index
        SASSERT(sorted_keys.size() == num_keys());
        SASSERT(new_keys.size() == num_keys());
        SASSERT(m_keys.size() == num_keys());
        iterator it = begin();
        trie* new_root = mk_trie();
        IF_VERBOSE(2, verbose_stream() << "before reshuffle: " << m_root->num_nodes() << " nodes\n";);
        for (; it != end(); ++it) {
            IF_VERBOSE(2, 
                       for (unsigned i = 0; i < num_keys(); ++i) {
                           for (unsigned j = 0; j < num_keys(); ++j) {
                               if (m_keys[j] == i) {
                                   verbose_stream() << it.keys()[j] << " ";
                                   break;
                               }
                           }
                       }
                       verbose_stream() << " |-> " << it.value() << "\n";);

            insert(new_root, num_keys(), it.keys(), sorted_keys.c_ptr(), it.value());
        }
        del_node(m_root);
        m_root = new_root;
        for (unsigned i = 0; i < m_keys.size(); ++i) {
            m_keys[i] = new_keys[i];
        }
        
        IF_VERBOSE(2, verbose_stream() << "after reshuffle: " << new_root->num_nodes() << " nodes\n";);
        IF_VERBOSE(2, 
                   it = begin();
                   for (; it != end(); ++it) {                       
                       for (unsigned i = 0; i < num_keys(); ++i) {
                           for (unsigned j = 0; j < num_keys(); ++j) {
                               if (m_keys[j] == i) {
                                   verbose_stream() << it.keys()[j] << " ";
                                   break;
                               }
                           }
                       }
                       verbose_stream() << " |-> " << it.value() << "\n";
                   });
    }

    bool find_le(node* n, unsigned index, Key const* keys, check_value& check) {
        if (index == num_keys()) {
            SASSERT(n->ref_count() > 0);
            bool r = check(to_leaf(n)->get_value());
            IF_VERBOSE(2, 
                       for (unsigned j = 0; j < index; ++j) {
                           verbose_stream() << " ";
                       }
                       verbose_stream() << to_leaf(n)->get_value() << (r?" hit\n":" miss\n"););
            return r;
        }
        else {
            Key const& key = get_key(keys, index);
            children_t& nodes = to_trie(n)->nodes();
            for (unsigned i = 0; i < nodes.size(); ++i) {
                ++m_stats.m_num_find_le_nodes;
                node* m = nodes[i].second;
                IF_VERBOSE(2,
                           for (unsigned j = 0; j < index; ++j) {
                               verbose_stream() << " ";
                           }
                           verbose_stream() << nodes[i].first << " <=? " << key << " rc:" << m->ref_count() << "\n";);
                if (m->ref_count() > 0 && m_le.le(nodes[i].first, key) && find_le(m, index+1, keys, check)) {
                    if (i > 0) {
                        std::swap(nodes[i], nodes[0]);
                    }
                    return true;
                }
            }
            return false;
        }
    }
    
    void insert(node* n, unsigned num_keys, Key const* keys, unsigned const* permutation, Value const& val) {
        // assumption: key is not in table.
        for (unsigned i = 0; i < num_keys; ++i) {
            n->inc_ref();
            n = insert_key(to_trie(n), (i + 1 == num_keys), keys[permutation[i]]);
        }
        n->inc_ref();
        to_leaf(n)->set_value(val);
        SASSERT(n->ref_count() == 1);
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
        void* mem = m_alloc.allocate(sizeof(leaf));
        return new (mem) leaf();
    }

    trie* mk_trie() {
        void* mem = m_alloc.allocate(sizeof(trie));
        return new (mem) trie();
    }

    void del_node(node* n) {
        if (!n) {
            return;
        }
        if (is_trie(n)) {
            trie* t = to_trie(n);
            for (unsigned i = 0; i < t->nodes().size(); ++i) {
                del_node(t->nodes()[i].second);
            }            
            t->~trie();
            m_alloc.deallocate(sizeof(trie), t);
        }
        else {
            leaf* l = to_leaf(n);
            l->~leaf();
            m_alloc.deallocate(sizeof(leaf), l);
        }
    }

    static trie* to_trie(node* n) {
        SASSERT(is_trie(n));
        return static_cast<trie*>(n);
    }

    static leaf* to_leaf(node* n) {
        SASSERT(is_leaf(n));
        return static_cast<leaf*>(n);
    }

    static bool is_leaf(node* n) {
        return n->type() == leaf_t;
    }

    static bool is_trie(node* n) {
        return n->type() == trie_t;
    }
};

#endif 
