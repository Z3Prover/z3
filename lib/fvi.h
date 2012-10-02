/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    fvi.h

Abstract:

    Feature Vector Indexing.

Author:

    Leonardo de Moura (leonardo) 2008-02-01.

Revision History:

--*/
#ifndef _FVI_H_
#define _FVI_H_

#include"splay_tree_map.h"
#include"hashtable.h"
#include"vector.h"

/**
   \brief A feature vector indexing for objects of type T *.

   ToVector is a functor for converting T into a vector of natural numbers.
   It should provide a method:
      - void operator(T * d, unsigned * f);
      This method should fill the vector f with the features of d.

   Hash: functor for computing the hashcode of T *.

   Eq  : functor for comparing T pointers.
*/
template<typename T, typename ToVector, typename Hash, typename Eq=ptr_eq<T> >
class fvi : private ToVector {
public:
    struct statistics {
        unsigned m_size;
        unsigned m_num_nodes;
        unsigned m_num_leaves;
        unsigned m_min_leaf_size;
        unsigned m_avg_leaf_size;
        unsigned m_max_leaf_size;
        statistics() { reset(); }

        void reset() { 
            m_size = m_num_nodes = m_num_leaves = m_avg_leaf_size = m_max_leaf_size = 0;
            m_min_leaf_size = UINT_MAX;
        }
    };
    
private:
    struct ucompare {
        int operator()(unsigned i1, unsigned i2) const {
            if (i1 < i2) return -1;
            if (i1 > i2) return  1;
            return 0;
        }
    };

    struct node {
        node() {}
        virtual ~node() {}
        virtual bool is_leaf() const = 0;
    };

    typedef splay_tree_map<unsigned, node *, ucompare> children;

    struct non_leaf : public node {
        children m_children;
        non_leaf() {}

        struct delete_children {
            void operator()(unsigned k, node * n) const {
                dealloc(n);
            }
        };

        virtual ~non_leaf() {
            delete_children visitor;
            m_children.visit(visitor);
            m_children.reset();
        }

        virtual bool is_leaf() const { return false; }
    };

    typedef ptr_hashtable<T, Hash, Eq>     set;
  
    struct leaf : public node {
        set   m_set;
        leaf() {}
        virtual ~leaf() {}
        virtual bool is_leaf() const { return true; }
    };

    unsigned          m_num_features;
    svector<unsigned> m_tmp_buffer;
    non_leaf *        m_root;

    struct stop {};

    template<typename Visitor>
    void visit_leaf(leaf * n, Visitor & v, bool le) const {
        typename set::iterator it  = n->m_set.begin();
        typename set::iterator end = n->m_set.end();
        for (; it != end; ++it)
            if (!v(*it))
                throw stop();
    }

    template<typename Visitor>
    struct non_leaf_visitor {
        fvi const & m_owner;        
        unsigned    m_fidx;
        Visitor &   m_visitor;
        bool        m_le;

        non_leaf_visitor(fvi const & o, unsigned fidx, Visitor & v, bool le):
            m_owner(o), m_fidx(fidx), m_visitor(v), m_le(le) {}
        
        void operator()(unsigned k, node * n) {
            if (n->is_leaf())
                m_owner.visit_leaf(static_cast<leaf*>(n), m_visitor, m_le);
            else
                m_owner.visit_non_leaf(static_cast<non_leaf*>(n), m_fidx + 1, m_visitor, m_le);
        }
    };
        
    template<typename Visitor>
    void visit_non_leaf(non_leaf * n, unsigned fidx, Visitor & v, bool le) const {
        // Remark: this function is recursive, but there is no risk
        // of stack overflow since the number of features is small.
        non_leaf_visitor<Visitor> v2(*this, fidx, v, le);
        if (le)
            n->m_children.visit_le(v2, m_tmp_buffer[fidx]);
        else
            n->m_children.visit_ge(v2, m_tmp_buffer[fidx]);
    }

#ifdef Z3DEBUG
    bool m_visiting;
#endif

    void to_fvector(T * d) const {
        fvi * _this = const_cast<fvi *>(this);
        _this->ToVector::operator()(d, _this->m_tmp_buffer.c_ptr()); 
    }
    
    struct non_leaf_stat_visitor {
        fvi const &  m_owner;        
        statistics & m_stats;
        non_leaf_stat_visitor(fvi const & o, statistics & st):m_owner(o), m_stats(st) {}
        void operator()(unsigned k, node * n);
    };

    void stats(leaf * n, statistics & result) const;
    void stats(non_leaf * n, statistics & result) const;

    struct non_leaf_collect_visitor {
        fvi const &     m_owner;
        ptr_vector<T> & m_elems;
        non_leaf_collect_visitor(fvi const & o, ptr_vector<T> & elems):m_owner(o), m_elems(elems) {}
        void operator()(unsigned k, node * n);
    };

    void collect(leaf * n, ptr_vector<T> & result) const;
    void collect(non_leaf * n, ptr_vector<T> & result) const;

public:
    fvi(unsigned num_features, ToVector const & t = ToVector());
    ~fvi() { reset(); dealloc(m_root); }

    void insert(T * d);
    bool contains(T * d) const;
    void erase(T * d);
    void reset();

    /**
       \brief Traverse the elements that have features  smaller (greater) or equal than the one of the given element.

       For each visited element the following method of v is executed:

       - bool operator()(T * d)

       If false is returned, the traversal is aborted.
       
       \warning The object cannot be updated during the traversal.
    */
    template<typename Visitor>
    void visit(T * d, Visitor & v, bool le = true) const {
        DEBUG_CODE(const_cast<fvi*>(this)->m_visiting = true;);
        to_fvector(d);
        try {
            visit_non_leaf(m_root, 0, v, le);
        }
        catch (stop) {
        }
        DEBUG_CODE(const_cast<fvi*>(this)->m_visiting = false;);
    }

    void stats(statistics & result) const;

    /**
       \brief Copy to result the set of elements stored in the index.
    */
    void collect(ptr_vector<T> & result) const;
};

#endif /* _FVI_H_ */
