/*
Copyright (c) 2017 Microsoft Corporation
Author: Lev Nachmanson
*/
#pragma once
#include <unordered_map>
#include <set>
#include <stack>
#include "util/vector.h"
namespace lean {
template < typename B> class stacked_vector {
    vector<unsigned> m_stack_of_vector_sizes;
    vector<unsigned> m_stack_of_change_sizes;
    vector<std::pair<unsigned, B>> m_changes;
    vector<B> m_vector;
public:
    class ref {
        stacked_vector<B> & m_vec;
        unsigned m_i;
    public:
        ref(stacked_vector<B> &m, unsigned key) :m_vec(m), m_i(key) {
            lean_assert(key < m.size());
        }
        ref & operator=(const B & b) {
            m_vec.emplace_replace(m_i, b);
            return *this;
        }
        ref & operator=(const ref & b) {
            m_vec.emplace_replace(m_i, b.m_vec.m_vector[b.m_i]);
            return *this;
        }
        operator const B&() const {
            return m_vec.m_vector[m_i];
        }

    };

    class ref_const {
        const stacked_vector<B> & m_vec;
        unsigned m_i;
    public:
        ref_const(const stacked_vector<B> &m, unsigned key) :m_vec(m), m_i(key) {
            lean_assert(key < m.size());
        }
 
        operator const B&() const {
            return m_vec.m_vector[m_i];
        }

    };

private:
    void emplace_replace(unsigned i,const B & b) {
		if (m_vector[i] != b) {
			m_changes.push_back(std::make_pair(i, m_vector[i]));
			m_vector[i] = b;
		}
    }
public:

    ref operator[] (unsigned a) {
        return ref(*this, a);
    }

    ref_const operator[] (unsigned a) const {
        return ref_const(*this, a);
    }

    /*
    const B & operator[](unsigned a) const {
        lean_assert(a < m_vector.size());
        return m_vector[a];
    }
    */    
    unsigned size() const {
        return m_vector.size();
    }

    
    void push() {
        m_stack_of_change_sizes.push_back(m_changes.size());
        m_stack_of_vector_sizes.push_back(m_vector.size());
    }

    void pop() {
        pop(1);
    }

    template <typename T>  
	void pop_tail(vector<T> & v, unsigned k) {
		lean_assert(v.size() >= k);
		v.resize(v.size() - k);
	}

    template <typename T>  
    void resize(vector<T> & v, unsigned new_size) {
		v.resize(new_size);
    }
    
    void pop(unsigned k) {
        lean_assert(m_stack_of_vector_sizes.size() >= k);
        lean_assert(k > 0);
        resize(m_vector, m_stack_of_vector_sizes[m_stack_of_vector_sizes.size() - k]);
        pop_tail(m_stack_of_vector_sizes, k);
        unsigned first_change = m_stack_of_change_sizes[m_stack_of_change_sizes.size() - k];
        pop_tail(m_stack_of_change_sizes, k);
        for (unsigned j = m_changes.size(); j-- > first_change; ) {
            const auto & p = m_changes[j];
            unsigned jc = p.first;
            if (jc < m_vector.size())
                m_vector[jc] = p.second; // restore the old value
        }
        resize(m_changes, first_change);

        /*
        while (k-- > 0) {
            
            if (m_stack.empty())
                return;
            
            delta & d = m_stack.back();
            lean_assert(m_vector.size() >= d.m_size);
            while (m_vector.size() > d.m_size)
                m_vector.pop_back();
            
            for (auto & t : d.m_original_changed) {
                lean_assert(t.first < m_vector.size());
                m_vector[t.first] = t.second;
            }
            //            lean_assert(d.m_deb_copy == m_vector);
            m_stack.pop_back();*/
    }   

    
    // void clear() {
    //     if (m_stack.empty()) {
    //         m_vector.clear();
    //         return;
    //     }

    //     delta & d = m_stack.top();
    //     auto & oc = d.m_original_changed;
    //     for (auto & p : m_vector) {
    //         const auto & it = oc.find(p.first);
    //         if (it == oc.end() && d.m_new.find(p.first) == d.m_new.end())
    //             oc.emplace(p.first, p.second);
    //     }
    //     m_vector.clear();
    // }

    void push_back(const B & b) {
        m_vector.push_back(b);
    }

    void increase_size_by_one() {
        m_vector.resize(m_vector.size() + 1);
    }

	unsigned peek_size(unsigned k) const {
		lean_assert(k > 0 && k <= m_stack_of_vector_sizes.size());
		return m_stack_of_vector_sizes[m_stack_of_vector_sizes.size() - k];
	}

    const vector<B>& operator()() const { return m_vector; }
};
}

