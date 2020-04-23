/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/

#pragma once
#include "util/vector.h"
namespace lp {
template < typename B> class stacked_vector {
    struct log_entry { 
        unsigned m_i; unsigned m_ts; B b;
        log_entry(unsigned i, unsigned t, B const& b): m_i(i), m_ts(t), b(b) {}
        log_entry():m_i(UINT_MAX), m_ts(0) {}
    };
    svector<unsigned> m_stack_of_vector_sizes;
    svector<unsigned> m_stack_of_change_sizes;
    vector<log_entry> m_log;
    vector<B>         m_vector;
    svector<unsigned> m_last_update;
public:
    class ref {
        stacked_vector<B> & m_vec;
        unsigned m_i;
    public:
        ref(stacked_vector<B> &m, unsigned key): m_vec(m), m_i(key) {
            lp_assert(key < m.size());
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
        
        bool operator==(B const& other) const {
            return m_vec.m_vector[m_i] == other;
        }
        B& operator+=(B const &delta) {
            // not tracking the change here!
            return m_vec.m_vector[m_i] += delta;
        }
        B& operator-=(B const &delta) {
            // not tracking the change here!
            return m_vec.m_vector[m_i] -= delta;
        }
    };

    class ref_const {
        const stacked_vector<B> & m_vec;
        unsigned m_i;
    public:
        ref_const(const stacked_vector<B> &m, unsigned key) :m_vec(m), m_i(key) {
            lp_assert(key < m.size());
        }
 
        operator const B&() const {
            return m_vec.m_vector[m_i];
        }

    };

private:

    unsigned now() const { return m_stack_of_change_sizes.size(); }

    void emplace_replace(unsigned i,const B & b) {
        unsigned n = now();
        if (m_last_update[i] == n) {
            m_vector[i] = b;
        }
        else if (m_vector[i] != b) {
            m_log.push_back(log_entry(i, m_last_update[i], m_vector[i]));
            m_vector[i] = b;
            m_last_update[i] = n;
        }
    }
public:

    stacked_vector() { }

    ref operator[] (unsigned a) {
        return ref(*this, a);
    }

    ref_const operator[] (unsigned a) const {
        return ref_const(*this, a);
    }

    /*
      const B & operator[](unsigned a) const {
      lp_assert(a < m_vector.size());
      return m_vector[a];
      }
    */    
    unsigned size() const {
        return m_vector.size();
    }
    
    void push() {
        m_stack_of_change_sizes.push_back(m_log.size());
        m_stack_of_vector_sizes.push_back(m_vector.size());        
    }

    void pop() {
        pop(1);
    }

    template <typename T>  
    void pop_tail(svector<T> & v, unsigned k) {
        lp_assert(v.size() >= k);
        v.resize(v.size() - k);
    }

    template <typename T>  
    void resize(vector<T> & v, unsigned new_size) {
        v.resize(new_size);
    }
    
    void pop(unsigned k) {
        lp_assert(m_stack_of_vector_sizes.size() >= k);
        lp_assert(k > 0);
        m_vector.resize(m_stack_of_vector_sizes[m_stack_of_vector_sizes.size() - k]);
        m_last_update.resize(m_stack_of_vector_sizes[m_stack_of_vector_sizes.size() - k]);
        pop_tail(m_stack_of_vector_sizes, k);
        unsigned first_change = m_stack_of_change_sizes[m_stack_of_change_sizes.size() - k];
        pop_tail(m_stack_of_change_sizes, k);
        for (unsigned j = m_log.size(); j-- > first_change; ) {
            const auto & p = m_log[j];
            unsigned jc = p.m_i;
            if (jc < m_vector.size()) {
                m_vector[jc] = p.b; // restore the old value
                m_last_update[jc] = p.m_ts;
            }            
        }
        resize(m_log, first_change);

    }   
   
    void push_back(const B & b) {
        m_vector.push_back(b);
        m_last_update.push_back(now());
    }

    void increase_size_by_one() {
        m_vector.resize(m_vector.size() + 1);
        m_last_update.push_back(now());
    }

    unsigned peek_size(unsigned k) const {
        lp_assert(k > 0 && k <= m_stack_of_vector_sizes.size());
        return m_stack_of_vector_sizes[m_stack_of_vector_sizes.size() - k];
    }

    const vector<B>& operator()() const { return m_vector; }
};
}

