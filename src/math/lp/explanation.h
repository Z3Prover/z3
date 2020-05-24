/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include "math/lp/lp_utils.h"
#include "util/map.h"
#include "util/hashtable.h"
namespace lp {
class explanation {
    typedef vector<std::pair<unsigned, mpq>> pair_vec;
    typedef    hashtable<unsigned, u_hash, u_eq>  ci_set;
    // Only one of the fields below is used. The first call adding an entry decides which one it is.
    vector<std::pair<constraint_index, mpq>> m_vector;
    ci_set  m_set;   
public:
    explanation() {}
    
    template <typename T>
    explanation(const T& t) {
        for (unsigned c : t)
            push_back(c);
    }
    
    void clear() { m_vector.clear(); m_set.reset(); }
    void add_pair(constraint_index j, const mpq& v) {
        SASSERT(m_set.empty()); 
        m_vector.push_back(std::make_pair(j, v));
    }

    // this signature is needed to use it in a template that also works for the vector type
    void push_back(constraint_index j) {
        SASSERT(m_vector.empty());
        m_set.insert(j);
    }
    
    void add_expl(const explanation& e) {
        if (e.m_vector.empty()) {
            for (constraint_index j : e.m_set)
                push_back(j);
        } else {
            for (const auto & p : e.m_vector) {
                add_pair(p.first, p.second);
            }
        }
    }

    bool empty() const {  return m_vector.empty() || m_set.empty();  }
    size_t size() const { return std::max(m_vector.size(), m_set.size()); }

    class cimpq {
        constraint_index m_var;
        const mpq&  m_coeff;
    public:
        cimpq(constraint_index var, const mpq & val) : m_var(var), m_coeff(val) { }
        constraint_index ci() const { return m_var; }
        const mpq &coeff() const { return m_coeff; }
    };
    class iterator {
        bool      m_run_on_vector;
        pair_vec::const_iterator    m_vi;
        ci_set::iterator            m_ci;
    public:
        cimpq operator*() const {
            return m_run_on_vector?
                cimpq( m_vi->first, m_vi->second) :
                cimpq( *m_ci, one_of_type<mpq>()); 
        }        
        iterator operator++() {
            if (m_run_on_vector)
                m_vi++;
            else
                m_ci++;                    
            return *this;
        }
        iterator operator++(int) {
            iterator i = *this; ++(*this); return i;
        }
        iterator(bool run_on_vector, pair_vec::const_iterator vi, ci_set::iterator cii) :
            m_run_on_vector(run_on_vector), m_vi(vi), m_ci(cii)
        {}
        bool operator==(const iterator &other) const {
            SASSERT(m_run_on_vector == other.m_run_on_vector);
            return  m_run_on_vector? m_vi == other.m_vi : m_ci == other.m_ci;
        }
        bool operator!=(const iterator &other) const { return !(*this == other); }
    };

    iterator begin() const {
        return iterator( !m_vector.empty(), m_vector.begin(), m_set.begin());
    }
    iterator end() const {
        return iterator(!m_vector.empty(), m_vector.end(), m_set.end());
    }

};
}
