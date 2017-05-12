/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
namespace lean {
template <typename T>
struct linear_combination_iterator {
    virtual bool next(T & a, unsigned & i) = 0;
    virtual bool next(unsigned & i) = 0;
    virtual void reset() = 0;
    virtual linear_combination_iterator * clone() = 0;
    virtual ~linear_combination_iterator(){}
    virtual unsigned size() const = 0;
};
template <typename T>
struct linear_combination_iterator_on_vector : linear_combination_iterator<T> {
    vector<std::pair<T, unsigned>> & m_vector;
    int m_offset;
    bool next(T & a, unsigned & i) {
        if(m_offset >= m_vector.size())
            return false;
        auto & p = m_vector[m_offset];
        a = p.first;
        i = p.second;
        m_offset++;
        return true;
    }

    bool next(unsigned & i) {
        if(m_offset >= m_vector.size())
            return false;
        auto & p = m_vector[m_offset];
        i = p.second;
        m_offset++;
        return true;
    }
    
    void reset() {m_offset = 0;}
    linear_combination_iterator<T> * clone() {
        return new linear_combination_iterator_on_vector(m_vector);
    }
    linear_combination_iterator_on_vector(vector<std::pair<T, unsigned>> & vec):
        m_vector(vec),
        m_offset(0)
    {}
    unsigned size() const { return m_vector.size(); }
};

}
