/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    heap.h

Abstract:

    A heap of integers.

Author:

    Leonardo de Moura (leonardo) 2006-09-14.

Revision History:

--*/
#ifndef HEAP_H_
#define HEAP_H_

#include"vector.h"
#include"debug.h"

template<typename LT>
class heap : private LT {
    int_vector    m_values;
    int_vector    m_value2indices;

    bool less_than(int v1, int v2) const { 
        return LT::operator()(v1, v2); 
    }

    static int left(int i) { 
        return i << 1; 
    }

    static int right(int i) { 
        return (i << 1) + 1; 
    }

    static int parent(int i) { 
        return i >> 1; 
    }

#ifdef Z3DEBUG
    // Return true if the value can be inserted in the heap. That is, the vector m_value2indices is big enough to store this value.
    bool is_valid_value(int v) const { 
        SASSERT(v >= 0 && v < static_cast<int>(m_value2indices.size())); 
        return true; 
    }

    bool check_invariant_core(int idx) const {
        if (idx < static_cast<int>(m_values.size())) {
            SASSERT(m_value2indices[m_values[idx]] == idx);
            SASSERT(parent(idx) == 0 || !less_than(m_values[idx], m_values[parent(idx)]));
            SASSERT(check_invariant_core(left(idx)));
            SASSERT(check_invariant_core(right(idx)));
        }
        return true;
    }
public:
    bool check_invariant() const { 
        return check_invariant_core(1); 
    }
#endif
private:

    void move_up(int idx) {
        int val = m_values[idx];
        while (true) {
            int parent_idx = parent(idx);
            if (parent_idx == 0 || !less_than(val, m_values[parent_idx])) {
                break;
            }
            m_values[idx]                  = m_values[parent_idx];
            m_value2indices[m_values[idx]] = idx;
            idx                            = parent_idx;
        }
        m_values[idx]        = val;
        m_value2indices[val] = idx;
        CASSERT("heap", check_invariant());
    }

    void move_down(int idx) {
        int val = m_values[idx];
        int sz  = static_cast<int>(m_values.size());
        while (true) {
            int left_idx  = left(idx);
            if (left_idx >= sz) {
                break;
            }
            int right_idx = right(idx);
            int min_idx   = right_idx < sz && less_than(m_values[right_idx], m_values[left_idx]) ? right_idx : left_idx;
            SASSERT(parent(min_idx) == idx);
            int min_value = m_values[min_idx];
            if (!less_than(min_value, val)) {
                break;
            }
            m_values[idx]                  = min_value;
            m_value2indices[min_value]     = idx;
            idx                            = min_idx;
        }
        m_values[idx]        = val;
        m_value2indices[val] = idx;
        CASSERT("heap", check_invariant());
    }

public:
    typedef int * iterator;
    typedef const int * const_iterator;

    heap(int s, const LT & lt = LT()):LT(lt) {
        m_values.push_back(-1);
        set_bounds(s);
        CASSERT("heap", check_invariant());
    }

    bool empty() const { 
        return m_values.size() == 1; 
    }

    bool contains(int val) const { 
        return val < static_cast<int>(m_value2indices.size()) && m_value2indices[val] != 0; 
    }

    void reset() {
        CASSERT("heap", check_invariant());
        if (empty()) {
            return;
        }
        memset(m_value2indices.begin(), 0, sizeof(int) * m_value2indices.size());
        m_values.reset();
        m_values.push_back(-1);
        CASSERT("heap", check_invariant());
    }

    void clear() { 
        reset(); 
    }

    void set_bounds(int s) { 
        m_value2indices.resize(s, 0); 
        CASSERT("heap", check_invariant());
    }
    
    unsigned get_bounds() const {
        return m_value2indices.size();
    }

    void reserve(int s) {
        CASSERT("heap", check_invariant());
        if (s > static_cast<int>(m_value2indices.size()))
            set_bounds(s);
        CASSERT("heap", check_invariant());
    }

    int min_value() const {
        SASSERT(!empty());
        return m_values[1];
    }

    int erase_min() {
        CASSERT("heap", check_invariant());
        SASSERT(!empty());
        SASSERT(m_values.size() >= 2);
        int result                  = m_values[1];
        if (m_values.size() == 2) {
            m_value2indices[result] = 0;
            m_values.pop_back();
            SASSERT(empty());
        }
        else {
            int last_val              = m_values.back();
            m_values[1]               = last_val;
            m_value2indices[last_val] = 1;
            m_value2indices[result]   = 0;
            m_values.pop_back();
            move_down(1);
        }
        CASSERT("heap", check_invariant());
        return result;
    }

    void erase(int val) {
        CASSERT("heap", check_invariant());
        SASSERT(contains(val));
        int idx      = m_value2indices[val];
        if (idx == static_cast<int>(m_values.size()) - 1) {
            m_value2indices[val] = 0;
            m_values.pop_back();
        }
        else {
            int last_val              = m_values.back();
            m_values[idx]             = last_val;
            m_value2indices[last_val] = idx;
            m_value2indices[val]      = 0;
            m_values.pop_back();
            int parent_idx            = parent(idx);
            if (parent_idx != 0 && less_than(last_val, m_values[parent(idx)])) {
                move_up(idx);
            }
            else {
                move_down(idx);
            }
        }
        CASSERT("heap", check_invariant());
    }

    void decreased(int val) { 
        SASSERT(contains(val)); 
        move_up(m_value2indices[val]); 
    }

    void increased(int val) { 
        SASSERT(contains(val)); 
        move_down(m_value2indices[val]); 
    }

    void insert(int val) {
        CASSERT("heap", check_invariant());
        SASSERT(is_valid_value(val));
        int idx              = static_cast<int>(m_values.size());
        m_value2indices[val] = idx;
        m_values.push_back(val);
        SASSERT(idx == static_cast<int>(m_values.size()) - 1);
        move_up(idx);
        CASSERT("heap", check_invariant());
    }

    iterator begin() { 
        return m_values.begin() + 1; 
    }

    iterator end() { 
        return m_values.end(); 
    }

    const_iterator begin() const { 
        return m_values.begin() + 1; 
    }

    const_iterator end() const { 
        return m_values.end(); 
    }

    void swap(heap & other) {
        if (this != &other) {
            CASSERT("heap", other.check_invariant());
            CASSERT("heap", check_invariant());
            m_values.swap(other.m_values);
            m_value2indices.swap(other.m_value2indices);
            CASSERT("heap", other.check_invariant());
            CASSERT("heap", check_invariant());
        }
    }

    /**
       \brief return set of values in heap that are less or equal to val.
     */
    void find_le(int val, int_vector& result) {
        int_vector todo;
        todo.push_back(1);
        while (!todo.empty()) {
            int index = todo.back();
            todo.pop_back();
            if (index < static_cast<int>(m_values.size()) &&
                !less_than(val, m_values[index])) {
                result.push_back(m_values[index]);
                todo.push_back(left(index));
                todo.push_back(right(index));
            }
        }
    }
  
};

#endif /* HEAP_H_ */

