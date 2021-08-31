/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    trail.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-02.

Revision History:

--*/
#pragma once

#include "util/obj_hashtable.h"
#include "util/region.h"
#include "util/obj_ref.h"
#include "util/vector.h"


class trail {
public:
    virtual ~trail() {}
    virtual void undo() = 0;
};

template<typename T>
class value_trail : public trail {
    T & m_value;
    T   m_old_value;

public:
    value_trail(T & value):
        m_value(value),
        m_old_value(value) {
    }

    value_trail(T & value, T const& new_value):
        m_value(value),
        m_old_value(value) {
        m_value = new_value;
    }

    void undo() override {
        m_value = m_old_value;
    }
};


    
template<typename T, typename Ts>
class scoped_value_trail : public trail {
    T & m_value;
    Ts & m_values;
    
public:
    scoped_value_trail(T & value, Ts& values):
        m_value(value),
        m_values(values) {
    }
    
    void undo() override {
        m_value = m_values.back();
        m_values.pop_back();
    }
};


class reset_flag_trail : public trail {
    bool & m_value;
public:
    reset_flag_trail(bool & value):
        m_value(value) {
    }

    void undo() override {
        m_value = false;
    }
};

template<typename T>
class set_ptr_trail : public trail {
    T * & m_ptr;
public:
    set_ptr_trail(T * & ptr):
        m_ptr(ptr) {
        SASSERT(m_ptr == 0);
    }

    void undo() override {
        m_ptr = nullptr;
    }
};

template<typename T, bool CallDestructors=true>
class restore_size_trail : public trail {
    vector<T, CallDestructors> & m_vector;
    unsigned                     m_old_size;
public:
    restore_size_trail(vector<T, CallDestructors> & v, unsigned sz):
        m_vector(v),
        m_old_size(sz) {
    }
    restore_size_trail(vector<T, CallDestructors> & v):
        m_vector(v),
        m_old_size(v.size()) {
    }

    void undo() override {
        m_vector.shrink(m_old_size);
    }
};

template<typename T, bool CallDestructors=true>
class vector_value_trail : public trail {
    vector<T, CallDestructors> & m_vector;
    unsigned                     m_idx;
    T                            m_old_value;
public:
    vector_value_trail(vector<T, CallDestructors> & v, unsigned idx):
        m_vector(v),
        m_idx(idx),
        m_old_value(v[idx]) {
    }

    void undo() override {
        m_vector[m_idx] = m_old_value;
    }
};

template<typename V, typename T>
class vector2_value_trail : public trail {
    V             & m_vector;
    unsigned        m_i;
    unsigned        m_j;
    T               m_old_value;
public:
    vector2_value_trail(V& v, unsigned i, unsigned j):
        m_vector(v),
        m_i(i),
        m_j(j),
        m_old_value(v[i][j]) {
    }

    void undo() override {
        m_vector[m_i][m_j] = m_old_value;
    }
};


template<typename D, typename R>
class insert_obj_map : public trail {
    obj_map<D,R>&     m_map;
    D*                m_obj;
public:
    insert_obj_map(obj_map<D,R>& t, D* o) : m_map(t), m_obj(o) {}
    void undo() override { m_map.remove(m_obj); }
};

template<typename D, typename R>
class remove_obj_map : public trail {
    obj_map<D,R>&     m_map;
    D*                m_obj;
    R                 m_value;
public:
    remove_obj_map(obj_map<D,R>& t, D* o, R v) : m_map(t), m_obj(o), m_value(v) {}
    void undo() override { m_map.insert(m_obj, m_value); }
};

template<typename M, typename D>
class insert_map : public trail {
    M&            m_map;
    D             m_obj;
public:
    insert_map(M& t, D o) : m_map(t), m_obj(o) {}
    void undo() override { m_map.remove(m_obj); }
};


template<typename M, typename Mgr, typename D>
class insert_ref_map : public trail {
    Mgr&          m;
    M&            m_map;
    D             m_obj;
public:
    insert_ref_map(Mgr& m, M& t, D o) : m(m), m_map(t), m_obj(o) {}
    void undo() override { m_map.remove(m_obj); m.dec_ref(m_obj); }
};

template<typename Mgr, typename D, typename R>
class insert_ref2_map : public trail {
    Mgr&           m;
    obj_map<D,R*>&  m_map;
    D*             m_obj;
    R*             m_val;
public:
    insert_ref2_map(Mgr& m, obj_map<D,R*>& t, D*o, R*r) : m(m), m_map(t), m_obj(o), m_val(r) {}
    void undo() override { m_map.remove(m_obj); m.dec_ref(m_obj); m.dec_ref(m_val); }
};


template<typename V>
class push_back_vector : public trail {
    V & m_vector;
public:
    push_back_vector(V & v):
        m_vector(v) {
    }

    void undo() override {
        m_vector.pop_back();
    }
};

template<typename T>
class set_vector_idx_trail : public trail {
    ptr_vector<T> & m_vector;
    unsigned                         m_idx;
public:
    set_vector_idx_trail(ptr_vector<T> & v, unsigned idx):
        m_vector(v),
        m_idx(idx) {
    }

    void undo() override {
        m_vector[m_idx] = nullptr;
    }
};

template<typename T, bool CallDestructors=true>
class pop_back_trail : public trail {
    vector<T, CallDestructors> & m_vector;
    T m_value;
public:
    pop_back_trail(vector<T, CallDestructors> & v):
    m_vector(v),
    m_value(m_vector.back()) {
    }

    virtual void undo() {
        m_vector.push_back(m_value);
    }
};

template<typename T, bool CallDestructors=true>
class pop_back2_trail : public trail {
    vector<T, CallDestructors> & m_vector;
    typedef vector<vector<T, CallDestructors>, true> vector_t;
    unsigned m_index;
    T m_value;
public:
    pop_back2_trail(vector<T, CallDestructors> & v, unsigned index):
    m_vector(v),
    m_index(index),
    m_value(m_vector[index].back()) {
    }

    void undo() override {
        m_vector[m_index].push_back(m_value);
    }
};



template<typename T, bool CallDestructors=true>
class push_back_trail : public trail {
    vector<T, CallDestructors> & m_vector;
public:
    push_back_trail(vector<T, CallDestructors> & v):
        m_vector(v) {
    }

    void undo() override {
        m_vector.pop_back();
    }
};

template<typename T, bool CallDestructors=true>
class push_back2_trail : public trail {
    typedef vector<vector<T, CallDestructors>, true> vector_t;
    vector_t & m_vector;
    unsigned   m_index;
public:
    push_back2_trail(vector_t & v, unsigned index) :
    m_vector(v),
    m_index(index) {
    }

    void undo() override {
        m_vector[m_index].pop_back();
    }
};


class set_bitvector_trail : public trail {
    bool_vector & m_vector;
    unsigned        m_idx;
public:
    set_bitvector_trail(bool_vector & v, unsigned idx):
        m_vector(v),
        m_idx(idx) {
        SASSERT(m_vector[m_idx] == false);
        m_vector[m_idx] = true;
    }

    void undo() override {
        m_vector[m_idx] = false;
    }
};


template<typename T, bool CallDestructors = true>
class history_trail : public trail {
    vector<T, CallDestructors>& m_dst;
    unsigned                     m_idx;
    vector<T, CallDestructors>& m_hist;
public:
    history_trail(vector<T, CallDestructors>& v, unsigned idx, vector<T, CallDestructors>& hist) :
        m_dst(v),
        m_idx(idx),
        m_hist(hist) {}
    
    void undo() override {
        m_dst[m_idx] = m_hist.back();
        m_hist.pop_back();
    }
};


template<typename T>
class new_obj_trail : public trail {
    T * m_obj;
public:
    new_obj_trail(T * obj):
        m_obj(obj) {
    }

    void undo() override {
        dealloc(m_obj);
    }
};

template<typename M, typename T>
class obj_ref_trail : public trail {
    obj_ref<T,M> m_obj;
public:
    obj_ref_trail(obj_ref<T,M>& obj):
        m_obj(obj) {
    }

    void undo() override {
        m_obj.reset();
    }
};

template<typename T>
class insert_obj_trail : public trail {
    obj_hashtable<T>& m_table;
    T*                m_obj;
public:
    insert_obj_trail(obj_hashtable<T>& t, T* o) : m_table(t), m_obj(o) {}
    void undo() override { m_table.remove(m_obj); }
};


template<typename T>
class remove_obj_trail : public trail {
    obj_hashtable<T>& m_table;
    T*                m_obj;
public:
    remove_obj_trail(obj_hashtable<T>& t, T* o) : m_table(t), m_obj(o) {}
    void undo() override { m_table.insert(m_obj); }
};


inline void undo_trail_stack(ptr_vector<trail> & s, unsigned old_size) {
    SASSERT(old_size <= s.size());
    typename ptr_vector<trail >::iterator begin = s.begin() + old_size;
    typename ptr_vector<trail >::iterator it    = s.end();
    while (it != begin) {
        --it;
        (*it)->undo();
    }
    s.shrink(old_size);
}

class trail_stack {
    ptr_vector<trail>       m_trail_stack;
    unsigned_vector         m_scopes;
    region                  m_region;
public:
    region & get_region() { return m_region; }

    void reset() {
        pop_scope(m_scopes.size());
        // Undo trail objects stored at lvl 0 (avoid memory leaks if lvl 0 contains new_obj_trail objects).
        undo_trail_stack(m_trail_stack, 0);
    }

    void push_ptr(trail * t) { m_trail_stack.push_back(t); }

    template<typename TrailObject>
    void push(TrailObject const & obj) { m_trail_stack.push_back(new (m_region) TrailObject(obj)); }

    unsigned get_num_scopes() const { return m_scopes.size(); }

    void push_scope() { m_region.push_scope(); m_scopes.push_back(m_trail_stack.size()); }

    void pop_scope(unsigned num_scopes) {
        if (num_scopes == 0) return;
        unsigned lvl      = m_scopes.size();
        SASSERT(num_scopes <= lvl);
        unsigned new_lvl  = lvl - num_scopes;
        unsigned old_size = m_scopes[new_lvl];
        undo_trail_stack(m_trail_stack, old_size);
        m_scopes.shrink(new_lvl);
        m_region.pop_scope(num_scopes);
    }
};
