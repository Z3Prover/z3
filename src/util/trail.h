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
#ifndef TRAIL_H_
#define TRAIL_H_

#include"obj_hashtable.h"
#include"region.h"
#include"obj_ref.h"

template<typename Ctx>
class trail {
public:
    virtual ~trail() {
    }
    virtual void undo(Ctx & ctx) = 0;
};

template<typename Ctx, typename T>
class value_trail : public trail<Ctx> {
    T & m_value;
    T   m_old_value;
    
public:
    value_trail(T & value):
        m_value(value),
        m_old_value(value) {
    }
    
    virtual ~value_trail() {
    }
    
    virtual void undo(Ctx & ctx) {
        m_value = m_old_value;
    }
};

template<typename Ctx>
class reset_flag_trail : public trail<Ctx> {
    bool & m_value;
public:
    reset_flag_trail(bool & value):
        m_value(value) {
    }
    
    virtual ~reset_flag_trail() {
    }
    
    virtual void undo(Ctx & ctx) {
        m_value = false;
    }
};

template<typename Ctx, typename T>
class set_ptr_trail : public trail<Ctx> {
    T * & m_ptr;
public:
    set_ptr_trail(T * & ptr):
        m_ptr(ptr) {
        SASSERT(m_ptr == 0);
    }
    
    virtual void undo(Ctx & ctx) {
        m_ptr = 0;
    }
};

template<typename Ctx, typename T, bool CallDestructors=true>
class restore_size_trail : public trail<Ctx> {
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
    virtual ~restore_size_trail() {
    }
    virtual void undo(Ctx & ctx) {
        m_vector.shrink(m_old_size);
    }
};    
        
template<typename Ctx, typename T, bool CallDestructors=true>
class vector_value_trail : public trail<Ctx> {
    vector<T, CallDestructors> & m_vector;
    unsigned                     m_idx;
    T                            m_old_value;
public:
    vector_value_trail(vector<T, CallDestructors> & v, unsigned idx):
        m_vector(v),
        m_idx(idx),
        m_old_value(v[idx]) {
    }
    
    virtual ~vector_value_trail() {
    }
    
    virtual void undo(Ctx & ctx) {
        m_vector[m_idx] = m_old_value;
    }
};


template<typename Ctx, typename D, typename R>
class insert_obj_map : public trail<Ctx> {
    obj_map<D,R>&     m_map;
    D*                m_obj;
public:
    insert_obj_map(obj_map<D,R>& t, D* o) : m_map(t), m_obj(o) {}
    virtual ~insert_obj_map() {}
    virtual void undo(Ctx & ctx) { m_map.remove(m_obj); }
};

template<typename Ctx, typename M, typename D>
class insert_map : public trail<Ctx> {
    M&            m_map;
    D             m_obj;
public:
    insert_map(M& t, D o) : m_map(t), m_obj(o) {}
    virtual ~insert_map() {}
    virtual void undo(Ctx & ctx) { m_map.remove(m_obj); }
};



template<typename Ctx, typename V>
class push_back_vector : public trail<Ctx> {
    V & m_vector;
public:
    push_back_vector(V & v):
        m_vector(v) {
    }
    
    virtual void undo(Ctx & ctx) {
        m_vector.pop_back();
    }
};

template<typename Ctx, typename T>
class set_vector_idx_trail : public trail<Ctx> {
    ptr_vector<T> & m_vector;
    unsigned                         m_idx;
public:
    set_vector_idx_trail(ptr_vector<T> & v, unsigned idx):
        m_vector(v),
        m_idx(idx) {
    }
    
    virtual ~set_vector_idx_trail() {
    }
    
    virtual void undo(Ctx & ctx) {
        m_vector[m_idx] = 0;
    }
};
    
template<typename Ctx, typename T, bool CallDestructors=true>
class pop_back_trail : public trail<Ctx> {
    vector<T, CallDestructors> & m_vector;
    T m_value;
public:
    pop_back_trail(vector<T, CallDestructors> & v):
    m_vector(v),
    m_value(m_vector.back()) {
    }
    
    virtual void undo(Ctx & ctx) {
        m_vector.push_back(m_value);
    }
};

template<typename Ctx, typename T, bool CallDestructors=true>
class pop_back2_trail : public trail<Ctx> {
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
    
    virtual void undo(Ctx & ctx) {
        m_vector[m_index].push_back(m_value);
    }
};



template<typename Ctx, typename T, bool CallDestructors=true>
class push_back_trail : public trail<Ctx> {
    vector<T, CallDestructors> & m_vector;
public:
    push_back_trail(vector<T, CallDestructors> & v):
        m_vector(v) {
    }
    
    virtual void undo(Ctx & ctx) {
        m_vector.pop_back();
    }
};

template<typename Ctx, typename T, bool CallDestructors=true>
class push_back2_trail : public trail<Ctx> {
    typedef vector<vector<T, CallDestructors>, true> vector_t;
    vector_t & m_vector;
    unsigned   m_index;
public:
    push_back2_trail(vector_t & v, unsigned index) : 
    m_vector(v),
    m_index(index) {
    }
    
    virtual void undo(Ctx & ctx) {
        m_vector[m_index].pop_back();
    }
};

template<typename Ctx>
class set_bitvector_trail : public trail<Ctx> {
    svector<bool> & m_vector;
    unsigned        m_idx;
public:
    set_bitvector_trail(svector<bool> & v, unsigned idx):
        m_vector(v),
        m_idx(idx) {
        SASSERT(m_vector[m_idx] == false);
        m_vector[m_idx] = true;
    }
    
    virtual void undo(Ctx & ctx) {
        m_vector[m_idx] = false;
    }
};
    
template<typename Ctx, typename T>
class new_obj_trail : public trail<Ctx> {
    T * m_obj;
public:
    new_obj_trail(T * obj):
        m_obj(obj) {
    }
    
    virtual void undo(Ctx & ctx) {
        dealloc(m_obj);
    }
};

template<typename Ctx, typename M, typename T>
class obj_ref_trail : public trail<Ctx> {
    obj_ref<T,M> m_obj;
public:
    obj_ref_trail(obj_ref<T,M>& obj):
        m_obj(obj) {
    }
    
    virtual void undo(Ctx & ctx) {
        m_obj.reset();
    }
};

template<typename Ctx, typename T>
class insert_obj_trail : public trail<Ctx> {
    obj_hashtable<T>& m_table;
    T*                m_obj;
public:
    insert_obj_trail(obj_hashtable<T>& t, T* o) : m_table(t), m_obj(o) {}
    virtual ~insert_obj_trail() {}
    virtual void undo(Ctx & ctx) { m_table.remove(m_obj); }
};



template<typename Ctx, typename T>
class remove_obj_trail : public trail<Ctx> {
    obj_hashtable<T>& m_table;
    T*                m_obj;
public:
    remove_obj_trail(obj_hashtable<T>& t, T* o) : m_table(t), m_obj(o) {}
    virtual ~remove_obj_trail() {}
    virtual void undo(Ctx & ctx) { m_table.insert(m_obj); } 
};


template<typename Ctx>
void undo_trail_stack(Ctx & ctx, ptr_vector<trail<Ctx> > & s, unsigned old_size) {
    SASSERT(old_size <= s.size());
    typename ptr_vector<trail<Ctx> >::iterator begin = s.begin() + old_size;
    typename ptr_vector<trail<Ctx> >::iterator it    = s.end();
    while (it != begin) {
        --it;
        (*it)->undo(ctx);
    }
    s.shrink(old_size);
}

template<typename Ctx>
class trail_stack {
    Ctx &                   m_ctx;
    ptr_vector<trail<Ctx> > m_trail_stack;
    unsigned_vector         m_scopes;
    region                  m_region;
public:
    trail_stack(Ctx & c):m_ctx(c) {}

    ~trail_stack() {}
    
    region & get_region() { return m_region; }
    
    void reset() { 
        pop_scope(m_scopes.size()); 
        // Undo trail objects stored at lvl 0 (avoid memory leaks if lvl 0 contains new_obj_trail objects).
        undo_trail_stack(m_ctx, m_trail_stack, 0); 
    }

    void push_ptr(trail<Ctx> * t) { m_trail_stack.push_back(t); }

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
        undo_trail_stack(m_ctx, m_trail_stack, old_size);
        m_scopes.shrink(new_lvl);
        m_region.pop_scope(num_scopes);
    }
};

#endif /* TRAIL_H_ */

