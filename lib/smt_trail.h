/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_trail.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#ifndef _SMT_TRAIL_H_
#define _SMT_TRAIL_H_

namespace smt {

    class context;

    class trail {
    public:
        virtual ~trail() {
        }
        virtual void undo(context & ctx) = 0;
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
        
        virtual ~value_trail() {
        }
        
        virtual void undo(context & ctx) {
            m_value = m_old_value;
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
        
        virtual void undo(context & ctx) {
            m_ptr = 0;
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
        
        virtual ~vector_value_trail() {
        }
        
        virtual void undo(context & ctx) {
            m_vector[m_idx] = m_old_value;
        }
    };
    
    template<typename T, bool CallDestructors=true>
    class push_back_trail : public trail {
        vector<T, CallDestructors> & m_vector;
    public:
        push_back_trail(vector<T, CallDestructors> & v):
            m_vector(v) {
        }
        
        virtual void undo(context & ctx) {
            m_vector.pop_back();
        }
    };
    
    class set_bitvector_trail : public trail {
        svector<bool> & m_vector;
        unsigned        m_idx;
    public:
        set_bitvector_trail(svector<bool> & v, unsigned idx):
            m_vector(v),
            m_idx(idx) {
            SASSERT(m_vector[m_idx] == false);
            m_vector[m_idx] = true;
        }
        
        virtual void undo(context & ctx) {
            m_vector[m_idx] = false;
        }
    };
    
    template<typename T>
    class new_obj_trail : public trail {
        T * m_obj;
    public:
        new_obj_trail(T * obj):
            m_obj(obj) {
        }
        
        virtual void undo(context & ctx) {
            dealloc(m_obj);
        }
    };

};

#endif /* _SMT_TRAIL_H_ */

