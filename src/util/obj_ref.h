/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    obj_ref.h

Abstract:

    Smart pointer.

Author:

    Leonardo de Moura (leonardo) 2008-01-03.

Revision History:

--*/
#ifndef OBJ_REF_H_
#define OBJ_REF_H_

/**
   Smart pointer for T objects.
   TManager must provide the functions:
   - void dec_ref(T * obj)
   - void inc_ref(T * obj)
*/
template<typename T, typename TManager>
class obj_ref {
    T *        m_obj;
    TManager & m_manager;

    void dec_ref() { if (m_obj) m_manager.dec_ref(m_obj); }
    void inc_ref() { if (m_obj) m_manager.inc_ref(m_obj); }

public:
    typedef TManager manager;

    obj_ref(T * n, TManager & m):
        m_obj(n),
        m_manager(m) {
        inc_ref();
    }

    explicit obj_ref(TManager & m):
        m_obj(nullptr),
        m_manager(m) {
    }

    obj_ref(obj_ref const & n):
        m_obj(n.m_obj),
        m_manager(n.m_manager) {
        inc_ref();
    }

    obj_ref(obj_ref && other) : m_obj(nullptr), m_manager(other.m_manager) {
        std::swap(m_obj, other.m_obj);
    }

    ~obj_ref() { dec_ref(); }

    TManager & get_manager() const { return m_manager; }

    TManager & m() const { return m_manager; }

    T * operator->() const { return m_obj; }

    T * get() const { return m_obj; }

    operator bool() const { return m_obj != nullptr; }

    bool operator!() const { return m_obj == nullptr; }

    operator T*() const { return m_obj; }

    T const & operator*() const { return *m_obj; }

    obj_ref & operator=(T * n) {
        if (n) {
            m_manager.inc_ref(n);
        }
        dec_ref();
        m_obj = n;
        return *this;
    }
    
    obj_ref & operator=(obj_ref & n) {
        SASSERT(&m_manager == &n.m_manager);
        n.inc_ref();
        dec_ref();
        m_obj = n.m_obj;
        return *this;
    }

    obj_ref & operator=(obj_ref && n) {
        SASSERT(&m_manager == &n.m_manager);
        if (this != &n) {
            std::swap(m_obj, n.m_obj);
            n.reset();
        }
        return *this;
    }

    void reset() {
        dec_ref();
        m_obj = nullptr;
    }

    void swap(obj_ref & n) {
        std::swap(m_obj, n.m_obj);
    }

    /**
       \brief Steal ownership without decrementing the reference counter.
    */
    T * steal() { 
        T * r = m_obj;
        m_obj = nullptr;
        return r;
    }
};

template<typename T, typename TManager>
inline bool operator==(obj_ref<T, TManager> const & n1, obj_ref<T, TManager> const & n2) {
    return n1.get() == n2.get();
}

template<typename T1, typename T2, typename TManager>
inline bool operator==(obj_ref<T1, TManager> const & n1, obj_ref<T2, TManager> const & n2) {
    return n1.get() == n2.get();
}

template<typename T, typename TManager>
inline bool operator!=(obj_ref<T, TManager> const & n1, obj_ref<T, TManager> const & n2) {
    return n1.get() != n2.get();
}

template<typename T1, typename T2, typename TManager>
inline bool operator!=(obj_ref<T1, TManager> const & n1, obj_ref<T2, TManager> const & n2) {
    return n1.get() != n2.get();
}

template<typename IT, typename TManager>
inline void dec_range_ref(IT const & begin, IT const & end, TManager & m) {
    for (IT it = begin; it != end; ++it) {
        if (*it) {
            m.dec_ref(*it);
        }
    }
}

#endif /* OBJ_REF_H_ */
