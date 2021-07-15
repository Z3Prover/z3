/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dlist.h

Abstract:

    Templates for manipulating circular doubly linked lists.

Author:

    Leonardo de Moura (leonardo) 2011-01-25.

Revision History:

--*/
#pragma once


template<typename T>
class dll_base {
    T* m_next { nullptr };
    T* m_prev { nullptr };
public:

    T* prev() { return m_prev; }
    T* next() { return m_next; }

    void init(T* t) {
        m_next = t;
        m_prev = t;
    }

    static T* pop(T*& list) {
        if (!list)
            return list;
        T* head = list;
        remove_from(list, head);
        return head;
    }
    
    static void remove_from(T*& list, T* elem) {
        if (list->m_next == list) {
            SASSERT(elem == list);
            list = nullptr;
            return;
        }            
        if (list == elem)
            list = elem->m_next;
        auto* next = elem->m_next;
        auto* prev = elem->m_prev;
        prev->m_next = next;
        next->m_prev = prev;        
    }

    static void push_to_front(T*& list, T* elem) {
        if (!list) {
            list = elem;
            elem->m_next = elem;
            elem->m_prev = elem;            
        }
        else if (list != elem) {
            auto* next = elem->m_next;
            auto* prev = elem->m_prev;
            prev->m_next = next;
            next->m_prev = prev;        
            list->m_prev->m_next = elem;
            elem->m_prev = list->m_prev;
            elem->m_next = list;
            list->m_prev = elem;
            list = elem;
        }
    }

    static void detach(T* elem) {
        elem->init(elem);
    }

    bool invariant() const {
        auto* e = this;
        do {
            if (e->m_next->m_prev != e)
                return false;
            e = e->m_next;
        }
        while (e != this);
        return true;
    }


    static bool contains(T* list, T* elem) {
        if (!list)
            return false;
        T* first = list;
        do {
            if (list == elem)
                return true;
            list = list->m_next;
        }         
        while (list != first);
        return false;
    }
};



