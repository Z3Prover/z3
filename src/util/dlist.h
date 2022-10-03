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
#include <type_traits>

template <typename T> class dll_iterator;

template <typename T>
class dll_base {
    T* m_next { nullptr };
    T* m_prev { nullptr };
public:

    T* prev() { return m_prev; }
    T* next() { return m_next; }
    T const* prev() const { return m_prev; }
    T const* next() const { return m_next; }

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

    void insert_after(T* elem) {
        T* next = this->m_next;
        elem->m_prev = next->m_prev;
        elem->m_next = next;
        this->m_next = elem;
        next->m_prev = elem;
    }

    void insert_before(T* elem) {
        T* prev = this->m_prev;
        elem->m_next = prev->m_next;
        elem->m_prev = prev;
        prev->m_next = elem;
        this->m_prev = elem;
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

    static bool contains(T const* list, T const* elem) {
        if (!list)
            return false;
        T const* first = list;
        do {
            if (list == elem)
                return true;
            list = list->m_next;
        }         
        while (list != first);
        return false;
    }
};

template <typename T>
class dll_iterator {
    T const* m_elem;
    bool m_first;

    dll_iterator(T const* elem, bool first): m_elem(elem), m_first(first) { }

public:
    static dll_iterator mk_begin(T const* elem) {
        // Setting first==(bool)elem makes this also work for elem==nullptr;
        // but we can't implement top-level begin/end for pointers because it clashes with the definition for arrays.
        return {elem, (bool)elem};
    }

    static dll_iterator mk_end(T const* elem) {
        return {elem, false};
    }

    // using value_type = T;
    // using pointer = T const*;
    // using reference = T const&;
    // using iterator_category = std::input_iterator_tag;

    dll_iterator& operator++() {
        m_elem = m_elem->next();
        m_first = false;
        return *this;
    }

    T const& operator*() const {
        return *m_elem;
    }

    bool operator==(dll_iterator const& other) const {
        return m_elem == other.m_elem && m_first == other.m_first;
    }

    bool operator!=(dll_iterator const& other) const {
        return !operator==(other);
    }
};

template < typename T
         , typename U = std::enable_if_t<std::is_base_of_v<dll_base<T>, T>>  // should only match if T actually inherits from dll_base<T>
         >
dll_iterator<T> begin(T const& elem) {
    return dll_iterator<T>::mk_begin(&elem);
}

template < typename T
         , typename U = std::enable_if_t<std::is_base_of_v<dll_base<T>, T>>  // should only match if T actually inherits from dll_base<T>
         >
dll_iterator<T> end(T const& elem)
{
    return dll_iterator<T>::mk_end(&elem);
}
