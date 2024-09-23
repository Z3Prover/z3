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
#include "util/debug.h"
#include "util/util.h"

#define DLIST_EXTRA_ASSERTIONS 0

template <typename T> class dll_iterator;

template <typename T>
class dll_base {
    T* m_next = nullptr;
    T* m_prev = nullptr;

protected:
    dll_base() = default;
    ~dll_base() = default;

public:
    dll_base(dll_base const&) = delete;
    dll_base(dll_base&&) = delete;
    dll_base& operator=(dll_base const&) = delete;
    dll_base& operator=(dll_base&&) = delete;

    T* prev() { return m_prev; }
    T* next() { return m_next; }
    T const* prev() const { return m_prev; }
    T const* next() const { return m_next; }

    void init(T* t) {
        m_next = t;
        m_prev = t;
        SASSERT(invariant());
    }

    static T* pop(T*& list) {
        if (!list)
            return list;
        T* head = list;
        remove_from(list, head);
        return head;
    }

    void insert_after(T* other) {
#if DLIST_EXTRA_ASSERTIONS
        SASSERT(other);
        SASSERT(invariant());
        SASSERT(other->invariant());
        size_t const old_sz1 = count_if(*static_cast<T*>(this), [](T const&) { return true; });
        size_t const old_sz2 = count_if(*other, [](T const&) { return true; });
#endif
        // have:        this -> next -> ...
        // insert:      other -> ... -> other_end
        // result:      this -> other -> ... -> other_end -> next -> ...
        T* next = this->m_next;
        T* other_end = other->m_prev;
        this->m_next = other;
        other->m_prev = static_cast<T*>(this);
        other_end->m_next = next;
        next->m_prev = other_end;
#if DLIST_EXTRA_ASSERTIONS
        SASSERT(invariant());
        SASSERT(other->invariant());
        size_t const new_sz = count_if(*static_cast<T*>(this), [](T const&) { return true; });
        SASSERT_EQ(new_sz, old_sz1 + old_sz2);
#endif
    }

    void insert_before(T* other) {
#if DLIST_EXTRA_ASSERTIONS
        SASSERT(other);
        SASSERT(invariant());
        SASSERT(other->invariant());
        size_t const old_sz1 = count_if(*static_cast<T*>(this), [](T const&) { return true; });
        size_t const old_sz2 = count_if(*other, [](T const&) { return true; });
#endif
        // have:        prev -> this -> ...
        // insert:      other -> ... -> other_end
        // result:      prev -> other -> ... -> other_end -> this -> ...
        T* prev = this->m_prev;
        T* other_end = other->m_prev;
        prev->m_next = other;
        other->m_prev = prev;
        other_end->m_next = static_cast<T*>(this);
        this->m_prev = other_end;
#if DLIST_EXTRA_ASSERTIONS
        SASSERT(invariant());
        SASSERT(other->invariant());
        size_t const new_sz = count_if(*static_cast<T*>(this), [](T const&) { return true; });
        SASSERT_EQ(new_sz, old_sz1 + old_sz2);
#endif
    }
    
    static void remove_from(T*& list, T* elem) {
#if DLIST_EXTRA_ASSERTIONS
        SASSERT(list);
        SASSERT(elem);
        SASSERT(list->invariant());
        SASSERT(elem->invariant());
#endif
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
#if DLIST_EXTRA_ASSERTIONS
        SASSERT(list->invariant());
#endif
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
    static dll_iterator mk_begin(T const* list) {
        // Setting first==(bool)list makes this also work for list==nullptr;
        // but we can't implement top-level begin/end for pointers because it clashes with the definition for arrays.
        return {list, (bool)list};
    }

    static dll_iterator mk_end(T const* list) {
        return {list, false};
    }

    using value_type = T;
    using pointer = T const*;
    using reference = T const&;
    using iterator_category = std::input_iterator_tag;
    using difference_type = std::ptrdiff_t;

    dll_iterator& operator++() {
        m_elem = m_elem->next();
        m_first = false;
        return *this;
    }

    T const& operator*() const {
        return *m_elem;
    }
    bool operator!=(dll_iterator const& other) const {
        return m_elem != other.m_elem || m_first != other.m_first;
    }
};

template <typename T>
class dll_elements {
    T const* m_list;
public:
    dll_elements(T const* list) : m_list(list) {}
    dll_iterator<T> begin() const { return dll_iterator<T>::mk_begin(m_list); }
    dll_iterator<T> end() const { return dll_iterator<T>::mk_end(m_list); }
};

template < typename T
         , typename U = std::enable_if_t<std::is_base_of_v<dll_base<T>, T>>  // should only match if T actually inherits from dll_base<T>
         >
dll_iterator<T> begin(T const& list) {
    return dll_iterator<T>::mk_begin(&list);
}

template < typename T
         , typename U = std::enable_if_t<std::is_base_of_v<dll_base<T>, T>>  // should only match if T actually inherits from dll_base<T>
         >
dll_iterator<T> end(T const& list)
{
    return dll_iterator<T>::mk_end(&list);
}
