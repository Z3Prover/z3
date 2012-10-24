/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dlist.h

Abstract:

    Templates for manipulating doubly linked lists.

Author:

    Leonardo de Moura (leonardo) 2011-01-25.

Revision History:

--*/
#ifndef __DLIST_H_
#define __DLIST_H_

/**
   Add element \c elem to the list headed by \c head.
   NextProc and PrevProc must have the methods:
      T * & operator()(T *);
      T * & operator()(T *);
   They should return the next and prev fields of the given object.
*/
template<typename T, typename NextProc, typename PrevProc>
void dlist_add(T * & head, T * elem, NextProc const & next = NextProc(), PrevProc const & prev = PrevProc()) {
    SASSERT(prev(elem) == 0);
    SASSERT(next(elem) == 0);
    if (head == 0) {
        head = elem;
    }
    else {
        next(elem) = head;
        prev(head) = elem;
        head       = elem;
    }
}

template<typename T, typename NextProc, typename PrevProc>
void dlist_del(T * & head, T * elem, NextProc const & next = NextProc(), PrevProc const & prev = PrevProc()) {
    T * & prev_elem = prev(elem);
    T * & next_elem = next(elem);
    if (head == elem) {
        SASSERT(prev_elem == 0);
        if (next_elem != 0)
            prev(next_elem) = 0;
        head = next_elem;
    }
    else {
        SASSERT(prev_elem != 0);
        next(prev_elem) = next_elem;
        if (next_elem != 0)
            prev(next_elem) = prev_elem;
    }
    prev_elem = 0;
    next_elem = 0;
}

/**
   \brief Remove the head of the list. Return the old head.
*/
template<typename T, typename NextProc, typename PrevProc>
T * dlist_pop(T * & head, NextProc const & next = NextProc(), PrevProc const & prev = PrevProc()) {
    if (head == 0) {
        return 0;
    }
    else {
        SASSERT(prev(head) == 0);
        T * r = head;
        head = next(head);
        if (head)
            prev(head) = 0;
        next(r) = 0;
        return r;
    }
}

/**
   \brief Insert new element after elem.
*/
template<typename T, typename NextProc, typename PrevProc>
void dlist_insert_after(T * elem, T * new_elem, NextProc const & next = NextProc(), PrevProc const & prev = PrevProc()) {
    SASSERT(elem);
    SASSERT(new_elem);
    T * & old_next_elem = next(elem);
    prev(new_elem) = elem;
    next(new_elem) = old_next_elem;
    if (old_next_elem)
        prev(old_next_elem) = new_elem;
    // next(elem) = new_elem;
    old_next_elem = new_elem;
}

template<typename T, typename NextProc>
bool dlist_contains(T * head, T const * elem, NextProc const & next = NextProc()) {
    T * curr = head;
    while (curr != 0) {
        if (curr == elem)
            return true;
        curr = next(curr);
    }
    return false;
}

template<typename T, typename NextProc>
unsigned dlist_length(T * head, NextProc const & next = NextProc()) {
    unsigned r = 0;
    T * curr = head;
    while (curr != 0) {
        r++;
        curr = next(curr);
    }
    return r;
}

template<typename T, typename NextProc, typename PrevProc>
bool dlist_check_invariant(T * head, NextProc const & next = NextProc(), PrevProc const & prev = PrevProc()) {
    if (head == 0)
        return true;
    SASSERT(prev(head) == 0);
    T * old  = head;
    T * curr = next(head);
    while (curr != 0) {
        SASSERT(prev(curr) == old);
        old = curr;
        curr = next(curr);
    }
    return true;
}

#endif


