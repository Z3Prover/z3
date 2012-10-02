/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_list.h

Abstract:

    Quick hack to have lists of ASTs.
    The lists have hash-consing.
    This is a substitute for the old expr_lists implemented on top of the ASTs.
    The new lists live in a different manager and do not affect the ast_manager.

Author:

    Leonardo de Moura (leonardo) 2011-01-06.

Revision History:

--*/
#ifndef _AST_LIST_H_
#define _AST_LIST_H_

#include"ast.h"

template<typename AST>
class ast_list_manager_tpl;

template<typename AST>
class ast_list_tpl {
public:
    typedef ast_list_tpl  list;
private:
    unsigned m_id;
    unsigned m_is_nil:1;
    unsigned m_ref_count:31;
    AST  *   m_head;
    list *   m_tail;

    ast_list_tpl():
        m_is_nil(true),
        m_ref_count(0),
        m_head(0),
        m_tail(0) {
    }

    ast_list_tpl(AST * h, list * t):
        m_is_nil(false),
        m_ref_count(0),
        m_head(h),
        m_tail(t) {
    }

    friend class ast_list_manager_tpl<AST>;

    struct hash_proc;
    friend struct hash_proc;
    
    struct hash_proc {
        unsigned operator()(ast_list_tpl * l) const {
            unsigned h1 = l->m_head ? l->m_head->get_id() : 5;
            unsigned h2 = l->m_tail ? l->m_tail->get_id() : 7;
            return hash_u_u(h1, h2);
        }
    };

    struct eq_proc;
    friend struct eq_proc;

    struct eq_proc {
        bool operator()(ast_list_tpl * l1, ast_list_tpl * l2) const {
            return l1->m_head == l2->m_head && l1->m_tail == l2->m_tail; 
        }
    };

    typedef ptr_hashtable<list, hash_proc, eq_proc> table; // for hash consing

public:
    unsigned get_id() const { return m_id; }
    unsigned get_ref_count() const { return m_ref_count; }
    unsigned hash() const { return m_id; }

    friend inline bool is_nil(list const * l) { return l->m_is_nil == true; }
    friend inline bool is_cons(list const * l) { return !is_nil(l); }
    friend inline AST * head(list const * l) { SASSERT(is_cons(l)); return l->m_head; }
    friend inline list * tail(list const * l) { SASSERT(is_cons(l)); return l->m_tail; }
};

template<typename AST>
class ast_list_manager_tpl {
public:
    typedef ast_list_tpl<AST>   list;
    typedef obj_hashtable<list> list_set;
private:
    typedef typename list::table table;
    ast_manager &          m_manager;
    small_object_allocator m_allocator;
    table                  m_table;
    id_gen                 m_id_gen;
    list                   m_nil;

public:    
    ast_list_manager_tpl(ast_manager & m):
        m_manager(m),
        m_nil() {
        m_nil.m_id = m_id_gen.mk();
        m_nil.m_ref_count = 1;
    }

    void inc_ref(list * l) {
        if (l != 0) {
            l->m_ref_count++;
        }
    }

    void dec_ref(list * l) {
        while (l != 0) {
            SASSERT(l->m_ref_count > 0);
            l->m_ref_count--;
            if (l->m_ref_count > 0) 
                return;
            SASSERT(l != &m_nil);
            m_table.erase(l);
            m_manager.dec_ref(l->m_head);
            m_id_gen.recycle(l->m_id);
            list * old_l = l;
            l = l->m_tail;
            m_allocator.deallocate(sizeof(list), old_l);
        }
    }

    list * mk_nil() { return &m_nil; }

    list * mk_cons(AST * h, list * l) {
        list tmp(h, l);
        list * r = 0;
        if (m_table.find(&tmp, r)) 
            return r;
        r = new (m_allocator.allocate(sizeof(list))) list(h, l);
        m_manager.inc_ref(h);
        inc_ref(l);
        r->m_id = m_id_gen.mk();
        m_table.insert(r);
        return r;
    }
};

typedef ast_list_tpl<expr>         expr_list;
typedef ast_list_manager_tpl<expr> expr_list_manager;

typedef ast_list_tpl<quantifier>         quantifier_list;
typedef ast_list_manager_tpl<quantifier> quantifier_list_manager;

typedef obj_ref<expr_list, expr_list_manager> expr_list_ref;
typedef obj_ref<quantifier_list, quantifier_list_manager> quantifier_list_ref;
typedef ref_vector<expr_list, expr_list_manager> expr_list_ref_vector;
typedef ref_vector<quantifier_list, quantifier_list_manager> quantifier_list_ref_vector;

#endif
