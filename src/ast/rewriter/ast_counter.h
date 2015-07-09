/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    ast_counter.h

Abstract:

    Routines for counting features of terms, such as free variables.

Author:

    Nikolaj Bjorner (nbjorner) 2013-03-18.
    Krystof Hoder (t-khoder) 2010-10-10.

Revision History:

    Hoisted from dl_util.h 2013-03-18.

--*/


#ifndef AST_COUNTER_H_
#define AST_COUNTER_H_

#include "ast.h"
#include "map.h"
#include "uint_set.h"
#include "var_subst.h"

class counter {
protected:
    typedef u_map<int> map_impl;
    map_impl m_data;
public:
    typedef map_impl::iterator iterator;
    
    counter() {}
    
    void reset() { m_data.reset(); }
    iterator begin() const { return m_data.begin(); }
    iterator end() const { return m_data.end(); }    
    void update(unsigned el, int delta);
    int & get(unsigned el);

    /**
       \brief Increase values of elements in \c els by \c delta.
       
       The function returns a reference to \c *this to allow for expressions like
       counter().count(sz, arr).get_positive_count()
    */
    counter & count(unsigned sz, const unsigned * els, int delta = 1);
    counter & count(const unsigned_vector & els, int delta = 1) {
        return count(els.size(), els.c_ptr(), delta);
    }
    
    void collect_positive(uint_set & acc) const;
    unsigned get_positive_count() const;

    bool get_max_positive(unsigned & res) const;
    unsigned get_max_positive() const;

    /**
       Since the default counter value of a counter is zero, the result is never negative.
    */
    int get_max_counter_value() const;
};

class var_counter : public counter {
protected:
    expr_fast_mark1  m_visited;
    expr_free_vars   m_fv;
    ptr_vector<expr> m_todo;
    unsigned_vector  m_scopes;
    unsigned get_max_var(bool & has_var);    
public:
    var_counter() {}
    void count_vars(const app * t, int coef = 1);
    unsigned get_max_var(expr* e);
    unsigned get_next_var(expr* e);
};

class ast_counter {
    typedef obj_map<ast, int> map_impl;
    map_impl m_data;
 public:
    typedef map_impl::iterator iterator;
    
    ast_counter() {}
    
    iterator begin() const { return m_data.begin(); }
    iterator end() const { return m_data.end(); }
    
    int & get(ast * el) {
        return m_data.insert_if_not_there2(el, 0)->get_data().m_value;
    }
    void update(ast * el, int delta){
        get(el) += delta;
    }
    
    void inc(ast * el) { update(el, 1); }
    void dec(ast * el) { update(el, -1); }
};

#endif
