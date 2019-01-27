/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    factor_equivs.h

Abstract:
  Factor equivalence classes out of an expression.

  "Equivalence class structure" for objs. Uses a union_find structure internally.
  Operations are :
  -Declare a new equivalence class with a single element
  -Merge two equivalence classes
  -Retrieve whether two elements are in the same equivalence class
  -Iterate on all the elements of the equivalence class of a given element
  -Iterate on all equivalence classes (and then within them)

Author:

    Julien Braine
    Arie Gurfinkel

Revision History:

*/

#ifndef FACTOR_EQUIVS_H_
#define FACTOR_EQUIVS_H_

#include "util/union_find.h"
#include "ast/ast_util.h"

///All functions naturally add their parameters to the union_find class
template<typename OBJ, typename Manager>
class obj_equiv_class {
    basic_union_find m_uf;
    obj_map<OBJ, unsigned> m_to_int;
    ref_vector<OBJ, Manager> m_to_obj;

    unsigned add_elem_impl(OBJ*o) {
        unsigned id = m_to_obj.size();
        m_to_int.insert(o, id);
        m_to_obj.push_back(o);
        return id;
    }
    unsigned add_if_not_there(OBJ*o) {
        unsigned id;
        if(!m_to_int.find(o, id)) {
            id = add_elem_impl(o);
        }
        return id;
    }

public:
    class iterator;
    class equiv_iterator;
    friend class iterator;
    friend class equiv_iterator;

    obj_equiv_class(Manager& m) : m_to_obj(m) {}

    Manager &m() const {return m_to_obj.m();}

    void add_elem(OBJ*o) {
        SASSERT(!m_to_int.find(o));
        add_elem_impl(o);
    }

    //Invalidates all iterators
    void merge(OBJ* a, OBJ* b) {
        unsigned v1 = add_if_not_there(a);
        unsigned v2 = add_if_not_there(b);
        unsigned tmp1 = m_uf.find(v1);
        unsigned tmp2 = m_uf.find(v2);
        m_uf.merge(tmp1, tmp2);
    }

    void reset() {
        m_uf.reset();
        m_to_int.reset();
        m_to_obj.reset();
    }

    bool are_equiv(OBJ*a, OBJ*b) {
        unsigned id1 = add_if_not_there(a);
        unsigned id2 = add_if_not_there(b);
        return m_uf.find(id1) == m_uf.find(id2);
    }

    class iterator {
        friend class obj_equiv_class;
    private :
        const obj_equiv_class& m_ouf;
        unsigned m_curr_id;
        bool m_first;
        iterator(const obj_equiv_class& uf, unsigned id, bool f) :
            m_ouf(uf), m_curr_id(id), m_first(f) {}
    public :
        OBJ*operator*() {return m_ouf.m_to_obj[m_curr_id];}

        iterator& operator++() {
            m_curr_id = m_ouf.m_uf.next(m_curr_id);
            m_first = false;
            return *this;
        }
        bool operator==(const iterator& o) {
            SASSERT(&m_ouf == &o.m_ouf);
            return  m_first == o.m_first && m_curr_id == o.m_curr_id;
        }
        bool operator!=(const iterator& o) {return !(*this == o);}
    };

    iterator begin(OBJ*o) {
        unsigned id = add_if_not_there(o);
        return iterator(*this, id, true);
    }
    iterator end(OBJ*o) {
        unsigned id = add_if_not_there(o);
        return iterator(*this, id, false);
    }

    class eq_class {
    private :
        iterator m_begin;
        iterator m_end;
    public :
        eq_class(const iterator& a, const iterator& b) : m_begin(a), m_end(b) {}
        iterator begin() {return m_begin;}
        iterator end() {return m_end;}
    };

    class equiv_iterator {
        friend class obj_equiv_class;
    private :
        const obj_equiv_class& m_ouf;
        unsigned m_rootnb;
        equiv_iterator(const obj_equiv_class& uf, unsigned nb) :
            m_ouf(uf), m_rootnb(nb) {
            while(m_rootnb != m_ouf.m_to_obj.size() &&
                  m_ouf.m_uf.is_root(m_rootnb) != true)
            { m_rootnb++; }
        }
    public :
        eq_class operator*() {
            return eq_class(iterator(m_ouf, m_rootnb, true),
                            iterator(m_ouf, m_rootnb, false));
        }
        equiv_iterator& operator++() {
            do {
                m_rootnb++;
            } while(m_rootnb != m_ouf.m_to_obj.size() &&
                    m_ouf.m_uf.is_root(m_rootnb) != true);
            return *this;
        }
        bool operator==(const equiv_iterator& o) {
            SASSERT(&m_ouf == &o.m_ouf);
            return m_rootnb == o.m_rootnb;
        }
        bool operator!=(const equiv_iterator& o) {return !(*this == o);}
    };

    equiv_iterator begin() {return equiv_iterator(*this, 0);}
    equiv_iterator end() {return equiv_iterator(*this, m_to_obj.size());}
};

typedef obj_equiv_class<expr, ast_manager> expr_equiv_class;


/**
 *  Factors input vector v into equivalence classes and the rest
 */
void factor_eqs(expr_ref_vector &v, expr_equiv_class &equiv);
/**
 * Rewrite expressions in v by choosing a representative from the
 * equivalence class.
 */
void rewrite_eqs(expr_ref_vector &v, expr_equiv_class &equiv);
/**
 * converts equivalence classes to equalities
 */
void equiv_to_expr(expr_equiv_class &equiv, expr_ref_vector &out);

/**
 * expands equivalence classes to all derivable equalities
 */
bool equiv_to_expr_full(expr_equiv_class &equiv, expr_ref_vector &out);


#endif
