/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    obj_equiv_class.h

Abstract:
  "Equivalence class structure" for objs. Uses a union_find structure internally.
  Operations are :
  -Declare a new equivalence class with a single element
  -Merge two equivalence classes
  -Retrieve whether two elements are in the same equivalence class
  -Iterate on all the elements of the equivalence class of a given element
  -Iterate on all equivalence classes (and then within them)

Author:

    Julien Braine

Revision History:

*/

#ifndef OBJ_EQUIV_CLASS_H_
#define OBJ_EQUIV_CLASS_H_

#include "union_find.h"
#include "ast_util.h"

namespace spacer {
//All functions naturally add their parameters to the union_find class
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
   Factors input vector v into equivalence classes and the rest
 */
inline void factor_eqs(expr_ref_vector &v, expr_equiv_class &equiv) {
    ast_manager &m = v.get_manager();
    arith_util arith(m);
    expr *e1, *e2;

    flatten_and(v);
    unsigned j = 0;
    for (unsigned i = 0; i < v.size(); ++i) {
        if (m.is_eq(v.get(i), e1, e2)) {
            if (arith.is_zero(e1)) {
                expr* t;
                t = e1; e1 = e2; e2 = t;
            }

            // y + -1*x == 0
            if (arith.is_zero(e2) && arith.is_add(e1) &&
                to_app(e1)->get_num_args() == 2) {
                expr *a0, *a1, *x;

                a0 = to_app(e1)->get_arg(0);
                a1 = to_app(e1)->get_arg(1);

                if (arith.is_times_minus_one(a1, x)) {
                    e1 = a0;
                    e2 = x;
                }
                else if (arith.is_times_minus_one(a0, x)) {
                    e1 = a1;
                    e2 = x;
                }
            }
            equiv.merge(e1, e2);
        }
        else {
            if (j < i) {v[j] = v.get(i);}
            j++;
        }
    }
    v.shrink(j);
}

/**
 * converts equivalence classes to equalities
 */
inline void equiv_to_expr(expr_equiv_class &equiv, expr_ref_vector &out) {
    ast_manager &m = out.get_manager();
    for (auto eq_class : equiv) {
        expr *rep = nullptr;
        for (expr *elem : eq_class) {
            if (!m.is_value (elem)) {
                rep = elem;
                break;
            }
        }
        SASSERT(rep);
        for (expr *elem : eq_class) {
            if (rep != elem) {out.push_back (m.mk_eq (rep, elem));}
        }
    }
}

/**
 * expands equivalence classes to all derivable equalities
 */
inline bool equiv_to_expr_full(expr_equiv_class &equiv, expr_ref_vector &out) {
    ast_manager &m = out.get_manager();
    bool dirty = false;
    for (auto eq_class : equiv) {
        for (auto a = eq_class.begin(), end = eq_class.end(); a != end; ++a) {
            expr_equiv_class::iterator b(a);
            for (++b; b != end; ++b) {
                out.push_back(m.mk_eq(*a, *b));
                dirty = true;
            }
        }
    }
    return dirty;
}

}

#endif
