/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    order.h

Abstract:

    Abstract class for term orderings.

Author:

    Leonardo de Moura (leonardo) 2008-01-28.

Revision History:

--*/
#ifndef _ORDER_H_
#define _ORDER_H_

#include"substitution.h"
#include"precedence.h"
#include"trace.h"

class order {
protected:
    ast_manager &  m_manager;
    precedence *   m_precedence;
    substitution * m_subst;

    typedef std::pair<expr_offset, expr_offset> expr_offset_pair;
    svector<expr_offset_pair> m_eq_todo;

    expr_offset find(expr_offset t) {
        while (m_subst && is_var(t.get_expr()) && m_subst->find(to_var(t.get_expr()), t.get_offset(), t))
            ;
        return t;
    }

    bool f_greater(func_decl * f, func_decl * g) const {
        bool r = m_precedence->compare(f, g) > 0;
        TRACE("order", tout << f->get_name() << " greater than " << g->get_name() << " == " << r << "\n";);
        return r;
    }
public:
    enum result {
        UNKNOWN,
        UNCOMPARABLE,
        EQUAL,
        GREATER,
        LESSER,
        NOT_GTEQ
    };
    static bool ok(result r) { return r == EQUAL || r == GREATER || r == LESSER; }
    order(ast_manager & m, precedence * p):m_manager(m), m_precedence(p) { SASSERT(p); }
    virtual ~order() { dealloc(m_precedence); }
    virtual void reserve(unsigned num_offsets, unsigned num_vars) {}
    virtual void reserve_offsets(unsigned num_offsets) {}
    virtual void reserve_vars(unsigned num_vars) {}
    ast_manager & get_manager() { return m_manager; }

    virtual result compare(expr_offset const & t1, expr_offset const & t2, substitution * s) = 0;
    result compare(expr * t1, expr * t2, unsigned offset, substitution * s) { return compare(expr_offset(t1, offset), expr_offset(t2, offset), s); }
    result compare(expr * t1, expr * t2) { return compare(expr_offset(t1, 0), expr_offset(t2, 0), 0); }
    virtual bool greater(expr_offset const & t1, expr_offset const & t2, substitution * s) = 0;
    bool greater(expr * t1, expr * t2) { return greater(expr_offset(t1,0), expr_offset(t2,0), 0); }
    bool greater(expr * t1, expr * t2, substitution * s) { return greater(expr_offset(t1,0), expr_offset(t2,0), s); }
    bool greater(expr * t1, expr * t2, unsigned offset, substitution * s) { 
        return greater(expr_offset(t1, offset), expr_offset(t2, offset), s); 
    }
    /**
       \brief Return a value > 0 if t1 is greater than t2, 0 if t1 == t2, and < 0 otherwise (uncomparable, unknown, lesser).
    */
    virtual int compare_ge(expr_offset const & t1, expr_offset const & t2, substitution * s) = 0;

    /**
       \brief Return true if the given terms are equal modulo the given substitution
    */
    bool equal(expr_offset const & t1, expr_offset const & t2, substitution * s);

    bool equal(expr * t1, expr * t2, unsigned offset = 0, substitution * s = 0) {
        return equal(expr_offset(t1, offset), expr_offset(t2, offset), s);
    }
};

#endif /* _ORDER_H_ */
