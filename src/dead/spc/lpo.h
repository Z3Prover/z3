/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    lpo.h

Abstract:

    Lexicographical Path Ordering

Author:

    Leonardo de Moura (leonardo) 2008-02-01.

Revision History:

--*/
#ifndef _LPO_H_
#define _LPO_H_

#include"order.h"
#include"vector.h"
#include"map.h"

class lpo : public order {
    svector<expr_offset>  m_todo;

    bool occurs(expr_offset const & t1, expr_offset const & t2);
    bool greater(expr_offset s, expr_offset t, unsigned depth);
    bool dominates_args(expr_offset s, expr_offset t, unsigned depth);
    bool arg_dominates_expr(expr_offset s, expr_offset t, unsigned depth);
    result lex_compare(expr_offset s, expr_offset t, unsigned depth);
    result compare_core(expr_offset s, expr_offset t, unsigned depth);
    result compare(expr_offset s, expr_offset t, unsigned depth);
    bool max_depth(unsigned d) { /* TODO */ return false; }
public:
    lpo(ast_manager & m, precedence * p):order(m, p) {}
    virtual ~lpo() {}
    
    virtual result compare(expr_offset const & t1, expr_offset const & t2, substitution * s);
    result compare(expr * t1, expr * t2) { return compare(expr_offset(t1, 0), expr_offset(t2, 0), static_cast<substitution*>(0)); }

    virtual bool greater(expr_offset const & t1, expr_offset const & t2, substitution * s);
    bool greater(expr_offset const & t1, expr_offset const & t2) { return greater(t1, t2); }
    virtual int compare_ge(expr_offset const & t1, expr_offset const & t2, substitution * s);
};

#endif /* _LPO_H_ */
