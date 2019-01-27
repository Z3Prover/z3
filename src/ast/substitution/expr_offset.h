/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    expr_offset.h

Abstract:

    Expressions + Offsets. 
    In order to avoid creating variants of terms, we use a pair (expression, offset),
    where offset is just a small integer.
    Non ground terms with different offsets are always considered
    disequal. For example, (f x):1 is different from (f x):2, and 
    (f x):1 is unifiable with x:2.

Author:

    Leonardo de Moura (leonardo) 2008-01-28.

Revision History:

--*/
#ifndef EXPR_OFFSET_H_
#define EXPR_OFFSET_H_

#include "ast/ast.h"

class expr_offset {
    expr *    m_expr;
    unsigned  m_offset;
public:
    expr_offset():m_expr(nullptr), m_offset(0) {}
    expr_offset(expr * e, unsigned o):m_expr(e), m_offset(o) {}
    
    expr * get_expr() const { return m_expr; }
    unsigned get_offset() const { return m_offset; }
    bool operator==(expr_offset const & other) const { return m_expr == other.m_expr && m_offset == other.m_offset; }
    bool operator!=(expr_offset const & other) const { return !operator==(other); }

    unsigned hash() const {
        unsigned a = m_expr->get_id();
        unsigned b = m_offset;
        unsigned c = 17;
        mix(a, b, c);
        return c;
    }
};

typedef std::pair<expr_offset, expr_offset> expr_offset_pair;
typedef pair_hash<obj_hash<expr_offset>, obj_hash<expr_offset> > expr_offset_pair_hash;

#endif /* EXPR_OFFSET_H_ */
