/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    num_occurs.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-27.

Revision History:

--*/
#ifndef NUM_OCCURS_H_
#define NUM_OCCURS_H_

#include "ast/ast.h"
#include "util/obj_hashtable.h"

/**
   \brief Functor for computing the number of occurrences of each sub-expression in a expression F.
*/
class num_occurs { 
protected:
    bool m_ignore_ref_count1;
    bool m_ignore_quantifiers;
    obj_map<expr, unsigned>        m_num_occurs;

    void process(expr * t, expr_fast_mark1 & visited);
public:
    num_occurs(bool ignore_ref_count1 = false, bool ignore_quantifiers = false):
        m_ignore_ref_count1(ignore_ref_count1), 
        m_ignore_quantifiers(ignore_quantifiers) {
    }

    void reset() { m_num_occurs.reset(); }
    
    void operator()(expr * t);
    void operator()(unsigned num, expr * const * ts);

    unsigned get_num_occs(expr * n) const { 
        unsigned val;
        if (m_num_occurs.find(n, val))
            return val;
        return 0;
    }
};

#endif /* NUM_OCCURS_H_ */

