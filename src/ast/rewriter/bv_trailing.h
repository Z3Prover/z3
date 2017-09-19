 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_trailing.h

 Abstract:

 A utility to count trailing zeros of an expression.  Treats 2x and x++0 equivalently.


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef BV_TRAILING_H_
#define BV_TRAILING_H_
#include "ast/ast.h"
#include "ast/rewriter/rewriter_types.h"
#include "ast/rewriter/mk_extract_proc.h"
class bv_trailing {
    public:
        bv_trailing(mk_extract_proc& ep);
        virtual ~bv_trailing();
    public:
        // Remove trailing zeros from both sides of an equality (might give False).
        br_status eq_remove_trailing(expr * e1, expr * e2,  expr_ref& result);

        // Gives a lower and upper bound on trailing zeros in e.
        void count_trailing(expr * e, unsigned& min, unsigned& max);

        // Attempts removing n trailing zeros from e. Returns how many were successfully removed.
        // We're assuming that it can remove at least as many zeros as min returned by count_training.
        // Removing the bit-width of e, sets result to NULL.
        unsigned remove_trailing(expr * e, unsigned n, expr_ref& result);

        // Reset cache(s) if it exceeded size condition.
        void reset_cache(unsigned condition);
    protected:
        struct imp;
        imp *        m_imp;
};
#endif /* BV_TRAILING_H_ */
