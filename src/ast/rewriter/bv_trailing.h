 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_trailing.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef BV_TRAILING_H_
#define BV_TRAILING_H_
#include"ast.h"
#include"bv_rewriter.h"
#include"rewriter_types.h"
class bv_trailing {
    public:
        bv_trailing(ast_manager&m, mk_extract_proc& ep);
        virtual ~bv_trailing();
        void count_trailing(expr * e, unsigned& min, unsigned& max, unsigned depth);
        br_status eq_remove_trailing(expr * e1, expr * e2,  expr_ref& result);
        unsigned remove_trailing(expr * e, unsigned n, expr_ref& result, unsigned depth);
    protected:
        struct imp;
        imp *        m_imp;
};
#endif /* BV_TRAILING_H_ */
