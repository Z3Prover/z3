 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  mk_extract_proc.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef MK_EXTRACT_PROC_H_
#define MK_EXTRACT_PROC_H_
#include "ast/ast.h"
#include "ast/bv_decl_plugin.h"
class mk_extract_proc {
    bv_util &     m_util;
    unsigned      m_high;
    unsigned      m_low;
    sort *        m_domain;
    func_decl *   m_f_cached;
public:
    mk_extract_proc(bv_util & u);
    ~mk_extract_proc();
    app * operator()(unsigned high, unsigned low, expr * arg);
    ast_manager & m() { return m_util.get_manager(); }
    bv_util & bvutil() { return m_util; }
};
#endif /* MK_EXTRACT_PROC_H_ */
