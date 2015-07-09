/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    decl_collector.h

Abstract:

    Collect uninterpreted func_delcs and sorts.
    This class was originally in ast_smt_pp.h

Author:

    Leonardo (leonardo) 2011-10-04

Revision History:

--*/
#ifndef SMT_DECL_COLLECTOR_H_
#define SMT_DECL_COLLECTOR_H_

#include"ast.h"

class decl_collector {
    ast_manager &         m_manager;
    bool                  m_sep_preds;
    ptr_vector<sort>      m_sorts;
    ptr_vector<func_decl> m_decls;
    ptr_vector<func_decl> m_preds;
    ast_mark m_visited;
    family_id m_basic_fid;
    family_id m_dt_fid;

    void visit_sort(sort* n);
    bool is_bool(sort* s);
    void visit_func(func_decl* n);


public:
    // if preds == true, then predicates are stored in a separate collection.
    decl_collector(ast_manager & m, bool preds=true);
    ast_manager & m() { return m_manager; }

    void visit(ast * n);

    unsigned get_num_sorts() const { return m_sorts.size(); }
    unsigned get_num_decls() const { return m_decls.size(); }
    unsigned get_num_preds() const { return m_preds.size(); }
    sort * const * get_sorts() const { return m_sorts.c_ptr(); }
    func_decl * const * get_func_decls() const { return m_decls.c_ptr(); }
    func_decl * const * get_pred_decls() const { return m_preds.c_ptr(); }
};

#endif
