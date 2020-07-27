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
#pragma once

#include "util/top_sort.h"
#include "ast/ast.h"
#include "ast/datatype_decl_plugin.h"

class decl_collector {
    ast_manager &         m_manager;
    ptr_vector<sort>      m_sorts;
    ptr_vector<func_decl> m_decls;
    ast_mark              m_visited;
    ast_ref_vector        m_trail;
    unsigned_vector       m_trail_lim;
    unsigned_vector       m_sorts_lim;
    unsigned_vector       m_decls_lim;
    family_id             m_basic_fid;
    family_id             m_dt_fid;
    datatype_util         m_dt_util;
    ptr_vector<ast>       m_todo;

    void visit_sort(sort* n);
    bool is_bool(sort* s);

    typedef obj_hashtable<sort> sort_set;
    sort_set* collect_deps(sort* s);
    void collect_deps(top_sort<sort>& st);
    void collect_deps(sort* s, sort_set& set);


public:
    decl_collector(ast_manager & m);
    ast_manager & m() { return m_manager; }

    void reset() { m_sorts.reset(); m_decls.reset(); m_visited.reset(); m_trail.reset(); }
    void visit_func(func_decl* n);
    void visit(ast * n);
    void visit(unsigned n, expr* const* es);
    void visit(expr_ref_vector const& es);

    void push();
    void pop(unsigned n);

    void order_deps(unsigned n);

    unsigned get_num_sorts() const { return m_sorts.size(); }
    unsigned get_num_decls() const { return m_decls.size(); }
    
    ptr_vector<sort> const& get_sorts() const { return m_sorts; }
    ptr_vector<func_decl> const& get_func_decls() const { return m_decls; }
};

