/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    ast_pp_util.h

Abstract:

    Utilities for printing SMT2 declarations and assertions.

Author:

    Nikolaj Bjorner (nbjorner) 2015-8-6.

Revision History:

--*/
#ifndef AST_PP_UTIL_H_
#define AST_PP_UTIL_H_

#include "ast/decl_collector.h"
#include "ast/ast_smt2_pp.h"
#include "util/obj_hashtable.h"

class ast_pp_util {
    ast_manager&        m;
    obj_hashtable<func_decl> m_removed;
    smt2_pp_environment_dbg m_env;
    unsigned                m_num_sorts, m_num_decls;
    unsigned_vector         m_num_sorts_trail, m_num_decls_trail;
    
 public:        

    decl_collector      coll;

    ast_pp_util(ast_manager& m): m(m), m_env(m), m_num_sorts(0), m_num_decls(0), coll(m) {}

    void reset() { coll.reset(); m_removed.reset(); m_num_sorts = 0; m_num_decls = 0; }


    void collect(expr* e);

    void collect(unsigned n, expr* const* es);

    void collect(expr_ref_vector const& es);

    void remove_decl(func_decl* f);

    void display_decls(std::ostream& out);

    void display_asserts(std::ostream& out, expr_ref_vector const& fmls, bool neat = true);

    void display_assert(std::ostream& out, expr* f, bool neat = true);

    void display_assert_and_track(std::ostream& out, expr* f, expr* t, bool neat = true);

    std::ostream& display_expr(std::ostream& out, expr* f, bool neat = true);

    void push();
    
    void pop(unsigned n);

    smt2_pp_environment& env() { return m_env; }
};

#endif /* AST_PP_UTIL_H_ */
