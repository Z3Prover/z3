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
 public:        

    decl_collector      coll;

    ast_pp_util(ast_manager& m): m(m), m_env(m), coll(m, false) {}

    void collect(expr* e);

    void collect(unsigned n, expr* const* es);

    void collect(expr_ref_vector const& es);

    void remove_decl(func_decl* f);

    void display_decls(std::ostream& out);

    void display_asserts(std::ostream& out, expr_ref_vector const& fmls, bool neat = true);

    smt2_pp_environment& env() { return m_env; }
};

#endif /* AST_PP_UTIL_H_ */
