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
#include "util/obj_hashtable.h"

class ast_pp_util {
    ast_manager&        m;
    obj_hashtable<func_decl> m_removed;
 public:        

    decl_collector      coll;

    ast_pp_util(ast_manager& m): m(m), coll(m, false) {}

    void collect(expr* e);

    void collect(unsigned n, expr* const* es);

    void collect(expr_ref_vector const& es);

    void remove_decl(func_decl* f);

    void display_decls(std::ostream& out);

    void display_asserts(std::ostream& out, expr_ref_vector const& fmls, bool neat = true);
};

#endif /* AST_PP_UTIL_H_ */
