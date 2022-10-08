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
#pragma once

#include "ast/decl_collector.h"
#include "ast/ast_smt2_pp.h"
#include "util/obj_hashtable.h"
#include "util/stacked_value.h"

class ast_pp_util {
    ast_manager&        m;
    obj_hashtable<func_decl> m_removed;
    smt2_pp_environment_dbg m_env;
    stacked_value<unsigned> m_rec_decls;
    stacked_value<unsigned> m_decls;
    stacked_value<unsigned> m_sorts;
    expr_mark               m_is_defined;
    expr_ref_vector         m_defined;
    unsigned_vector         m_defined_lim;

 public:

    decl_collector      coll;
    
    ast_pp_util(ast_manager& m): m(m), m_env(m), m_rec_decls(0), m_decls(0), m_sorts(0), m_defined(m), coll(m) {}

    void reset();

    void collect(expr* e);

    void collect(unsigned n, expr* const* es);

    void collect(expr_ref_vector const& es);

    void remove_decl(func_decl* f);

    void display_decls(std::ostream& out);

    void display_skolem_decls(std::ostream& out);

    void display_asserts(std::ostream& out, expr_ref_vector const& fmls, bool neat = true);

    void display_assert(std::ostream& out, expr* f, bool neat = true);

    void display_assert_and_track(std::ostream& out, expr* f, expr* t, bool neat = true);

    std::ostream& display_expr(std::ostream& out, expr* f, bool neat = true);

    std::ostream& define_expr(std::ostream& out, expr* f);

    std::ostream& display_expr_def(std::ostream& out, expr* f);

    void push();

    void pop(unsigned n);

    smt2_pp_environment& env() { return m_env; }
};

