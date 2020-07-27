/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pattern_validation.cpp

Abstract:

    Code for checking whether a pattern is valid or not.

Author:

    Leonardo de Moura (leonardo) 2006-12-08.

Revision History:

--*/

#include "parsers/util/pattern_validation.h"
#include "ast/for_each_expr.h"
#include "util/warning.h"

#include "ast/ast_pp.h"

struct pattern_validation_functor {
    uint_set & m_found_vars;
    unsigned   m_num_bindings;
    unsigned   m_num_new_bindings;
    bool       m_result;
    bool       m_found_a_var;
    family_id  m_bfid;
    family_id  m_lfid;
    unsigned   m_line, m_pos;
    
    pattern_validation_functor(uint_set & found_vars, unsigned num_bindings, unsigned num_new_bindings, 
                               family_id bfid, family_id lfid, unsigned line, unsigned pos):
        m_found_vars(found_vars),
        m_num_bindings(num_bindings),
        m_num_new_bindings(num_new_bindings),
        m_result(true),
        m_found_a_var(false),
        m_bfid(bfid),
        m_lfid(lfid),
        m_line(line),
        m_pos(pos) {
    }

    bool is_forbidden(func_decl const * decl) {
        family_id fid = decl->get_family_id();
        if (fid == m_bfid && decl->get_decl_kind() != OP_EQ && decl->get_decl_kind() != OP_TRUE && decl->get_decl_kind() != OP_FALSE)
            return true;
        if (fid == m_lfid)
            return true;
        return false;
    }
    
    void operator()(app * n) {
        func_decl * decl = to_app(n)->get_decl();
        if (is_forbidden(decl)) {
            auto str = decl->get_name().str();
            warning_msg("(%d,%d): '%s' cannot be used in patterns.", m_line, m_pos, str.c_str());
            m_result = false;
        }
    }
    
    void operator()(var * v) {
        unsigned idx = to_var(v)->get_idx();
        if (idx >= m_num_bindings) {
            warning_msg("(%d,%d): free variables cannot be used in patterns.", m_line, m_pos);
            m_result = false;
            return;
        }
        if (idx < m_num_new_bindings) {
            m_found_a_var = true;
            m_found_vars.insert(idx);
        }
    }
    
    void operator()(quantifier * q) { m_result = false; }
};

bool pattern_validator::process(uint_set & found_vars, unsigned num_bindings, unsigned num_new_bindings, expr * n, unsigned line, unsigned pos) {
    // I'm traversing the DAG as a tree, this is not a problem since pattern are supposed to be small ASTs.
    if (n->get_kind() == AST_VAR) {
        warning_msg("(%d,%d): invalid pattern: variable.", line, pos);
        return false;
    }

    pattern_validation_functor f(found_vars, num_bindings, num_new_bindings, m_bfid, m_lfid, line, pos);
    for_each_expr(f, n);
    if (!f.m_result)
        return false;
    if (!f.m_found_a_var) {
        warning_msg("(%d,%d): pattern does not contain any variable.", line, pos);
        return false;
    }
    return true;
}

bool pattern_validator::operator()(unsigned num_bindings, unsigned num_new_bindings, expr * n, unsigned line, unsigned pos) {
    uint_set found_vars;
    if (!process(found_vars, num_bindings, num_new_bindings, n, line, pos))
        return false;
    bool r = found_vars.num_elems() == num_new_bindings;
    if (!r)
        warning_msg("(%d,%d): pattern does not contain all quantified variables.", line, pos);
    return r;
}
