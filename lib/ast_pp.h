/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_pp.h

Abstract:

    Pretty printer

Author:

    Leonardo de Moura 2008-01-20.

Revision History:

--*/
#ifndef _AST_PP_H_
#define _AST_PP_H_

#include"ast.h"
#include"pp_params.h"

std::ostream & ast_pp(std::ostream & strm, ast * n, ast_manager & m, pp_params const & p, unsigned indent = 0, 
                      unsigned num_vars = 0, char const * const * names = 0);
std::ostream & ast_pp(std::ostream & strm, ast * n, ast_manager & m);

std::string & ast_pp(std::string & s, ast * n, ast_manager & m, pp_params const & p, unsigned indent = 0);
std::string ast_pp(ast * n, ast_manager & m, pp_params const & p, unsigned indent = 0);
std::string & ast_pp(std::string & s, ast * n, ast_manager & m);
std::string ast_pp(ast * n, ast_manager & m);

struct mk_pp {
    ast *             m_ast;
    ast_manager &     m_manager;
    pp_params const & m_params;
    unsigned          m_indent;
    unsigned          m_num_var_names;
    char const * const * m_var_names;
    mk_pp(ast * a, ast_manager & m, pp_params const & p, unsigned indent = 0, unsigned num_var_names = 0, char const * const * var_names = 0);
    mk_pp(ast * a, ast_manager & m, unsigned indent = 0, unsigned num_var_names = 0, char const * const * var_names = 0);
};

inline std::ostream& operator<<(std::ostream& out, const mk_pp & p) {
    return ast_pp(out, p.m_ast, p.m_manager, p.m_params, p.m_indent, p.m_num_var_names, p.m_var_names);
}

inline std::string& operator+=(std::string& out, const mk_pp & p) {
    return ast_pp(out, p.m_ast, p.m_manager, p.m_params, p.m_indent);
}

#endif
