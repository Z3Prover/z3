/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ast_printer.cpp

Abstract:

    Abstract AST printer
    
Author:

    Leonardo de Moura (leonardo) 2012-10-21

Revision History:

--*/
#include"ast_printer.h"
#include"pp.h"

class simple_ast_printer_context : public ast_printer_context {
    ast_manager & m_manager;
    smt2_pp_environment_dbg m_env;
public:
    simple_ast_printer_context(ast_manager & m):m_manager(m), m_env(m) {}
    virtual ~simple_ast_printer_context() {}
    ast_manager & m() const { return m_manager; }
    virtual ast_manager & get_ast_manager() { return m_manager; }
    virtual void display(std::ostream & out, sort * s, unsigned indent = 0) { out << mk_ismt2_pp(s, m(), indent); }
    virtual void display(std::ostream & out, expr * n, unsigned indent = 0) { out << mk_ismt2_pp(n, m(), indent); }
    virtual void display(std::ostream & out, func_decl * f, unsigned indent = 0) const {
        out << f->get_name();
    }
    virtual void pp(sort * s, format_ns::format_ref & r) { mk_smt2_format(s, m_env, get_pp_default_params(), r); }
    virtual void pp(func_decl * f, format_ns::format_ref & r) { mk_smt2_format(f, m_env, get_pp_default_params(), r); }
    virtual void pp(expr * n, format_ns::format_ref & r) { 
        sbuffer<symbol> buf;
        mk_smt2_format(n, m_env, get_pp_default_params(), 0, 0, r, buf); 
    }
    virtual void pp(expr * n, unsigned num_vars, char const * var_prefix, format_ns::format_ref & r, sbuffer<symbol> & var_names) {
        mk_smt2_format(n, m_env, get_pp_default_params(), num_vars, var_prefix, r, var_names);
    }
    virtual void display(std::ostream & out, expr * n, unsigned indent, unsigned num_vars, char const * var_prefix, sbuffer<symbol> & var_names) const {
        NOT_IMPLEMENTED_YET();
    }

};

ast_printer_context * mk_simple_ast_printer_context(ast_manager & m) {
    return alloc(simple_ast_printer_context, m);
}
