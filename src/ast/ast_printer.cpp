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
#include "ast/ast_printer.h"
#include "ast/pp.h"

class simple_ast_printer_context : public ast_printer_context {
    ast_manager & m_manager;
    scoped_ptr<smt2_pp_environment_dbg> m_env;
    smt2_pp_environment_dbg & env() const { return *(m_env.get()); }
public:
    simple_ast_printer_context(ast_manager & m):m_manager(m) { m_env = alloc(smt2_pp_environment_dbg, m); }
    ~simple_ast_printer_context() override {}
    ast_manager & m() const { return m_manager; }
    ast_manager & get_ast_manager() override { return m_manager; }
    void display(std::ostream & out, sort * s, unsigned indent = 0) const override { out << mk_ismt2_pp(s, m(), indent); }
    void display(std::ostream & out, expr * n, unsigned indent = 0) const override { out << mk_ismt2_pp(n, m(), indent); }
    void display(std::ostream & out, func_decl * f, unsigned indent = 0) const override {
        out << f->get_name();
    }
    void pp(sort * s, format_ns::format_ref & r) const override { mk_smt2_format(s, env(), params_ref(), r); }
    void pp(func_decl * f, format_ns::format_ref & r) const override { mk_smt2_format(f, env(), params_ref(), r, "declare-fun"); }
    void pp(expr * n, format_ns::format_ref & r) const override {
        sbuffer<symbol> buf;
        mk_smt2_format(n, env(), params_ref(), 0, nullptr, r, buf);
    }
    void pp(expr * n, unsigned num_vars, char const * var_prefix, format_ns::format_ref & r, sbuffer<symbol> & var_names) const override {
        mk_smt2_format(n, env(), params_ref(), num_vars, var_prefix, r, var_names);
    }
    void display(std::ostream & out, expr * n, unsigned indent, unsigned num_vars, char const * var_prefix, sbuffer<symbol> & var_names) const override {
        NOT_IMPLEMENTED_YET();
    }

};

ast_printer_context * mk_simple_ast_printer_context(ast_manager & m) {
    return alloc(simple_ast_printer_context, m);
}
