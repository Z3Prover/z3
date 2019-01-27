/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ast_printer.h

Abstract:

    Abstract AST printer
    
Author:

    Leonardo de Moura (leonardo) 2012-10-21

Revision History:

--*/
#ifndef AST_PRINTER_H_
#define AST_PRINTER_H_

#include "ast/ast.h"
#include "ast/ast_smt2_pp.h"

class ast_printer {
public:
    virtual ~ast_printer() {}
    virtual void pp(sort * s, format_ns::format_ref & r) const { UNREACHABLE(); }
    virtual void pp(func_decl * f, format_ns::format_ref & r) const { UNREACHABLE(); }
    virtual void pp(expr * n, unsigned num_vars, char const * var_prefix, format_ns::format_ref & r, sbuffer<symbol> & var_names) const { UNREACHABLE(); }
    virtual void pp(expr * n, format_ns::format_ref & r) const { UNREACHABLE(); }
    virtual void display(std::ostream & out, sort * s, unsigned indent = 0) const {
        out << "#" << s->get_id() << "\n";
    }
    virtual void display(std::ostream & out, expr * n, unsigned indent, unsigned num_vars, char const * var_prefix, sbuffer<symbol> & var_names) const {
        out << "#" << n->get_id() << "\n";
    }
    virtual void display(std::ostream & out, expr * n, unsigned indent = 0) const {
        out << "#" << n->get_id() << "\n";
    }
    virtual void display(std::ostream & out, func_decl * f, unsigned indent = 0) const {
        out << "#" << f->get_id() << "\n";
    }
};

class ast_printer_context : public ast_printer {
public:
    ~ast_printer_context() override {}
    virtual ast_manager & get_ast_manager() = 0;
    virtual std::ostream & regular_stream() { return std::cout; }
    virtual std::ostream & diagnostic_stream() { return std::cerr; }
};


ast_printer_context * mk_simple_ast_printer_context(ast_manager & m);

#endif
