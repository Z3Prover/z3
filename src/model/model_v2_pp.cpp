/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_v2_pp.cpp

Abstract:

    V2 Pretty printer for models. (backward compatibility)

Author:

    Leonardo de Moura (leonardo)

Revision History:
--*/
#include "model/model_v2_pp.h"
#include "model/model_core.h"
#include "ast/ast_pp.h"

static void display_function(std::ostream & out, model_core const & md, func_decl * f, bool partial) {
    ast_manager & m = md.get_manager();
    func_interp * g = md.get_func_interp(f);
    out << f->get_name() << " -> {\n";
    unsigned num_entries = g->num_entries();
    unsigned arity       = g->get_arity();
    char const * else_str = num_entries == 0 ? "  " : "  else -> ";
    unsigned else_indent  = static_cast<unsigned>(strlen(else_str));
    for (unsigned i = 0; i < num_entries; i++) {
        func_entry const * entry = g->get_entry(i);
        out << "  ";
        for (unsigned j = 0; j < arity; j++) {
            expr * arg = entry->get_arg(j);
            out << mk_pp(arg, m);
            out << " ";
        }
        out << "-> "; 
        out << mk_pp(entry->get_result(), m);
        out << "\n";
    }
    if (partial) {
        out << else_str << "#unspecified\n";
    }
    else {
        expr * else_val = g->get_else();
        out << else_str;
        if (else_val)
            out << mk_pp(else_val, m, else_indent);
        else
            out << "#unspecified";
        out << "\n";
    }
    out << "}\n";
}

static void display_functions(std::ostream & out, model_core const & md, bool partial) {
    unsigned sz = md.get_num_functions();
    for (unsigned i = 0; i < sz; i++) {
        func_decl * f = md.get_function(i);
        display_function(out, md, f, partial);
    }
}

static void display_constants(std::ostream & out, model_core const & md) {
    ast_manager & m = md.get_manager();
    unsigned sz = md.get_num_constants();
    for (unsigned i = 0; i < sz; i++) {
        func_decl * d = md.get_constant(i);

        std::string name   = d->get_name().str();
        const char * arrow = " -> "; 
        out << name << arrow;
        unsigned indent = static_cast<unsigned>(name.length() + strlen(arrow));
        out << mk_pp(md.get_const_interp(d), m, indent) << "\n";
    }
}

void model_v2_pp(std::ostream & out, model_core const & md, bool partial) {
    display_constants(out, md);
    display_functions(out, md, partial);
}

// debugging support
void pp(model_core const & md) {
    model_v2_pp(std::cout, md, false);
}
