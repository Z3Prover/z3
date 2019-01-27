/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_pp.cpp

Abstract:

    Pretty printer for models for debugging purposes.

Author:

    Leonardo de Moura (leonardo)

Revision History:


--*/
#include "model/model_pp.h"
#include "model/model_core.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/used_symbols.h"
#include "ast/pp.h"

static void display_uninterp_sorts(std::ostream & out, model_core const & md) {
    ast_manager & m = md.get_manager();
    unsigned sz = md.get_num_uninterpreted_sorts();
    for (unsigned i = 0; i < sz; i++) {
        sort * s = md.get_uninterpreted_sort(i);
        out << "(define-sort " << mk_pp(s, m); 
        ptr_vector<expr> const & univ  = md.get_universe(s);
        for (expr* e : univ) {
            out << " " << mk_ismt2_pp(e, m);
        }
        out << ")\n";
    }
}

static void display_constants(std::ostream & out, model_core const & md) {
    ast_manager & m = md.get_manager();
    unsigned sz = md.get_num_constants();
    for (unsigned i = 0; i < sz; i++) {
        func_decl * c = md.get_constant(i);
        char const * d = "(define ";
        std::string n  = c->get_name().str();
        unsigned indent = static_cast<unsigned>(n.length() + strlen(d) + 1);
        out << d << n << " " << mk_ismt2_pp(md.get_const_interp(c), m, indent) << ")\n";
    }
}

static void display_functions(std::ostream & out, model_core const & md) {
    ast_manager & m = md.get_manager();
    unsigned sz = md.get_num_functions();
    for (unsigned i = 0; i < sz; i++) {
        func_decl * f = md.get_function(i);
        out << "(define (" << f->get_name();
        unsigned arity = f->get_arity();
        func_interp * fi = md.get_func_interp(f);
        for (unsigned j = 0; j < arity; j++) {
            out << " " << "x!" << j;
        }
        out << ")\n";
        
        unsigned num_entries = fi->num_entries();
        for (unsigned j = 0; j < num_entries; j++) {
            func_entry const * curr = fi->get_entry(j);
            out << "  (if ";
            if (arity > 1)
                out << "(and ";
            for (unsigned j = 0; j < arity; j++) {
                out << "(= x!" << j << " " << mk_ismt2_pp(curr->get_arg(j), m) << ")";
                if (j + 1 < arity)
                    out << " ";
            }
            if (arity > 1)
                out << ")";
            out << " " << mk_ismt2_pp(curr->get_result(), m) << "\n";
        }
        if (num_entries > 0)
            out << "  ";
        if (fi->is_partial())
            out << "  #unspecified";
        else {
            out << "  " << mk_ismt2_pp(fi->get_else(), m, params_ref(), 5, arity, "x");
        }
        for (unsigned j = 0; j < num_entries; j++)
            out << ")";
        out << ")\n";
    }
}


void model_pp(std::ostream & out, model_core const & md) {
    display_uninterp_sorts(out, md);
    display_constants(out, md);
    display_functions(out, md);
}
