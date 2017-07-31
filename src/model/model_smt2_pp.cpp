/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_smt2_pp.cpp

Abstract:

    Pretty printer for models using SMT2 format.

Author:

    Leonardo de Moura (leonardo)

Revision History:


--*/
#include<sstream>
#include "model/model_smt2_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/func_decl_dependencies.h"
#include "ast/pp.h"
using namespace format_ns;

static void pp_indent(std::ostream & out, unsigned indent) {
    for (unsigned i = 0; i < indent; i++) 
        out << " ";
}

static unsigned pp_symbol(std::ostream & out, symbol const & s) {
    if (is_smt2_quoted_symbol(s)) {
        std::string str = mk_smt2_quoted_symbol(s);
        out << str;
        return static_cast<unsigned>(str.length());
    }
    else if (s.is_numerical()) {
        std::string str = s.str();
        out << str;
        return static_cast<unsigned>(str.length());
    }
    else {
        out << s.bare_str();
        return static_cast<unsigned>(strlen(s.bare_str()));
    }
}

#define TAB_SZ 2

static void pp_uninterp_sorts(std::ostream & out, ast_printer_context & ctx, model_core const & md, unsigned indent) {
    ast_manager & m = ctx.get_ast_manager();
    ptr_buffer<format> f_conds;
    unsigned num = md.get_num_uninterpreted_sorts();
    for (unsigned i = 0; i < num; i++) {
        sort * s = md.get_uninterpreted_sort(i);
        ptr_vector<expr> const & u = md.get_universe(s);
        std::ostringstream buffer;
        buffer << "universe for ";
        ctx.display(buffer, s, 13);
        buffer << ":\n";
        pp_indent(buffer, TAB_SZ);
        ptr_vector<expr>::const_iterator it  = u.begin();
        ptr_vector<expr>::const_iterator end = u.end();
        for (; it != end; ++it) {
            SASSERT(is_app(*it));
            app * c = to_app(*it);
            pp_symbol(buffer, c->get_decl()->get_name());
            buffer << " ";
        }
        buffer << "\n-----------";
        std::string buffer_str = buffer.str();
        unsigned len = static_cast<unsigned>(buffer_str.length());
        pp_indent(out, indent);
        out << ";; ";
        for (unsigned i = 0; i < len; i++) {
            char c = buffer_str[i];
            if (c == '\n') {
                out << "\n";
                pp_indent(out, indent);
                out << ";; ";
            }
            else {
                out << c;
            }
        }
        out << "\n";
        pp_indent(out, indent);
        out << ";; definitions for universe elements:\n";
        it  = u.begin();
        for (; it != end; ++it) {
            app * c = to_app(*it);
            pp_indent(out, indent);
            out << "(declare-fun ";
            unsigned len  = pp_symbol(out, c->get_decl()->get_name());
            out << " () ";
            ctx.display(out, c->get_decl()->get_range(), indent + len + 16);
            out << ")\n";
        }
        pp_indent(out, indent);
        out << ";; cardinality constraint:\n";
        f_conds.reset();
        format * var = mk_string(m, "x");
        it  = u.begin();
        for (; it != end; ++it) {
            app * c = to_app(*it);
            symbol csym = c->get_decl()->get_name();
            std::string cname;
            if (is_smt2_quoted_symbol(csym))
                cname = mk_smt2_quoted_symbol(csym);
            else
                cname = csym.str();
            format * c_args[2] = { var, mk_string(m, cname.c_str()) };
            f_conds.push_back(mk_seq1<format**, f2f>(m, c_args, c_args+2, f2f(), "="));
        }
        SASSERT(!f_conds.empty());
        format * f_cond;
        if (f_conds.size() > 1)
            f_cond = mk_seq1(m, f_conds.begin(), f_conds.end(), f2f(), "or");
        else
            f_cond = f_conds[0];
        format_ref f_s(fm(m));
        ctx.pp(s, f_s);
        format * f_args[2] = { mk_compose(m, 
                                          mk_string(m, "((x "),
                                          mk_indent(m, 4, mk_compose(m, f_s.get(), mk_string(m, "))")))),
                               f_cond };
        format_ref f_card(fm(m));
        f_card = mk_indent(m, indent, mk_seq1<format**, f2f>(m, f_args, f_args+2, f2f(), "forall"));
        pp_indent(out, indent);
        pp(out, f_card, m);
        out << "\n";
        pp_indent(out, indent);
        out << ";; -----------\n";
    }
}

static void pp_consts(std::ostream & out, ast_printer_context & ctx, model_core const & md, unsigned indent) {
    unsigned num = md.get_num_constants();
    for (unsigned i = 0; i < num; i++) {
        func_decl * c = md.get_constant(i);
        expr * c_i    = md.get_const_interp(c);
        pp_indent(out, indent);
        out << "(define-fun ";
        unsigned len  = pp_symbol(out, c->get_name());
        out << " () ";
        ctx.display(out, c->get_range(), indent + len + 16);
        out << "\n";
        pp_indent(out, indent + TAB_SZ);
        ctx.display(out, c_i);
        out << ")\n";
    }
}

void sort_fun_decls(ast_manager & m, model_core const & md, ptr_buffer<func_decl> & result) {
    func_decl_set         visited;
    ptr_vector<func_decl> todo;
    unsigned sz = md.get_num_functions();
    for (unsigned i = 0; i < sz; i++) {
        func_decl * f = md.get_function(i);
        if (visited.contains(f))
            continue;
        visited.insert(f);
        todo.push_back(f);
        while (!todo.empty()) {
            func_decl * curr = todo.back();
            func_interp * curr_i = md.get_func_interp(curr);
            SASSERT(curr_i != 0);
            if (!curr_i->is_partial()) {
                func_decl_set deps;
                bool all_visited = true;
                collect_func_decls(m, curr_i->get_else(), deps);
                func_decl_set::iterator it2  = deps.begin();
                func_decl_set::iterator end2 = deps.end();
                for (; it2 != end2; ++it2) {
                    func_decl * d = *it2;
                    if (d->get_arity() > 0 && md.has_interpretation(d) && !visited.contains(d)) {
                        todo.push_back(d);
                        visited.insert(d);
                        all_visited = false;
                    }
                }
                if (!all_visited)
                    continue;
            }
            todo.pop_back();
            result.push_back(curr);
        }
    }
}

static void pp_funs(std::ostream & out, ast_printer_context & ctx, model_core const & md, unsigned indent) {
    ast_manager & m = ctx.get_ast_manager();
    sbuffer<symbol>    var_names;
    ptr_buffer<format> f_var_names;
    ptr_buffer<format> f_arg_decls;
    ptr_buffer<format> f_entries;
    ptr_buffer<format> f_entry_conds;
    ptr_buffer<func_decl> func_decls;
    sort_fun_decls(m, md, func_decls);
    for (unsigned i = 0; i < func_decls.size(); i++) {
        func_decl * f     = func_decls[i]; 
        func_interp * f_i = md.get_func_interp(f);
        SASSERT(f->get_arity() == f_i->get_arity());
        format_ref body(fm(m));
        var_names.reset();
        if (f_i->is_partial()) {
            body = mk_string(m, "#unspecified");
            for (unsigned j = 0; j < f->get_arity(); j++) {
                std::stringstream strm;
                strm << "x!" << (j+1);
                var_names.push_back(symbol(strm.str().c_str()));
            }
        }
        else {
            ctx.pp(f_i->get_else(), f->get_arity(), "x", body, var_names);  
        }
        TRACE("model_smt2_pp", for (unsigned i = 0; i < var_names.size(); i++) tout << var_names[i] << "\n";);
        f_var_names.reset();
        for (unsigned i = 0; i < f->get_arity(); i++)
            f_var_names.push_back(mk_string(m, var_names[i].bare_str()));
        f_arg_decls.reset();
        for (unsigned i = 0; i < f->get_arity(); i++) {
            format_ref f_domain(fm(m));
            ctx.pp(f->get_domain(i), f_domain);
            format * args[2] = { f_var_names[i], f_domain.get() };
            f_arg_decls.push_back(mk_seq5<format**, f2f>(m, args, args+2, f2f()));
        }
        format * f_domain = mk_seq5(m, f_arg_decls.begin(), f_arg_decls.end(), f2f());
        format_ref f_range(fm(m));
        ctx.pp(f->get_range(), f_range);
        if (f_i->num_entries() > 0) {
            f_entries.reset();
            for (unsigned i = 0; i < f_i->num_entries(); i++) {
                func_entry const * e = f_i->get_entry(i);
                f_entry_conds.reset();
                for (unsigned j = 0; j < f->get_arity(); j++) {
                    format_ref f_arg(fm(m));
                    ctx.pp(e->get_arg(j), f_arg);
                    format * eq_args[2] = { f_var_names[j], f_arg.get() };
                    f_entry_conds.push_back(mk_seq1<format**, f2f>(m, eq_args, eq_args+2, f2f(), "="));
                }
                format * f_entry_cond;
                SASSERT(!f_entry_conds.empty());
                if (f_entry_conds.size() > 1)
                    f_entry_cond = mk_seq1(m, f_entry_conds.begin(), f_entry_conds.end(), f2f(), "and");
                else
                    f_entry_cond = f_entry_conds[0];
                format_ref f_result(fm(m));
                ctx.pp(e->get_result(), f_result);
                if (i > 0)
                    f_entries.push_back(mk_line_break(m));
                f_entries.push_back(mk_group(m, mk_compose(m, 
                                                           mk_string(m, "(ite "),
                                                           mk_indent(m, 5, f_entry_cond),
                                                           mk_indent(m, TAB_SZ, mk_compose(m, 
                                                                                           mk_line_break(m),
                                                                                           f_result.get())))));
            }
            f_entries.push_back(mk_indent(m, TAB_SZ, mk_compose(m,
                                                                mk_line_break(m),
                                                                body.get())));
            for (unsigned i = 0; i < f_i->num_entries(); i++)
                f_entries.push_back(mk_string(m, ")"));
            body = mk_compose(m, f_entries.size(), f_entries.c_ptr());
        }
        format_ref def(fm(m));
        std::string fname;
        if (is_smt2_quoted_symbol(f->get_name()))
            fname = mk_smt2_quoted_symbol(f->get_name());
        else
            fname = f->get_name().str();
        def = mk_indent(m, indent, mk_compose(m, 
                                              mk_compose(m, 
                                                         mk_string(m, "(define-fun "),
                                                         mk_string(m, fname.c_str()),
                                                         mk_string(m, " "),
                                                         mk_compose(m, 
                                                                    f_domain,
                                                                    mk_string(m, " "),
                                                                    f_range)),
                                              mk_indent(m, TAB_SZ, mk_compose(m, 
                                                                              mk_line_break(m),
                                                                              body.get(),
                                                                              mk_string(m, ")")))));
        pp_indent(out, indent);
        pp(out, def.get(), m);
        out << "\n";
    }
}

void model_smt2_pp(std::ostream & out, ast_printer_context & ctx, model_core const & m, unsigned indent) {
    pp_uninterp_sorts(out, ctx, m, indent);
    pp_consts(out, ctx, m, indent);
    pp_funs(out, ctx, m, indent);
}

void model_smt2_pp(std::ostream & out, ast_manager & m, model_core const & md, unsigned indent) {
    scoped_ptr<ast_printer_context> ctx;
    ctx = mk_simple_ast_printer_context(m);
    pp_uninterp_sorts(out, *(ctx.get()), md, indent);
    pp_consts(out, *(ctx.get()), md, indent);
    pp_funs(out, *(ctx.get()), md, indent);
}
