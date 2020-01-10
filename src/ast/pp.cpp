/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pp.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-20.

Revision History:

--*/
#include "ast/pp.h"
#include "ast/pp_params.hpp"
using namespace format_ns;

static std::pair<unsigned, bool> space_upto_line_break(ast_manager & m, format * f) {
    unsigned r;
    SASSERT(f->get_family_id() == fm(m).get_family_id("format"));
    decl_kind k = f->get_decl_kind();
    switch(k) {
    case OP_STRING: {
        unsigned len = f->get_decl()->get_parameter(0).get_symbol().display_size();
        return std::make_pair(len, false);
    }
    case OP_CHOICE:
        return space_upto_line_break(m, to_app(f->get_arg(0)));
    case OP_COMPOSE: 
        r = 0;
        for (unsigned i = 0; i < f->get_num_args(); i++) {
            std::pair<unsigned, bool> pair = space_upto_line_break(m, to_app(f->get_arg(i)));
            r += pair.first;
            if (pair.second)
                return std::make_pair(r, true); 
        }
        return std::make_pair(r, false);
    case OP_INDENT:
        return space_upto_line_break(m, to_app(f->get_arg(0)));
    case OP_LINE_BREAK:
    case OP_LINE_BREAK_EXT:
        return std::make_pair(0, true);
    default:
        return std::make_pair(0, false);
    }
}

inline bool fits(ast_manager & m, format * f, unsigned space_left) {
    unsigned s = space_upto_line_break(m, f).first;
    TRACE("fits", tout << "s: " << s << " space_left " << space_left << "\n";);
    return s <= space_left;
}

void pp(std::ostream & out, format * f, ast_manager & m, params_ref const & _p) {
    pp_params p(_p);
    unsigned max_width     = p.max_width();
    unsigned max_ribbon    = p.max_ribbon(); 
    unsigned max_num_lines = p.max_num_lines();
    unsigned max_indent    = p.max_indent();
    bool     bounded       = p.bounded();
    bool     single_line   = p.single_line();

    unsigned pos = 0;
    unsigned ribbon_pos = 0;
    unsigned line = 0;
    unsigned len;
    unsigned i;
    int space_left;
    svector<std::pair<format *, unsigned> > todo;
    todo.push_back(std::make_pair(f, 0));
    app_ref  space(mk_string(m, " "), fm(m));
    while (!todo.empty()) {
        if (line >= max_num_lines)
            return;
        std::pair<format *, unsigned> pair = todo.back();
        format * f = pair.first;
        unsigned indent    = pair.second;
        todo.pop_back();
        SASSERT(f->get_family_id() == fm(m).get_family_id("format"));
        switch (f->get_decl_kind()) {
        case OP_STRING:
            if (bounded && pos > max_width)
                break;
            len = static_cast<unsigned>(strlen(f->get_decl()->get_parameter(0).get_symbol().bare_str()));
            if (bounded && pos + len > max_width) {
                out << "...";
                break;
            }
            pos += len;
            ribbon_pos += len;
            out << f->get_decl()->get_parameter(0).get_symbol();
            break;
        case OP_INDENT:
            todo.push_back(std::make_pair(to_app(f->get_arg(0)), 
                                          std::min(indent + f->get_decl()->get_parameter(0).get_int(),
                                                   max_indent)));
            break;
        case OP_COMPOSE:
            i = f->get_num_args();
            while (i > 0) {
                --i;
                todo.push_back(std::make_pair(to_app(f->get_arg(i)), indent));
            }
            break;
        case OP_CHOICE:
            space_left = std::min(max_width - pos, max_ribbon - pos);
            if (space_left > 0 && fits(m, to_app(f->get_arg(0)), space_left)) 
                todo.push_back(std::make_pair(to_app(f->get_arg(0)), indent));
            else
                todo.push_back(std::make_pair(to_app(f->get_arg(1)), indent));
            break;
        case OP_LINE_BREAK:
        case OP_LINE_BREAK_EXT:
            if (single_line) {
                todo.push_back(std::make_pair(space, indent));
                break;
            }
            pos = indent;
            ribbon_pos = 0;
            line++;
            if (line < max_num_lines) {
                out << "\n";
                for (unsigned i = 0; i < indent; i++) 
                    out << " ";
            }
            else
                out << "...\n";
            break;
        default:
            break;
        }
    }
}

