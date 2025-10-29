/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    format.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-20.

Revision History:

--*/
#pragma once
#include <string>

#include "ast/ast.h"

namespace format_ns {
    typedef app format;

    typedef app_ref format_ref;
    
    enum format_sort_kind {
        FORMAT_SORT
    };
    
    enum format_op_kind {
        OP_NIL,
        OP_STRING,
        OP_INDENT,
        OP_COMPOSE,
        OP_CHOICE,
        OP_LINE_BREAK,
        OP_LINE_BREAK_EXT
    };
    
    struct f2f {
        format * operator()(format * f) { return f; }
    };

    /**
       \brief Return the "format manager" associated with the given ast_manager.
    */
    inline ast_manager & fm(ast_manager & m) {
        return m.get_format_manager();
    }

    family_id get_format_family_id(ast_manager & m);

    format * mk_string(ast_manager & m, char const * str);
    static inline format * mk_string(ast_manager & m, const std::string & str) { return mk_string(m, str.c_str()); }
    format * mk_int(ast_manager & m, int i);
    format * mk_unsigned(ast_manager & m, unsigned u);
    format * mk_indent(ast_manager & m, unsigned i, format * f);
    format * mk_line_break(ast_manager & m);
    format * mk_group(ast_manager & m, format * f);
    format * mk_compose(ast_manager & m, unsigned num_children, format * const * children);
    format * mk_compose(ast_manager & m, format * f1, format * f2);
    format * mk_compose(ast_manager & m, format * f1, format * f2, format * f3);
    format * mk_compose(ast_manager & m, format * f1, format * f2, format * f3, format * f4);
    format * mk_nil(ast_manager & m);
    format * mk_choice(ast_manager & m, format * f1, format * f2);

    template<typename It, typename ToDoc>
    format * mk_seq(ast_manager & m, It const & begin, It const & end, ToDoc proc) {
        app_ref_buffer children(fm(m));
        for (It it = begin; it != end; ++it) {
            format * curr = proc(*it);
            if (curr->get_decl_kind() != OP_NIL) {
                children.push_back(mk_line_break(m));
                children.push_back(curr);
            }
        }
        return mk_compose(m, children.size(), children.data());
    }

    /**
       (header elem_1
               elem_2
               ...
               elem_n)
    */
    template<typename It, typename ToDoc>
        format * mk_seq1(ast_manager & m, It const & begin, It const & end, ToDoc proc, char const * header, 
                     char const * lp = "(", char const * rp = ")") {
        if (begin == end)
            {
                format * lp_fmt = mk_string(m, lp);
                format * header_fmt = mk_string(m, header);
                format * rp_fmt = mk_string(m, rp);
                return mk_compose(m, lp_fmt, header_fmt, rp_fmt);
            }
        unsigned indent = static_cast<unsigned>(strlen(lp) + strlen(header) + 1);
        It it = begin;
        format * first  = proc(*it);
        ++it;
        format * lp_fmt = mk_string(m, lp);
        format * header_fmt = mk_string(m, header);
        format * space_fmt = mk_string(m, " ");
        format * seq_fmt = mk_seq(m, it, end, proc);
        format * rp_fmt = mk_string(m, rp);
        format * tail_comp = mk_compose(m, space_fmt, first, seq_fmt, rp_fmt);
        format * indented = mk_indent(m, indent, tail_comp);
        format * composed = mk_compose(m, lp_fmt, header_fmt, indented);
        return mk_group(m, composed);
    }

    template<typename It, typename ToDoc>
    static inline format * mk_seq1(ast_manager & m, It const & begin, It const & end, ToDoc proc, const std::string &header,
                     char const * lp = "(", char const * rp = ")") {
        return mk_seq1(m, begin, end, proc, header.c_str(), lp, rp);
    }

#define FORMAT_DEFAULT_INDENT 2

    /**
       (header
          elem_1
          ...
          elem_n)
    */
    template<typename It, typename ToDoc>
    format * mk_seq2(ast_manager & m, It const & begin, It const & end, ToDoc proc, char const * header, 
                     unsigned indent = FORMAT_DEFAULT_INDENT, char const * lp = "(", char const * rp = ")") {
        
        if (begin == end)
            return mk_compose(m, mk_string(m, lp), mk_string(m, header), mk_string(m, rp));
        return mk_group(m, mk_compose(m,
                                      mk_indent(m, static_cast<unsigned>(strlen(lp)),
                                                mk_compose(m, mk_string(m, lp), mk_string(m, header))),
                                      mk_indent(m, indent,
                                                mk_compose(m, mk_seq(m, begin, end, proc), mk_string(m, rp)))));
    }

    /**
       (header elem_1
               ...
               elem_i
          elem_{i+1}
          ...
          elem_n)
    */
    template<typename It, typename ToDoc>
    format * mk_seq3(ast_manager & m, It const & begin, It const & end, ToDoc proc, char const * header, unsigned i = 1,
                     unsigned indent = FORMAT_DEFAULT_INDENT, char const * lp = "(", char const * rp = ")") {
        SASSERT(i >= 1);
        if (begin == end)
            {
                format * lp_fmt = mk_string(m, lp);
                format * header_fmt = mk_string(m, header);
                format * rp_fmt = mk_string(m, rp);
                return mk_compose(m, lp_fmt, header_fmt, rp_fmt);
            }
        unsigned idx = 0;
        It end1 = begin;
        for (;end1 != end && idx < i; ++end1, ++idx)
            ;
        It it = begin;
        format * first = proc(*it);
        ++it;
        unsigned header_indent = static_cast<unsigned>(strlen(header) + strlen(lp) + 1);
        format * lp_fmt = mk_string(m, lp);
        format * header_fmt = mk_string(m, header);
        format * header_compose = mk_compose(m, lp_fmt, header_fmt);
        format * space_fmt = mk_string(m, " ");
        format * prefix_seq = mk_seq(m, it, end1, proc);
        format * prefix_comp = mk_compose(m, space_fmt, first, prefix_seq);
        format * indent_prefix = mk_group(m, mk_indent(m, header_indent, prefix_comp));
        format * suffix_seq = mk_seq(m, end1, end, proc);
        format * suffix_indent = mk_indent(m, indent, suffix_seq);
        format * rp_fmt = mk_string(m, rp);
        format * composed = mk_compose(m, header_compose, indent_prefix, suffix_indent, rp_fmt);
        return mk_group(m, composed);
    }

    /**
       (elem_1
          elem_2
          ...
          elem_n)
    */
    template<typename It, typename ToDoc>
    format * mk_seq4(ast_manager & m, It const & begin, It const & end, ToDoc proc, unsigned indent = FORMAT_DEFAULT_INDENT, 
                     char const * lp = "(", char const * rp = ")") {
        if (begin == end)
            {
                format * lp_fmt = mk_string(m, lp);
                format * rp_fmt = mk_string(m, rp);
                return mk_compose(m, lp_fmt, rp_fmt);
            }
        unsigned indent1 = static_cast<unsigned>(strlen(lp));
        It it = begin;
        format * first = proc(*it);
        ++it;
        format * lp_fmt = mk_string(m, lp);
        format * first_comp = mk_compose(m, lp_fmt, first);
        format * first_indent = mk_indent(m, indent1, first_comp);
        format * seq_rest = mk_seq(m, it, end, proc);
        format * rp_fmt = mk_string(m, rp);
        format * tail_comp = mk_compose(m, seq_rest, rp_fmt);
        format * tail_indent = mk_indent(m, indent, tail_comp);
        return mk_group(m, mk_compose(m, first_indent, tail_indent));
    }

    /**
       (elem_1
        elem_2
        ...
        elem_n)
    */
    template<typename It, typename ToDoc>
    format * mk_seq5(ast_manager & m, It const & begin, It const & end, ToDoc proc, 
                     char const * lp = "(", char const * rp = ")") {
        return mk_seq4(m, begin, end, proc, static_cast<unsigned>(strlen(lp)), lp, rp);
    }
  
};
