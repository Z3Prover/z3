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
#ifndef FORMAT_H_
#define FORMAT_H_

#include"ast.h"

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
        return mk_compose(m, children.size(), children.c_ptr());
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
            return mk_compose(m, mk_string(m, lp), mk_string(m, header), mk_string(m, rp));
        unsigned indent = static_cast<unsigned>(strlen(lp) + strlen(header) + 1);
        It it = begin;
        format * first  = proc(*it);
        ++it;
        return mk_group(m, mk_compose(m, 
                                      mk_string(m, lp), 
                                      mk_string(m, header), 
                                      mk_indent(m, indent, 
                                                mk_compose(m, 
                                                           mk_string(m, " "),
                                                           first,
                                                           mk_seq(m, it, end, proc),
                                                           mk_string(m, rp)))));
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
            return mk_compose(m, mk_string(m, lp), mk_string(m, header), mk_string(m, rp));
        unsigned idx = 0;
        It end1 = begin;
        for (;end1 != end && idx < i; ++end1, ++idx)
            ;
        It it = begin;
        format * first = proc(*it);
        ++it;
        return mk_group(m, 
                        mk_compose(m, 
                                   mk_compose(m, mk_string(m, lp), mk_string(m, header)),
                                   mk_group(m, mk_indent(m, static_cast<unsigned>(strlen(header) + strlen(lp) + 1),
                                                         mk_compose(m, mk_string(m, " "), first, 
                                                                    mk_seq(m, it, end1, proc)))),
                                   mk_indent(m, indent, mk_seq(m, end1, end, proc)),
                                   mk_string(m, rp)));
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
            return mk_compose(m, mk_string(m, lp), mk_string(m, rp));
        unsigned indent1 = static_cast<unsigned>(strlen(lp));
        It it = begin;
        format * first = proc(*it);
        ++it;
        return mk_group(m, mk_compose(m,
                                      mk_indent(m, indent1, mk_compose(m, mk_string(m, lp), first)),
                                      mk_indent(m, indent, mk_compose(m, 
                                                                      mk_seq(m, it, end, proc), 
                                                                      mk_string(m, rp)))));
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

#endif /* FORMAT_H_ */

