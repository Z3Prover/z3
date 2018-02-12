/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    format.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-20.

Revision History:

--*/
#include "ast/format.h"
#include "ast/recurse_expr_def.h"

namespace format_ns {

    class format_decl_plugin : public decl_plugin {
    protected:
        sort *       m_format_sort;
        symbol       m_nil;
        symbol       m_string;
        symbol       m_indent;
        symbol       m_compose;
        symbol       m_choice;
        symbol       m_line_break;
        symbol       m_line_break_ext;
        
        void set_manager(ast_manager * m, family_id id) override {
            SASSERT(m->is_format_manager());
            decl_plugin::set_manager(m, id);
            
            m_format_sort = m->mk_sort(symbol("format"), sort_info(id, FORMAT_SORT));
            m->inc_ref(m_format_sort);
        }
        
    public:
        format_decl_plugin():
            m_format_sort(nullptr),
            m_nil("nil"),
            m_string("string"),
            m_indent("indent"),
            m_compose("compose"),
            m_choice("choice"),
            m_line_break("cr"),
            m_line_break_ext("cr++") {
        }
        
        ~format_decl_plugin() override {}

        void finalize() override {
            if (m_format_sort)
                m_manager->dec_ref(m_format_sort);
        }

        decl_plugin * mk_fresh() override {
            return alloc(format_decl_plugin);
        }
        
        sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override {
            SASSERT(k == FORMAT_SORT);
            return m_format_sort;
        }
        
        func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                 unsigned arity, sort * const * domain, sort * range) override {
            switch (k) {
            case OP_NIL:    
                return m_manager->mk_func_decl(m_nil, arity, domain, m_format_sort, 
                                               func_decl_info(m_family_id, OP_NIL));
            case OP_STRING: 
                return m_manager->mk_func_decl(m_string, arity, domain, m_format_sort, 
                                               func_decl_info(m_family_id, OP_STRING, num_parameters, parameters));
            case OP_INDENT:
                return m_manager->mk_func_decl(m_indent, arity, domain, m_format_sort,
                                               func_decl_info(m_family_id, OP_INDENT, num_parameters, parameters));
            case OP_COMPOSE:
                return m_manager->mk_func_decl(m_compose, arity, domain, m_format_sort,
                                               func_decl_info(m_family_id, OP_COMPOSE));
            case OP_CHOICE:
                return m_manager->mk_func_decl(m_choice, arity, domain, m_format_sort,
                                               func_decl_info(m_family_id, OP_CHOICE));
            case OP_LINE_BREAK:
                return m_manager->mk_func_decl(m_line_break, arity, domain, m_format_sort,
                                               func_decl_info(m_family_id, OP_LINE_BREAK));
                
            case OP_LINE_BREAK_EXT:
                return m_manager->mk_func_decl(m_line_break_ext, arity, domain, m_format_sort, 
                                               func_decl_info(m_family_id, OP_LINE_BREAK_EXT, num_parameters, parameters));
            default:
                return nullptr;
            }
        }
    };

    family_id get_format_family_id(ast_manager & m) {
        symbol f("format");
        if (!fm(m).has_plugin(f)) 
            fm(m).register_plugin(f, alloc(format_decl_plugin));
        return fm(m).mk_family_id(f);
    }

    static family_id fid(ast_manager & m) {
        return get_format_family_id(m);
    }

    sort * fsort(ast_manager & m) {
        return fm(m).mk_sort(fid(m), FORMAT_SORT);
    }

    struct flat_visitor {
        ast_manager & m_manager;
        family_id     m_fid;

        flat_visitor(ast_manager & m):
            m_manager(fm(m)),
            m_fid(fid(m)) {
            SASSERT(m_manager.is_format_manager());
        }
        
        format * visit(var *) { UNREACHABLE(); return nullptr; }
        format * visit(quantifier * q, format *, format * const *, format * const *) { UNREACHABLE(); return nullptr; }
        format * visit(format * n, format * const * children) {
            if (is_app_of(n, m_fid, OP_LINE_BREAK)) 
                return mk_string(m_manager, " ");
            else if (is_app_of(n, m_fid, OP_LINE_BREAK_EXT))
                return mk_string(m_manager, n->get_decl()->get_parameter(0).get_symbol().bare_str());
            else if (is_app_of(n, m_fid, OP_CHOICE))
                return to_app(n->get_arg(0));
            else 
                return m_manager.mk_app(n->get_decl(), n->get_num_args(), (expr *const*) children);
        }
    };

    format * flat(ast_manager & m, format * f) {
        flat_visitor v(m);
        recurse_expr<format *, flat_visitor, true, true> r(v);
        return r(f);
    }

    format * mk_string(ast_manager & m, char const * str) {
        symbol s(str);
        parameter p(s);
        return fm(m).mk_app(fid(m), OP_STRING, 1, &p, 0, nullptr);
    }
    
    format * mk_int(ast_manager & m, int i) {
        char buffer[128];
#ifdef _WINDOWS
        sprintf_s(buffer, ARRAYSIZE(buffer), "%d", i);
#else
        sprintf(buffer, "%d", i);
#endif
        return mk_string(m, buffer); 
    }
    
    format * mk_unsigned(ast_manager & m, unsigned u) {
        char buffer[128];
#ifdef _WINDOWS
        sprintf_s(buffer, ARRAYSIZE(buffer), "%u", u);
#else
        sprintf(buffer, "%u", u);
#endif
        return mk_string(m, buffer); 
    }
    
    format * mk_indent(ast_manager & m, unsigned i, format * f) {
        parameter p(i);
        expr * e = static_cast<expr*>(f);
        return fm(m).mk_app(fid(m), OP_INDENT, 1, &p, 1, &e);
    }
    
    format * mk_line_break(ast_manager & m) {
        return fm(m).mk_app(fid(m), OP_LINE_BREAK);
    }

    format * mk_choice(ast_manager & m, format * f1, format * f2) {
        return fm(m).mk_app(fid(m), OP_CHOICE, f1, f2);
    }
        
    format * mk_group(ast_manager & m, format * f) {
        return mk_choice(m, flat(m, f), f);
    }
    
    format * mk_compose(ast_manager & m, unsigned num_children, format * const * children) {
        return fm(m).mk_app(fid(m), OP_COMPOSE, num_children, (expr * const *) children);
    }
    
    format * mk_compose(ast_manager & m, format * f1, format * f2) {
        return fm(m).mk_app(fid(m), OP_COMPOSE, f1, f2);
    }
    
    format * mk_compose(ast_manager & m, format * f1, format * f2, format * f3) {
        return fm(m).mk_app(fid(m), OP_COMPOSE, f1, f2, f3);
    }
    
    format * mk_compose(ast_manager & m, format * f1, format * f2, format * f3, format * f4) {
        expr * f[4] = { f1, f2, f3, f4 };
        return fm(m).mk_app(fid(m), OP_COMPOSE, 4, f);
    }
    
    format * mk_nil(ast_manager & m) {
        return fm(m).mk_app(fid(m), OP_NIL);
    }

};
