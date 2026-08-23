/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    ast_translation.h

Abstract:

    AST translation functions

Author:

    Christoph Wintersteiger (t-cwinte) 2008-11-20

Revision History:

    2011-05-26: New local translation class.

--*/
#pragma once

#include "ast/ast.h"

class ast_translation {
    struct frame {
        ast *    m_n;
        unsigned m_idx;
        unsigned m_cpos;
        unsigned m_rpos;
        frame(ast * n, unsigned idx, unsigned cpos, unsigned rpos):m_n(n), m_idx(idx), m_cpos(cpos), m_rpos(rpos) {}
    };
    ast_manager &       m_from_manager;
    ast_manager &       m_to_manager;
    svector<frame>      m_frame_stack;
    ptr_vector<ast>     m_extra_children_stack; // for sort and func_decl, since they have nested AST in their parameters
    ptr_vector<ast>     m_result_stack; 
    obj_map<ast, ast*>  m_cache;
    unsigned            m_loop_count;
    unsigned            m_hit_count;
    unsigned            m_miss_count;
    unsigned            m_insert_count;
    unsigned            m_num_process;

    void cache(ast * s, ast * t);
    void collect_decl_extra_children(decl * d);
    void push_frame(ast * n);
    bool visit(ast * n);
    void copy_params(decl * d, unsigned rpos, buffer<parameter> & ps);
    void mk_sort(sort * s, frame & fr);
    void mk_func_decl(func_decl * f, frame & fr);
    
    ast * process(ast const * n);

public:
    ast_translation(ast_manager & from, ast_manager & to, bool copy_plugins = true) : m_from_manager(from), m_to_manager(to) {
        m_loop_count = 0;
        m_hit_count = 0;
        m_miss_count = 0;
        m_insert_count = 0;
        m_num_process = 0;
        if (&from != &to) {
            if (copy_plugins)
                m_to_manager.copy_families_plugins(m_from_manager);
            m_to_manager.update_fresh_id(m_from_manager);
        }
    }

    ~ast_translation();

    template<typename T>
    T * operator()(T const * n) { 
        return translate(n);
    }

    template<typename T>
    T * translate(T const * n) { 
        if (&from() == &to()) return const_cast<T*>(n);
        SASSERT(!n || from().contains(const_cast<T*>(n)));
        ast * r = process(n);
        SASSERT((!n && !r) || to().contains(const_cast<ast*>(r)));
        return static_cast<T*>(r);
    }


    ast_manager & from() const { return m_from_manager; }
    ast_manager & to() const { return m_to_manager; }

    template<typename T>
    ref_vector<T, ast_manager> operator()(ref_vector<T, ast_manager> const& src) {
        ref_vector<T, ast_manager> dst(to());
        for (expr* v : src) dst.push_back(translate(v));
        return dst;
    }

    void reset_cache();
    void cleanup();
    
    unsigned loop_count() const { return m_loop_count; }
    unsigned hit_count() const { return m_hit_count; }
    unsigned miss_count() const { return m_miss_count; }
    unsigned insert_count() const { return m_insert_count; }
    unsigned long long get_num_collision() const { return m_cache.get_num_collision(); }
};

// Translation with non-persistent cache.
inline ast * translate(ast const * a, ast_manager & from, ast_manager & to) {
    return ast_translation(from, to)(a);
}

inline expr * translate(expr const * e, ast_manager & from, ast_manager & to) {
    return ast_translation(from, to)(e);
}


class expr_dependency_translation {
    ast_translation & m_translation;
    ptr_vector<expr>  m_buffer;
public:
    expr_dependency_translation(ast_translation & t):m_translation(t) {}
    expr_dependency * operator()(expr_dependency * d);
};

inline expr_dependency * translate(expr_dependency * d, ast_manager & from, ast_manager & to) {
    ast_translation t(from, to);
    expr_dependency_translation td(t);
    return td(d);
}

