/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    func_decl_dependencies.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-12-15.

Revision History:

--*/
#include "ast/func_decl_dependencies.h"
#include "ast/for_each_expr.h"
#include "ast/ast_util.h"

struct collect_dependencies_proc {
    ast_manager &     m_manager;
    func_decl_set &   m_set;
    bool              m_ng_only; // collect only declarations in non ground expressions
   
    collect_dependencies_proc(ast_manager & m, func_decl_set & s, bool ng_only):
        m_manager(m),
        m_set(s),
        m_ng_only(ng_only) {}

    void operator()(var * n) {}
    
    void operator()(quantifier * n) {}
    
    void operator()(app * n) {        
        // We do not need to track dependencies on constants ...
        if (n->get_num_args()==0) 
            return;
        if (m_ng_only && is_ground(n))
            return;
        // ... and interpreted function symbols
        func_decl * d = n->get_decl();
        if (d->get_family_id() == null_family_id) {
            m_set.insert(d);
        }
    }
};

void collect_func_decls(ast_manager & m, expr * n, func_decl_set & r, bool ng_only) {
    collect_dependencies_proc proc(m, r, ng_only);
    for_each_expr(proc, n);
}

void func_decl_dependencies::reset() {
    dependency_graph::iterator it  = m_deps.begin();
    dependency_graph::iterator end = m_deps.end();
    for (; it != end; ++it) {
        func_decl * f  = (*it).m_key;
        func_decl_set * s    = (*it).m_value;
        m_manager.dec_ref(f);
        dec_ref(m_manager, *s);
        dealloc(s);
    }
    m_deps.reset();
}

void func_decl_dependencies::collect_func_decls(expr * n, func_decl_set * s) {
    ::collect_func_decls(m_manager, n, *s, false);
}

void func_decl_dependencies::collect_ng_func_decls(expr * n, func_decl_set * s) {
    ::collect_func_decls(m_manager, n, *s, true);
}

/**
   \brief Functor for finding cycles in macro definitions
*/
class func_decl_dependencies::top_sort {
    enum color { OPEN, IN_PROGRESS, CLOSED };
    dependency_graph &  m_deps;

    typedef obj_map<func_decl, color> color_map;
    color_map               m_colors;
    ptr_vector<func_decl>   m_todo;

    func_decl_set * definition(func_decl * f) const {        
        func_decl_set * r = nullptr;
        m_deps.find(f, r);
        return r;
    }

    color get_color(func_decl * f) const {
        if (!f) 
            return CLOSED;
        color_map::iterator it = m_colors.find_iterator(f);
        if (it != m_colors.end()) 
            return it->m_value;
        return OPEN;
    }

    void set_color(func_decl * f, color c) {        
        m_colors.insert(f, c);
    }

    void visit(func_decl * f, bool & visited) {
        if (get_color(f) != CLOSED) {
            m_todo.push_back(f);
            visited = false;
        }
    }

    bool visit_children(func_decl * f) {              
        func_decl_set * def = definition(f);
        if (!def) 
            return true;
        bool visited = true;
        func_decl_set::iterator it  = def->begin();
        func_decl_set::iterator end = def->end();
        for (; it != end; ++it) {
            visit(*it, visited);
        }
        return visited;
    }

    bool all_children_closed(func_decl * f) const {
        func_decl_set * def = definition(f);
        if (!def) 
            return true;
        func_decl_set::iterator it  = def->begin();
        func_decl_set::iterator end = def->end();
        for (; it != end; ++it) {
            if (get_color(*it) != CLOSED)
                return false;
        }
        return true;
    }

    /**
       \brief Return \c true if a cycle is detected.
    */
    bool main_loop(func_decl * f) {
        if (get_color(f) == CLOSED) 
            return false;
        m_todo.push_back(f);
        while (!m_todo.empty()) {
            func_decl * cf = m_todo.back();
            
            switch (get_color(cf)) {
            case CLOSED:                
                m_todo.pop_back();
                break;
            case OPEN:
                set_color(cf, IN_PROGRESS);
                if (visit_children(cf)) {
                    SASSERT(m_todo.back() == cf);
                    m_todo.pop_back();
                    set_color(cf, CLOSED);
                }
                break;
            case IN_PROGRESS: 
                if (all_children_closed(cf)) {
                    SASSERT(m_todo.back() == cf);
                    set_color(cf, CLOSED);
                } else {
                    m_todo.reset();
                    return true;
                }
                break;
            default:
                UNREACHABLE();
            }
        }
        return false;
    }

public:
    top_sort(dependency_graph & deps) : m_deps(deps) {}
    
    bool operator()(func_decl * new_decl) {

        // [Leo]: It is not trivial to reuse m_colors between different calls since we are update the graph.
        // To implement this optimization, we need an incremental topological sort algorithm.
        // The trick of saving the dependencies will save a lot of time. So, I don't think we really
        // need a incremental top-sort algo. 
        m_colors.reset();
        return main_loop(new_decl);
    }
};

bool func_decl_dependencies::insert(func_decl * f, func_decl_set * s) {
    if (m_deps.contains(f)) {
        dealloc(s);
        return false;
    }

    m_deps.insert(f, s);

    top_sort cycle_detector(m_deps);
    if (cycle_detector(f)) {
        m_deps.erase(f);
        dealloc(s);
        return false;
    }

    m_manager.inc_ref(f);
    inc_ref(m_manager, *s);
    return true;
}

void func_decl_dependencies::erase(func_decl * f) {
    func_decl_set * s = nullptr;
    if (m_deps.find(f, s)) {
        m_manager.dec_ref(f);
        dec_ref(m_manager, *s);
        m_deps.erase(f);
        dealloc(s);
    }
}

void func_decl_dependencies::display(std::ostream & out) {
    // TODO
}
