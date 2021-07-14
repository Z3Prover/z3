/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_ll_pp.cpp

Abstract:
 
    AST low level pretty printer.
    
Author:

    Leonardo de Moura (leonardo) 2006-10-19.

Revision History:

--*/

#include<iostream>
#include "ast/for_each_ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"

// #define AST_LL_PP_SHOW_FAMILY_NAME

class ll_printer {
    std::ostream & m_out;
    ast_manager &  m_manager;
    ast *          m_root;
    bool           m_only_exprs;
    bool           m_compact;
    arith_util     m_autil;
    datatype_util  m_dt;

    void display_def_header(ast * n) {
        if (n != m_root) {
            m_out << "#" << n->get_id() << " := ";
        }
    }

    void display_child_ref(ast * n) {
        m_out << "#" << n->get_id();
    }

    void display_name(func_decl * decl) {
        m_out << decl->get_name();
    }

    bool process_numeral(expr * n) {
        rational val;
        bool is_int;
        if (m_autil.is_numeral(n, val, is_int)) {
            m_out << val;
            if (!is_int && val.is_int()) m_out << ".0";
            return true;
        }
        return false;
    }

    void display_sort(sort * s) {
        m_out << s->get_name();
        display_params(s);
    }
        
    void display_child(ast * n) {
        switch (n->get_kind()) {
        case AST_SORT:
            display_sort(to_sort(n));
            break;
        case AST_APP:
            if (process_numeral(to_expr(n))) {
                // skip
            }
            else if (to_app(n)->get_num_args() == 0) {
                display_name(to_app(n)->get_decl());
                display_params(to_app(n)->get_decl());
            }
            else {
                display_child_ref(n);
            }
            break;
        default:
            display_child_ref(n);
        }
    }

    template<typename T>
    void display_children(unsigned num_children, T * const * children) {
        for (unsigned i = 0; i < num_children; i++) {
            if (i > 0) {
                m_out << " ";
            }
            display_child(children[i]);
        }
    }

    void display_params(decl * d) {
        unsigned n = d->get_num_parameters();
        parameter const* p = d->get_parameters();
        if (n > 0 && p[0].is_symbol() && d->get_name() == p[0].get_symbol()) {
            n--;
            p++;
        } 

        if (n > 0 && !d->private_parameters()) {
            m_out << "[";
            for (unsigned i = 0; i < n; i ++) {
                if (p[i].is_ast()) {
                    display_child(p[i].get_ast());
                }
                else {
                    m_out << p[i];
                }
                m_out << (i < n-1 ? ":" : "");
            }
            m_out << "]";
        }
        else if (is_func_decl(d) && m_dt.is_is(to_func_decl(d))) {
            func_decl* fd = m_dt.get_recognizer_constructor(to_func_decl(d));
            m_out << " " << fd->get_name();
        }
    }

public:

    ll_printer(std::ostream & out, ast_manager & m, ast * n, bool only_exprs, bool compact):
        m_out(out),
        m_manager(m),
        m_root(n),
        m_only_exprs(only_exprs),
        m_compact(compact),
        m_autil(m),
        m_dt(m) {
    }

    void pp(ast* n) {
        ast_mark visited;
        pp(n, visited);
    }

    void pp(ast* n, ast_mark& visited) {
        if (is_sort(n)) {
            display_sort(to_sort(n));
        }
        else {
            for_each_ast(*this, visited, n, true);
        }
    }

    void operator()(sort* n) {
    }

    void operator()(func_decl * n) {
        if (m_only_exprs) {
            return;
        }
        if (n->get_family_id() != null_family_id) {
            return;
        }
        m_out << "decl ";
        display_name(n);
        m_out << " :: ";
        if (n->get_arity() == 0) {
            display_child(n->get_range());
        }
        else {
            m_out << "(-> ";
            display_children(n->get_arity(), n->get_domain());
            m_out << " ";
            display_child(n->get_range());
            m_out << ")";
            display_params(n);
            if (n->is_associative()) {
                m_out << " :assoc";
            }
            if (n->is_commutative()) {
                m_out << " :comm";
            }
            if (n->is_injective()) {
                m_out << " :inj";
            }
        }
        m_out << "\n";
    }
        
    void operator()(var * n) {
        display_def_header(n);
        m_out << "(:var " << to_var(n)->get_idx() << " ";
        display_sort(n->get_sort());
        m_out << ")\n";
    }

    void operator()(app * n) {
        if (m_autil.is_numeral(n)) {
            if (!m_compact) 
                display_def_header(n);
            if (n == m_root || !m_compact) {
                process_numeral(n);
                m_out << "\n";
            }
        }
        else if (m_manager.is_proof(n)) {
            display_def_header(n);
            m_out << "[" << n->get_decl()->get_name();
            unsigned num_params = n->get_decl()->get_num_parameters();
            for (unsigned i = 0; i < num_params; ++i) {
                m_out << " ";
                m_out << n->get_decl()->get_parameter(i);
            }
            unsigned num_parents = m_manager.get_num_parents(n);
            for (unsigned i = 0; i < num_parents; i++) {
                m_out << " ";
                display_child(m_manager.get_parent(n, i));
            }
            m_out << "]: ";
            if (m_manager.has_fact(n)) {
                // display(m_manager.get_fact(n), 6);
                display_child(m_manager.get_fact(n));
            }
            else 
                m_out << "*";
            m_out << "\n";
        }
        else if (m_compact && n->get_num_args() == 0) {
            if (n == m_root) {
                display_child(n);
                m_out << "\n";
            }
        }
        else {
            display_def_header(n);
            if (n->get_num_args() > 0)
                m_out << "(";
            display_name(n->get_decl());
            display_params(n->get_decl());
            if (n->get_num_args() > 0) {
                m_out << " ";
                display_children(n->get_num_args(), n->get_args());
                m_out << ")";
            }
#ifdef AST_LL_PP_SHOW_FAMILY_NAME
            if (to_app(n)->get_family_id() != null_family_id) {
                m_out << " family: " << m_manager.get_family_name(to_app(n)->get_family_id());
            }
#endif        
            m_out << "\n";
        }
    }

    void operator()(quantifier * n) {
        display_def_header(n);
        m_out << "(" << (n->get_kind() == forall_k ? "forall" : (n->get_kind() == exists_k ? "exists" : "lambda")) << " ";
        unsigned num_decls = n->get_num_decls();
        m_out << "(vars ";
        for (unsigned i = 0; i < num_decls; i++) {
            if (i > 0) {
                m_out << " ";
            }
            m_out << "(" << n->get_decl_name(i) << " ";
            display_sort(n->get_decl_sort(i));
            m_out << ")";
        }
        m_out << ") ";
        if (n->get_num_patterns() > 0) {
            m_out << "(:pat ";
            display_children(n->get_num_patterns(), n->get_patterns());
            m_out << ") ";
        }
        if (n->get_num_no_patterns() > 0) {
            m_out << "(:nopat ";
            display_children(n->get_num_no_patterns(), n->get_no_patterns());
            m_out << ") ";
        }
        display_child(n->get_expr());
        m_out << ")\n";
    }

    void display(expr * n, unsigned depth) {
        if (is_var(n)) {
            m_out << "(:var " << to_var(n)->get_idx() << ")";
            return;
        }

        if (!is_app(n) || depth == 0 || to_app(n)->get_num_args() == 0) {
            display_child(n);
            return;
        }
        unsigned num_args = to_app(n)->get_num_args();
        
        if (num_args > 0) 
            m_out << "(";
        display_name(to_app(n)->get_decl());
        display_params(to_app(n)->get_decl());
        for (unsigned i = 0; i < num_args && i < 16; i++) {
            m_out << " ";
            display(to_app(n)->get_arg(i), depth-1);
        }
        if (num_args >= 16) 
            m_out << " ...";
        if (num_args > 0)
            m_out << ")";
    }

    void display_bounded(ast * n, unsigned depth) {
        if (!n)
   	     m_out << "null";    
        else if (is_app(n)) {
            display(to_expr(n), depth);
        }
        else if (is_var(n)) {
            m_out << "(:var " << to_var(n)->get_idx() << ")";
        }
        else {
            m_out << "#" << n->get_id();
        }
    }
};

void ast_ll_pp(std::ostream & out, ast_manager & m, ast * n, bool only_exprs, bool compact) {
    ll_printer p(out, m, n, only_exprs, compact);
    p.pp(n);
}

void ast_ll_pp(std::ostream & out, ast_manager & m, ast * n, ast_mark & visited, bool only_exprs, bool compact) {
    ll_printer p(out, m, n, only_exprs, compact);
    p.pp(n, visited);
}

void ast_def_ll_pp(std::ostream & out, ast_manager & m, ast * n, ast_mark & visited, bool only_exprs, bool compact) {
    ll_printer p(out, m, nullptr, only_exprs, compact);
    p.pp(n, visited);
}

void ast_ll_bounded_pp(std::ostream & out, ast_manager & m, ast * n, unsigned depth) {
    ll_printer p(out, m, nullptr, false, true);
    p.display_bounded(n, depth);
}
