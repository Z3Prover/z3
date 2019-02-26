/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    substitution.cpp

Abstract:

    A substitution, that is, a mapping from (variable, offset) to (expr, offset).
    We use offsets in order to avoid creating variants of terms.

Author:

    Leonardo de Moura (leonardo) 2008-02-01.

Revision History:

--*/
#include "ast/substitution/substitution.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/rewriter/rewriter.h"

substitution::substitution(ast_manager & m):
    m_manager(m),
    m_refs(m),
    m_new_exprs(m),
    m_state(CLEAN) {
}

void substitution::reset() {
    m_subst.reset(); 
    m_vars.reset();
    m_refs.reset();
    m_scopes.reset();
    reset_cache();
}


void substitution::reset_cache() {
    TRACE("subst_bug", tout << "substitution::reset_cache\n";
          for (unsigned i = 0; i < m_new_exprs.size(); i++) { tout << mk_pp(m_new_exprs.get(i), m_manager) << "\nref_count: " << m_new_exprs.get(i)->get_ref_count() << "\n"; });

    m_apply_cache.reset();
    m_new_exprs.reset();
    m_state = CLEAN;
}

void substitution::pop_scope(unsigned num_scopes) {
    unsigned lvl     = m_scopes.size();
    SASSERT(num_scopes <= lvl);
    unsigned new_lvl = lvl - num_scopes;
    unsigned old_sz  = m_scopes[new_lvl];
    unsigned curr_sz = m_vars.size();
    SASSERT(old_sz <= curr_sz);
    for (unsigned i = old_sz; i < curr_sz; i++) {
        var_offset & curr = m_vars[i];
        m_subst.erase(curr.first, curr.second);
    }
    m_vars.shrink(old_sz);
    m_refs.shrink(old_sz);
    m_scopes.shrink(new_lvl);
    reset_cache();    
}

inline void substitution::apply_visit(expr_offset const & n, bool & visited) {
    if (!m_apply_cache.contains(n)) {
        m_todo.push_back(n);
        visited = false;
    }
}

void substitution::apply(unsigned num_actual_offsets, unsigned const * deltas, expr_offset const & n, 
                         expr_offset const & s, expr_offset const & t, expr_ref & result) {
    
    TRACE("subst_bug", tout << "BEGIN substitution::apply\n";);


    // It is incorrect to cache results between different calls if we are applying a substitution
    // modulo a substitution s -> t.
    if (m_state == INSERT || s != expr_offset(nullptr,0))
        reset_cache();

    m_state = APPLY;

    unsigned         j;
    expr *           e = nullptr;
    unsigned         off;
    expr_offset      n1;
    bool             visited;
    unsigned         num_args;
    ptr_buffer<expr> new_args;

    m_todo.push_back(n);
    while (!m_todo.empty()) {
        expr_offset n = m_todo.back();
        TRACE("subst_bug", tout << "n: " << mk_pp(n.get_expr(), m_manager) << " : " << n.get_offset() << "\n";);
        if (m_apply_cache.contains(n)) {
            m_todo.pop_back();
            continue;
        }
        expr_offset n_prime = n == s ? t : n;
        TRACE("subst_bug", tout << "n_prime: " << mk_pp(n_prime.get_expr(), m_manager) << " : " << n_prime.get_offset() << "\n";);
        visited = true;
        e   = n_prime.get_expr();
        off = n_prime.get_offset();
        switch (e->get_kind()) {
        case AST_VAR:
            if (find(to_var(e)->get_idx(), off, n1)) {
                apply_visit(n1, visited);
                TRACE("subst_bug", tout << "visited: " << visited << ", n1: " << mk_pp(n1.get_expr(), m_manager) << " : " << n1.get_offset() << "\n";);
                if (visited) {
                    m_todo.pop_back();
                    expr * new_expr = nullptr;
                    m_apply_cache.find(n1, new_expr);
                    m_apply_cache.insert(n, new_expr);
                    TRACE("subst_bug", tout << "1. insert n: " << mk_pp(n.get_expr(), m_manager) << " : " << n.get_offset() 
                          << " --> " << mk_pp(new_expr, m_manager) << "\n";);
                }
            }
            else {
                m_todo.pop_back();
                SASSERT(off < num_actual_offsets);
                unsigned delta = deltas[off];
                expr * new_expr = e;
                if (delta > 0) { 
                    new_expr = m_manager.mk_var(to_var(e)->get_idx() + delta, to_var(e)->get_sort());
                    m_new_exprs.push_back(new_expr);
                }
                m_apply_cache.insert(n, new_expr);
                TRACE("subst_bug", tout << "2. insert n: " << mk_pp(n.get_expr(), m_manager) << " : " << n.get_offset() 
                      << " --> " << mk_pp(new_expr, m_manager) << "\n";);
            }
            break;
        case AST_APP:
            num_args = to_app(e)->get_num_args();
            j        = num_args;
            while (j > 0) {
                --j;
                apply_visit(expr_offset(to_app(e)->get_arg(j), off), visited);
            }
            if (visited) {
                m_todo.pop_back();
                new_args.reset();
                bool has_new_args = false;
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg     = to_app(e)->get_arg(i);
                    expr * new_arg = nullptr;
                    
                    VERIFY(m_apply_cache.find(expr_offset(arg, off), new_arg));
                    new_args.push_back(new_arg);
                    if (arg != new_arg)
                        has_new_args = true;
                }
                if (!has_new_args) {
                    m_apply_cache.insert(n, e);
                    TRACE("subst_bug", tout << "3. insert n: " << mk_pp(n.get_expr(), m_manager) << " : " << n.get_offset() 
                          << " --> " << mk_pp(e, m_manager) << "\n";);
                }
                else {
                    expr * new_expr = m_manager.mk_app(to_app(e)->get_decl(), new_args.size(), new_args.c_ptr());
                    m_new_exprs.push_back(new_expr);
                    m_apply_cache.insert(n, new_expr);
                    TRACE("subst_bug", tout << "3. insert n: " << mk_pp(n.get_expr(), m_manager) << " : " << n.get_offset() 
                          << " --> " << mk_pp(new_expr, m_manager) << "\n";);
                }
            }
            break;
        case AST_QUANTIFIER: {
            quantifier* q = to_quantifier(e);
            unsigned num_vars = q->get_num_decls();
            substitution subst(m_manager);
            expr_ref er(m_manager);
            subst.reserve(m_subst.offsets_capacity(), m_subst.vars_capacity() + num_vars);
            var_shifter var_sh(m_manager);
            expr_offset r;
            for (unsigned i = 0; i < m_subst.offsets_capacity(); i++) {
                for (unsigned j = 0; j < m_subst.vars_capacity(); j++) {
                    if (find(j, i, r)) {
                        var_sh(r.get_expr(), num_vars, er);
                        subst.insert(j + num_vars, i, expr_offset(er, r.get_offset()));
                    }
                }
            }
            expr_offset body(q->get_expr(), off);
            expr_ref s1_ref(m_manager), t1_ref(m_manager);
            if (s.get_expr() != nullptr) {
                var_sh(s.get_expr(), num_vars, s1_ref);
            }
            if (t.get_expr() != nullptr) {
                var_sh(t.get_expr(), num_vars, t1_ref);
            }
            expr_offset s1(s1_ref, s.get_offset());
            expr_offset t1(t1_ref, t.get_offset());
            expr_ref_vector pats(m_manager), no_pats(m_manager);
            for (unsigned i = 0; i < q->get_num_patterns(); ++i) {
                subst.apply(num_actual_offsets, deltas, expr_offset(q->get_pattern(i), off), s1, t1, er);
                pats.push_back(std::move(er));
            }
            for (unsigned i = 0; i < q->get_num_no_patterns(); ++i) {
                subst.apply(num_actual_offsets, deltas, expr_offset(q->get_no_pattern(i), off), s1, t1, er);
                no_pats.push_back(std::move(er));
            }
            subst.apply(num_actual_offsets, deltas, body, s1, t1, er);
            er = m_manager.update_quantifier(q, pats.size(), pats.c_ptr(), no_pats.size(), no_pats.c_ptr(), er);
            m_todo.pop_back();
            m_new_exprs.push_back(std::move(er));
            m_apply_cache.insert(n, er);            
            break;
        }            
        default:
            UNREACHABLE();
        }
    }
    SASSERT(m_apply_cache.contains(n));
    VERIFY(m_apply_cache.find(n, e));
    m_new_exprs.push_back(e);
    result = e;
    
    if (s != expr_offset(nullptr,0))
        reset_cache();
    
    TRACE("subst_bug", tout << "END substitution::apply\nresult:\n" << mk_pp(e, m_manager) << "\nref_count: " << e->get_ref_count() << "\n";);
}

inline substitution::color substitution::get_color(expr_offset const & p) const {
    color c;
    if (m_color.find(p, c)) 
        return c;
    return White;
}

inline void substitution::set_color(expr_offset const & p, color c) {
    m_color.insert(p, c);
}

inline void substitution::visit(expr_offset const & p, bool & visited) {
    if (get_color(p) != Black) {
        m_todo.push_back(p);
        visited = false;
    }
}

bool substitution::visit_children(expr_offset const & p) {
    bool visited = true;
    expr * n     = p.get_expr();
    unsigned off;
    expr_offset p1;
    unsigned j;
    switch (n->get_kind()) {
    case AST_VAR:
        if (find(p, p1) && p != p1)
            visit(p1, visited);
        break;
    case AST_APP:
        off  = p.get_offset();
        j    = to_app(n)->get_num_args();
        while (j > 0) {
            --j;
            visit(expr_offset(to_app(n)->get_arg(j), off), visited);
        }
        break;
    default:
        UNREACHABLE();
    }
    return visited;
}

bool substitution::acyclic(expr_offset p) {
    if (get_color(p) == Black)
        return true;
    m_todo.reset();
    m_todo.push_back(p);
    while (!m_todo.empty()) {
        expr_offset p = m_todo.back();
        switch (get_color(p)) {
        case Black:
            m_todo.pop_back();
            break;
        case White:
            set_color(p, Grey);
            if (visit_children(p)) {
                set_color(p, Black);
                SASSERT(m_todo.back() == p);
                m_todo.pop_back();
            }
            break;
        case Grey:
            if (!visit_children(p))
                return false;
            set_color(p, Black);
            SASSERT(m_todo.back() == p);
            m_todo.pop_back();
            break;
        }
    }
    return true;
}

bool substitution::acyclic() {
    m_color.reset();
    expr_offset r;
    svector<var_offset>::iterator it  = m_vars.begin();
    svector<var_offset>::iterator end = m_vars.end();
    for (; it != end; ++it) {
        m_subst.find(it->first, it->second, r);
        if (!acyclic(r))
            return false;
    }
    return true;
}

void substitution::display(std::ostream & out, unsigned num_actual_offsets, unsigned const * deltas) {
    reset_cache();
    for (unsigned i = 0; i < num_actual_offsets; i++)
        for (unsigned j = 0; j < m_subst.vars_capacity(); j++) {
            expr_offset r;
            if (find(j, i, r)) {
                expr_ref tmp(m_manager);
                apply(num_actual_offsets, deltas, r, tmp);
                out << "VAR " << j << ":" << i << " -->\n" << mk_pp(tmp, m_manager) << "\n";
            }
        }
}

void substitution::display(std::ostream & out) {
    for (unsigned i = 0; i < m_subst.offsets_capacity(); i++)
        for (unsigned j = 0; j < m_subst.vars_capacity(); j++) {
            expr_offset r;
            if (find(j, i, r))
                out << "VAR " << j << ":" << i << " --> " << r.get_offset() << "\n" << mk_pp(r.get_expr(), m_manager) << "\n";
        }
}

