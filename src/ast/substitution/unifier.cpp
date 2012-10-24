/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    unifier.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-28.

Revision History:

--*/
#include"unifier.h"
#include"ast_pp.h"

void unifier::reset(unsigned num_offsets) {
    m_todo.reset();
    m_find.reset();
    m_size.reset();
}

/**
   \brief Find with path compression.
*/
expr_offset unifier::find(expr_offset p) {
    buffer<expr_offset> path;
    expr_offset next;
    while (m_find.find(p, next)) {
        path.push_back(p);
        p = next;
    }
    buffer<expr_offset>::iterator it  = path.begin();
    buffer<expr_offset>::iterator end = path.end();
    for (; it != end; ++it) {
        expr_offset & prev = *it;
        m_find.insert(prev, p);
    }
    return p;
}

void unifier::save_var(expr_offset const & p, expr_offset const & t) {
    expr * n = p.get_expr();
    if (is_var(n)) {
        unsigned off = p.get_offset();
        m_subst->insert(to_var(n)->get_idx(), off, t);
    }
}


/**
   \brief Merge the equivalence classes of n1 and n2. n2 will be the
   root of the resultant equivalence class.
*/
void unifier::union1(expr_offset const & n1, expr_offset const & n2) {
    DEBUG_CODE({
        expr_offset f;
        SASSERT(!m_find.find(n1, f));
        SASSERT(!m_find.find(n2, f));
    });
    unsigned sz1 = 1;
    unsigned sz2 = 1;
    m_size.find(n1, sz1);
    m_size.find(n2, sz2);
    m_find.insert(n1, n2);
    m_size.insert(n2, sz1 + sz2);
    save_var(n1, n2);
}

/**
   \brief Merge the equivalence classes of n1 and n2. The root of the
   resultant equivalence class is the one with more elements.
*/
void unifier::union2(expr_offset n1, expr_offset n2) {
    DEBUG_CODE({
        expr_offset f;
        SASSERT(!m_find.find(n1, f));
        SASSERT(!m_find.find(n2, f));
    });
    unsigned sz1 = 1;
    unsigned sz2 = 1;
    m_size.find(n1, sz1);
    m_size.find(n2, sz2);
    if (sz1 > sz2) 
        std::swap(n1, n2);
    m_find.insert(n1, n2);
    m_size.insert(n2, sz1 + sz2);
    save_var(n1, n2);
}

bool unifier::unify_core(expr_offset p1, expr_offset p2) {
    entry e(p1, p2);
    m_todo.push_back(e);
    while (!m_todo.empty()) {
        entry const & e = m_todo.back();
        p1 = find(e.first);
        p2 = find(e.second);
        m_todo.pop_back();
        if (p1 != p2) {
            expr * n1 = p1.get_expr();
            expr * n2 = p2.get_expr();
            SASSERT(!is_quantifier(n1));
            SASSERT(!is_quantifier(n2));
            bool v1 = is_var(n1);
            bool v2 = is_var(n2);
            if (v1 && v2) {
                union2(p1, p2);
            }
            else if (v1) {
                union1(p1, p2);
            }
            else if (v2) {
                union1(p2, p1);
            }
            else {
                app * a1 = to_app(n1);
                app * a2 = to_app(n2);

                unsigned off1 = p1.get_offset();
                unsigned off2 = p2.get_offset();
                if (a1->get_decl() != a2->get_decl() || a1->get_num_args() != a2->get_num_args())
                    return false;
                union2(p1, p2);
                unsigned j = a1->get_num_args();
                while (j > 0) {
                    --j;
                    entry new_e(expr_offset(a1->get_arg(j), off1),
                                expr_offset(a2->get_arg(j), off2));
                    m_todo.push_back(new_e);
                }
            }
        }
    }
    return true;
}

bool unifier::operator()(unsigned num_exprs, expr ** es, substitution & s, bool use_offsets) {
    SASSERT(num_exprs > 0);
    unsigned num_offsets = use_offsets ? num_exprs : 1;
    reset(num_offsets);
    m_subst = &s;    
#if 1
    TRACE("unifier", for (unsigned i = 0; i < num_exprs; ++i) tout << mk_pp(es[i], m_manager) << "\n";);
    for (unsigned i = s.get_num_bindings(); i > 0; ) {
        --i;
        std::pair<unsigned,unsigned> bound;
        expr_offset root, child;
        s.get_binding(i, bound, root);
        TRACE("unifier", tout << bound.first << " |-> " << mk_pp(root.get_expr(), m_manager) << "\n";);
        if (is_var(root.get_expr())) {
            var* v = m_manager.mk_var(bound.first,to_var(root.get_expr())->get_sort());
            child = expr_offset(v, bound.second);
            unsigned sz1 = 1;
            unsigned sz2 = 1;
            m_size.find(child, sz1);
            m_size.find(root, sz2);
            m_find.insert(child, root);
            m_size.insert(root, sz1 + sz2);
        }
    }
#endif
    for (unsigned i = 0; i < num_exprs - 1; i++) {
        if (!unify_core(expr_offset(es[i], use_offsets ? i : 0), 
                        expr_offset(es[i+1], use_offsets ? i + 1 : 0))) {
            m_last_call_succeeded = false;
            return m_last_call_succeeded;
        }
    }
    
    m_last_call_succeeded = m_subst->acyclic();
    return m_last_call_succeeded;
}

bool unifier::operator()(expr * e1, expr * e2, substitution & s, bool use_offsets) {
    expr * es[2] = { e1, e2 };
    return operator()(2, es, s, use_offsets);
}
    
