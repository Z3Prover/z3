/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    lpo.h

Abstract:

    Lexicographical Path Ordering

Author:

    Leonardo de Moura (leonardo) 2008-02-01.

Revision History:

--*/
#include"lpo.h"

/**
   \brief Check whether the variable in t1 occurs in t2.
*/
bool lpo::occurs(expr_offset const & t1, expr_offset const & t2) {
    SASSERT(is_var(t1.get_expr()));
    if (is_ground(t2.get_expr()))
        return false;
    m_todo.reset();
    m_todo.push_back(t2);
    while (!m_todo.empty()) {
        expr_offset t = m_todo.back();
        m_todo.pop_back();
        t = find(t);
        expr * n        = t.get_expr();
        if (is_ground(n))
            continue;
        unsigned offset = t.get_offset();
        unsigned j;
        switch (n->get_kind()) {
        case AST_VAR:
            if (t == t1)
                return true;
            break;
        case AST_APP:
            j = to_app(n)->get_num_args();
            while (j > 0) {
                --j;
                expr * arg = to_app(n)->get_arg(j);
                if (!is_ground(arg)) 
                    m_todo.push_back(expr_offset(arg, offset));
            }
            break;
        default:
            UNREACHABLE();
        }
    }
    return false;
}

inline bool lpo::greater(expr_offset s, expr_offset t, unsigned depth) {
    return lpo::compare(s, t, depth) == GREATER;
}

/**
   \brief Return true if s >_{lpo} t_i forall children t_i of t.
*/
bool lpo::dominates_args(expr_offset s, expr_offset t, unsigned depth) {
    SASSERT(is_app(t.get_expr()));
    unsigned num_args = to_app(t.get_expr())->get_num_args();
    unsigned off      = t.get_offset();
    for (unsigned i = 0; i < num_args; i++) {
        expr * t_i = to_app(t.get_expr())->get_arg(i);
        if (!greater(s, expr_offset(t_i, off), depth+1))
            return false;
    }
    return true;
}

/**
   \brief Return true if s_i >=_{lpo} t for some arg s_i of s.
 */
bool lpo::arg_dominates_expr(expr_offset s, expr_offset t, unsigned depth) {
    SASSERT(is_app(s.get_expr()));
    unsigned num_args = to_app(s.get_expr())->get_num_args();
    unsigned off      = s.get_offset();
    for (unsigned i = 0; i < num_args; i++) {
        expr * s_i = to_app(s.get_expr())->get_arg(i);
        result r   = compare(expr_offset(s_i, off), t, depth+1);
        if (r == EQUAL || r == GREATER)
            return true;
    }
    return false;
}

order::result lpo::lex_compare(expr_offset s, expr_offset t, unsigned depth) {
    SASSERT(is_app(s.get_expr()));
    SASSERT(is_app(t.get_expr()));
    app * _s = to_app(s.get_expr());
    app * _t = to_app(t.get_expr());
    unsigned num_args1 = _s->get_num_args();
    unsigned num_args2 = _t->get_num_args();
    unsigned num_args  = std::min(num_args1, num_args2);
    unsigned off1      = s.get_offset();
    unsigned off2      = t.get_offset();
    result r = EQUAL;
    for (unsigned i = 0; i < num_args; i++) {
        r = compare(expr_offset(_s->get_arg(i), off1), expr_offset(_t->get_arg(i), off2), depth+1);
        if (r != EQUAL)
            break;
    }
    if (r == EQUAL) {
        if (num_args1 > num_args2)
            return GREATER;
        if (num_args1 < num_args2)
            return NOT_GTEQ;
    }
    return r;
}

inline order::result lpo::compare_core(expr_offset s, expr_offset t, unsigned depth) {
    s = find(s);
    t = find(t);
    
    if (max_depth(depth))
        return UNKNOWN;

    if (is_var(s.get_expr()))
        return s == t ? EQUAL : UNCOMPARABLE;
    else if (is_var(t.get_expr()))
        return occurs(t, s) ? GREATER : UNCOMPARABLE;
    else {
        func_decl * f = to_app(s.get_expr())->get_decl();
        func_decl * g = to_app(t.get_expr())->get_decl();
        if (f_greater(f, g))
            return dominates_args(s, t, depth) ? GREATER : NOT_GTEQ;
        else if (f != g)
            return arg_dominates_expr(s, t, depth) ? GREATER : NOT_GTEQ;
        else {
            result r = lex_compare(s, t, depth);
            if (r == GREATER) {
                if (dominates_args(s, t, depth))
                    return GREATER;
            }
            else if (r == EQUAL)
                return EQUAL;
            return to_app(s.get_expr())->get_num_args() > 1 && arg_dominates_expr(s, t, depth) ? GREATER : NOT_GTEQ;
        }
    }
}

order::result lpo::compare(expr_offset s, expr_offset t, unsigned depth) {
    TRACE("lpo", tout << "comparing:\n" << mk_pp(s.get_expr(), m_manager) << "\n" << mk_pp(t.get_expr(), m_manager) << "\n";);
    result r = compare_core(s, t, depth);
    TRACE("lpo", tout << "result of comparing:\n" << mk_pp(s.get_expr(), m_manager) << "\n" << mk_pp(t.get_expr(), m_manager) << "\nresult: " << r << "\n";);
    return r;
}

bool lpo::greater(expr_offset const & t1, expr_offset const & t2, substitution * s) {
    m_subst = s;
    return greater(t1, t2, static_cast<unsigned>(0));
}

order::result lpo::compare(expr_offset const & t1, expr_offset const & t2, substitution * s) {
    m_subst = s;
    result r = compare(t1, t2, static_cast<unsigned>(0));
    if (r != NOT_GTEQ) 
        return r;
    r = compare(t2, t1, static_cast<unsigned>(0));
    if (r == GREATER)
        return LESSER;
    if (r == UNKNOWN)
        return UNKNOWN;
    return UNCOMPARABLE;
}

int lpo::compare_ge(expr_offset const & t1, expr_offset const & t2, substitution * s) {
    m_subst = s;
    result r = compare(t1, t2, static_cast<unsigned>(0));
    switch (r) {
    case GREATER: return 1;
    case EQUAL:   return 0;
    default:      return -1;
    }
}
