/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    kbo.cpp

Abstract:

    Knuth-Bendix ordering.

Author:

    Leonardo de Moura (leonardo) 2008-01-28.

Revision History:

--*/
#include"kbo.h"
#include"ast_pp.h"

inline unsigned kbo::f_weight(func_decl * f) const {
    // TODO
    return 1;
}

inline unsigned kbo::var_weight() const {
    return m_var_weight;
}

inline void kbo::reset() {
    m_weight_balance = 0;
    m_deltas.reset();
    m_num_pos = 0;
    m_num_neg = 0;
}

/**
   \brief Increase the balance of the given variable.
*/
inline void kbo::inc(expr_offset v) {
    SASSERT(is_var(v.get_expr()));
    int val;
    unsigned v_idx  = to_var(v.get_expr())->get_idx();
    unsigned offset = v.get_offset();
    if (m_deltas.find(v_idx, offset, val)) {
        if (val == -1) 
            m_num_neg--;
        else if (val == 0)
            m_num_pos++;
        m_deltas.insert(v_idx, offset, val + 1);
    }
    else {
        m_deltas.insert(v_idx, offset, 1);
        m_num_pos ++;
    }
}

/**
   \brief Decreate the balance of the given variable.
*/
inline void kbo::dec(expr_offset v) {
    int val;
    unsigned v_idx  = to_var(v.get_expr())->get_idx();
    unsigned offset = v.get_offset();
    if (m_deltas.find(v_idx, offset, val)) {
        if (val == 0) 
            m_num_neg++;
        else if (val == 1)
            m_num_pos--;
        m_deltas.insert(v_idx, offset, val - 1);
    }
    else {
        m_deltas.insert(v_idx, offset, -1);
        m_num_neg ++;
    }
}

/**
   \brief Accumulate the variables and weight balance of t. Return
   true if t contains target_var.
*/
template<bool pos>
bool kbo::VWBc(expr_offset t, expr_offset target_var) {
    SASSERT(target_var.get_expr() == 0 || is_var(target_var.get_expr()));
    svector<expr_offset> & todo = m_vwbc_todo;
    expr_offset s;
    bool found = false;
    unsigned j;
    SASSERT(todo.empty());
    todo.push_back(t);
    while (!todo.empty()) {
        t        = todo.back();
        if (t == target_var)
            found = true;
        expr * n        = t.get_expr();
        unsigned offset = t.get_offset();
        todo.pop_back();
        switch (n->get_kind()) {
        case AST_VAR:
            if (m_subst && m_subst->find(to_var(n), offset, s))
                todo.push_back(s);
            else if (pos) {
                inc(t);
                m_weight_balance += var_weight();
            }
            else {
                dec(t);
                m_weight_balance -= var_weight();
            }
            break;
        case AST_APP:
            if (pos)
                m_weight_balance += f_weight(to_app(n)->get_decl());
            else
                m_weight_balance -= f_weight(to_app(n)->get_decl());
            j = to_app(n)->get_num_args();
            while (j > 0) {
                --j;
                todo.push_back(expr_offset(to_app(n)->get_arg(j), offset));
            }
            break;
        default:
            UNREACHABLE();
            break;
        }
    }
    return found;
}

template<bool pos>
inline void kbo::VWB(expr_offset t, unsigned idx) {
    expr_offset null(0, 0);
    app * n = to_app(t.get_expr());
    unsigned num = n->get_num_args();
    for (; idx < num; idx++)
        VWBc<pos>(expr_offset(n->get_arg(idx), t.get_offset()), null);
}

inline bool is_unary_app(expr * n) {
    return is_app(n) && to_app(n)->get_num_args() == 1;
}

inline kbo::result kbo::no_neg() const {
    return m_num_neg == 0 ? GREATER : UNCOMPARABLE;
}

inline kbo::result kbo::no_pos() const {
    return m_num_pos == 0 ? LESSER : UNCOMPARABLE;
}

order::result kbo::compare(expr_offset const & t1, expr_offset const & t2, substitution * s) {
    reset();
    m_subst = s;

    if (t1 == t2) 
        return EQUAL;

    expr * n1 = t1.get_expr();
    expr * n2 = t2.get_expr();

    // f(s) >_{kbo} f(t) iff s >_{kbo} t
    while (is_unary_app(n1) && is_unary_app(n2) && to_app(n1)->get_decl() == to_app(n2)->get_decl()) {
        n1 = to_app(n1)->get_arg(0);
        n2 = to_app(n2)->get_arg(0);
    }

    svector<entry> & todo = m_compare_todo;
    SASSERT(todo.empty());
    todo.push_back(entry(find(expr_offset(n1, t1.get_offset())),
                         find(expr_offset(n2, t2.get_offset())),
                         0));

    result res = UNKNOWN;

    while (!todo.empty()) {
        entry & e = todo.back();
        expr_offset t1 = e.m_t1;
        expr_offset t2 = e.m_t2;
        expr * n1 = t1.get_expr();
        expr * n2 = t2.get_expr();
        TRACE("kbo", tout << "processing with idx: " << e.m_idx << "\n" << 
              mk_pp(n1, m_manager) << "\n" << mk_pp(n2, m_manager) << "\n";
              tout << "wb : " << m_weight_balance << "\n";);
        SASSERT(!is_quantifier(n1) && !is_quantifier(n2));
        bool v1 = is_var(n1);
        bool v2 = is_var(n2);
        if (v1 && v2) {
            todo.pop_back();
            inc(t1);
            dec(t2);
            res = t1 == t2 ? EQUAL : UNCOMPARABLE;
        }
        else if (v1) {
            todo.pop_back();
            res = VWBc<false>(t2, t1) ? LESSER : UNCOMPARABLE;
            inc(t1);
            m_weight_balance += var_weight();
        }
        else if (v2) {
            todo.pop_back();
            res = VWBc<true>(t1, t2) ? GREATER : UNCOMPARABLE;
            dec(t2);
            m_weight_balance -= var_weight();
        }
        else {
            func_decl * f = to_app(n1)->get_decl();
            func_decl * g = to_app(n2)->get_decl();
            result lex;
            if (f != g || to_app(n1)->get_num_args() != to_app(n2)->get_num_args()) {
                VWB<true>(t1, 0);
                VWB<false>(t2, 0);
                lex = UNCOMPARABLE;
            }
            else {
                unsigned & idx = e.m_idx;
                // when idx > 0, res contains the result for child (idx - 1)
                if (idx > 0 && res != EQUAL) {
                    VWB<true>(t1, idx);
                    VWB<false>(t2, idx);
                    lex = res;
                }
                else if (idx == to_app(n1)->get_num_args()) {
                    // all children were visited
                    lex = EQUAL;
                }
                else if (idx < to_app(n1)->get_num_args()) {
                    expr_offset c1 = find(expr_offset(to_app(n1)->get_arg(idx), t1.get_offset()));
                    expr_offset c2 = find(expr_offset(to_app(n2)->get_arg(idx), t2.get_offset()));
                    idx++; // move curr entry child idx
                    entry new_entry(c1, c2, 0);
                    todo.push_back(new_entry);
                    continue; // process child before continuing
                }
            }
            
            todo.pop_back();
            m_weight_balance += f_weight(f);
            m_weight_balance -= f_weight(g);

            if (m_weight_balance > 0)
                res = no_neg();
            else if (m_weight_balance < 0)
                res = no_pos();
            else if (f_greater(f, g))
                res = no_neg();
            else if (f_greater(g, f))
                res = no_pos();
            else if (f != g)
                res = UNCOMPARABLE;
            else if (lex == EQUAL)
                res = EQUAL;
            else if (lex == GREATER)
                res = no_neg();
            else if (lex == LESSER)
                res = no_pos();
            else
                res = UNCOMPARABLE;
        }
        TRACE("kbo", tout << "result: " << res << "\n";);
    }

    return res;
}

bool kbo::greater(expr_offset const & t1, expr_offset const & t2, substitution * s) {
    return compare(t1, t2, s) == GREATER;
}

int kbo::compare_ge(expr_offset const & t1, expr_offset const & t2, substitution * s) {
    switch (compare(t1, t2, s)) {
    case GREATER: return 1;
    case EQUAL:   return 0;
    default: return -1;
    }
}
