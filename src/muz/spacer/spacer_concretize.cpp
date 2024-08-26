/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_concretize.cpp

Abstract:

  Concretize a pob

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/
#include "spacer_concretize.h"

namespace pattern_var_marker_ns {
struct proc {
    arith_util &m_arith;
    expr_fast_mark2 &m_marks;
    proc(arith_util &arith, expr_fast_mark2 &marks)
        : m_arith(arith), m_marks(marks) {}
    void operator()(var *n) const {}
    void operator()(quantifier *q) const {}
    void operator()(app const *n) const {
        expr *e1 = nullptr, *e2 = nullptr;
        if (m_arith.is_mul(n, e1, e2)) {
            if (is_var(e1) && !is_var(e2))
                m_marks.mark(e2);
            else if (is_var(e2) && !is_var(e1))
                m_marks.mark(e1);
        }
    }
};
}; // namespace pattern_var_marker_ns
namespace spacer {
void pob_concretizer::mark_pattern_vars() {
    pattern_var_marker_ns::proc proc(m_arith, m_var_marks);
    quick_for_each_expr(proc, const_cast<expr *>(m_pattern));
}

bool pob_concretizer::push_out(expr_ref_vector &out, const expr_ref &e) {
    // using m_var_marks to mark both variables and expressions sent to out
    // the two sets are distinct so we can reuse the same marks
    if (!m_var_marks.is_marked(e)) {
        m_var_marks.mark(e);
        out.push_back(e);
        return true;
    }
    return false;
}

bool pob_concretizer::apply(const expr_ref_vector &cube, expr_ref_vector &out) {
    // mark variables that are being split out
    mark_pattern_vars();

    for (auto *lit : cube) {
        if (!apply_lit(lit, out)) {
            out.reset();
            m_var_marks.reset();
            return false;
        }
    }

    m_var_marks.reset();
    return true;
}

bool pob_concretizer::is_split_var(expr *e, expr *&var, bool &pos) {
    expr *e1 = nullptr, *e2 = nullptr;
    rational n;

    if (m_var_marks.is_marked(e)) {
        var = e;
        pos = true;
        return true;
    } else if (m_arith.is_mul(e, e1, e2) && m_arith.is_numeral(e1, n) &&
               m_var_marks.is_marked(e2)) {
        var = e2;
        pos = !n.is_neg();
        return true;
    }

    return false;
}

void pob_concretizer::split_lit_le_lt(expr *_lit, expr_ref_vector &out) {
    expr *e1 = nullptr, *e2 = nullptr;

    expr *lit = _lit;
    m.is_not(_lit, lit);
    VERIFY(m_arith.is_le(lit, e1, e2) || m_arith.is_gt(lit, e1, e2) ||
           m_arith.is_lt(lit, e1, e2) || m_arith.is_ge(lit, e1, e2));

    ptr_buffer<expr> kids;
    expr *var;
    bool pos;
    expr_ref val(m);
    for (auto *arg : *to_app(e1)) {
        if (is_split_var(arg, var, pos)) {
            val = m_model->operator()(var);

            // reuse val to keep the new literal
            val = pos ? m_arith.mk_le(var, val) : m_arith.mk_ge(var, val);
            push_out(out, val);
        } else {
            kids.push_back(arg);
        }
    }

    if (kids.empty()) return;

    // -- nothing was changed in the literal, move it out as is
    if (kids.size() == to_app(e1)->get_num_args()) {
        push_out(out, {_lit, m});
        return;
    }

    // create new leftover literal using remaining arguments
    expr_ref lhs(m);
    if (kids.size() == 1) {
        lhs = kids.get(0);
    } else
        lhs = m_arith.mk_add(kids.size(), kids.data());

    expr_ref rhs = m_model->operator()(lhs);
    expr_ref new_lit(m_arith.mk_le(lhs, rhs), m);
    push_out(out, new_lit);
}

void pob_concretizer::split_lit_ge_gt(expr *_lit, expr_ref_vector &out) {
    expr *e1 = nullptr, *e2 = nullptr;

    expr *lit = _lit;
    m.is_not(_lit, lit);
    VERIFY(m_arith.is_le(lit, e1, e2) || m_arith.is_gt(lit, e1, e2) ||
           m_arith.is_lt(lit, e1, e2) || m_arith.is_ge(lit, e1, e2));

    ptr_buffer<expr> kids;
    expr *var;
    bool pos;
    expr_ref val(m);
    for (auto *arg : *to_app(e1)) {
        if (is_split_var(arg, var, pos)) {
            val = m_model->operator()(var);

            // reuse val to keep the new literal
            val = pos ? m_arith.mk_ge(var, val) : m_arith.mk_le(var, val);
            push_out(out, val);
        } else {
            kids.push_back(arg);
        }
    }

    if (kids.empty()) return;

    // -- nothing was changed in the literal, move it out as is
    if (kids.size() == to_app(e1)->get_num_args()) {
        push_out(out, {_lit, m});
        return;
    }

    // create new leftover literal using remaining arguments
    expr_ref lhs(m);
    if (kids.size() == 1) {
        lhs = kids.get(0);
    } else
        lhs = m_arith.mk_add(kids.size(), kids.data());

    expr_ref rhs = m_model->operator()(lhs);
    expr_ref new_lit(m_arith.mk_ge(lhs, rhs), m);
    push_out(out, new_lit);
}

bool pob_concretizer::apply_lit(expr *_lit, expr_ref_vector &out) {
    expr *lit = _lit;
    bool is_neg = m.is_not(_lit, lit);

    // split literals of the form a1*x1 + ... + an*xn ~ c, where c is a
    // constant, ~ is <, <=, >, or >=, and the top level operator of LHS is +
    expr *e1 = nullptr, *e2 = nullptr;
    if ((m_arith.is_lt(lit, e1, e2) || m_arith.is_le(lit, e1, e2)) &&
        m_arith.is_add(e1)) {
        SASSERT(m_arith.is_numeral(e2));
        if (!is_neg) {
            split_lit_le_lt(_lit, out);
        } else {
            split_lit_ge_gt(_lit, out);
        }
    } else if ((m_arith.is_gt(lit, e1, e2) || m_arith.is_ge(lit, e1, e2)) &&
               m_arith.is_add(e1)) {
        SASSERT(m_arith.is_numeral(e2));
        if (!is_neg) {
            split_lit_ge_gt(_lit, out);
        } else {
            split_lit_le_lt(_lit, out);
        }
    } else {
        out.push_back(_lit);
    }
    return true;
}
} // namespace spacer

