/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_eq_solver

Abstract:

    Solver-agnostic equality solving routines for sequences

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-01

--*/

#include "ast/rewriter/seq_eq_solver.h"
#include "ast/bv_decl_plugin.h"

namespace seq {

    bool eq_solver::reduce(expr* s, expr* t, eq_ptr& r) {
        expr_ref_vector ls(m), rs(m);
        ls.push_back(s);
        rs.push_back(t);
        eqr e(ls, rs);
        return reduce(e, r);
    }

    bool eq_solver::reduce(eqr const& e, eq_ptr& r) {
        r = nullptr;
        if (reduce_unit(e, r))
            return true;
        if (reduce_itos1(e, r))
            return true;
        if (reduce_itos2(e, r))
            return true;
        if (reduce_itos3(e, r))
            return true;
        if (reduce_ubv2s1(e, r))
            return true;
        if (reduce_ubv2s2(e, r))
            return true;
        if (reduce_binary_eq(e, r))
            return true;
        if (reduce_nth_solved(e, r))
            return true;

        return false;
    }


    bool eq_solver::branch(unsigned priority, eqr const& e) {
        switch (priority) {
        case 0:
            return branch_unit_variable(e);
        case 1:
        default:
            break;
        }
        return false;
    }

    void eq_solver::set_conflict() {
        m_clause.reset();
        ctx.add_consequence(true, m_clause);
    }

    void eq_solver::add_consequence(expr_ref const& a) {
        m_clause.reset();
        m_clause.push_back(a);
        ctx.add_consequence(true, m_clause);
    }

    void eq_solver::add_consequence(expr_ref const& a, expr_ref const& b) {
        m_clause.reset();
        m_clause.push_back(a);
        m_clause.push_back(b);
        ctx.add_consequence(true, m_clause);
    }

    /**
     * from_int(s) == from_int(t)
     * --------------------------
     * s = t or (s < 0 and t < 0)
     */

    bool eq_solver::match_itos1(eqr const& e, expr*& a, expr*& b) {
        return
            e.ls.size() == 1 && e.rs.size() == 1 &&
            seq.str.is_itos(e.ls[0], a) && seq.str.is_itos(e.rs[0], b);
    }

    bool eq_solver::reduce_itos1(eqr const& e, eq_ptr& r) {
        expr* s = nullptr, * t = nullptr;
        if (!match_itos1(e, s, t))
            return false;
        expr_ref eq = mk_eq(s, t);
        add_consequence(eq, mk_le(s, -1));
        add_consequence(eq, mk_le(t, -1));
        return true;
    }

    /**
     * from_int(s) == ""
     * -----------------
     *       s < 0
     */

    bool eq_solver::match_itos2(eqr const& e, expr*& s) {
        if (e.ls.size() == 1 && e.rs.empty() && seq.str.is_itos(e.ls[0], s))
            return true;
        if (e.rs.size() == 1 && e.ls.empty() && seq.str.is_itos(e.rs[0], s))
            return true;
        return false;
    }

    bool eq_solver::reduce_itos2(eqr const& e, eq_ptr& r) {
        expr* s = nullptr;
        if (!match_itos2(e, s))
            return false;
        add_consequence(mk_le(s, -1));
        return true;
    }

    /**
    *       itos(n) = ""
    *       ------------
    *          n <= -1
    *
    *          itos(n) = [d1]+[d2]+...+[dk]
    *       ---------------------------------
    *           n = 10^{k-1}*d1 + ... + dk
    *
    *           k > 1 => d1 > 0
    */

    bool eq_solver::match_itos3(eqr const& e, expr*& n, expr_ref_vector const*& es) {
        if (e.ls.size() == 1 && seq.str.is_itos(e.ls[0], n)) {
            es = &e.rs;
            return true;
        }
        if (e.rs.size() == 1 && seq.str.is_itos(e.rs[0], n)) {
            es = &e.ls;
            return true;
        }
        return false;
    }

    bool eq_solver::reduce_itos3(eqr const& e, eq_ptr& r) {
        expr* n = nullptr;
        expr_ref_vector const* _es = nullptr;
        if (!match_itos3(e, n, _es))
            return false;

        expr_ref_vector const& es = *_es;

        if (es.empty()) {
            add_consequence(m_ax.mk_le(n, -1));
            return true;
        }
        expr* u = nullptr;
        for (expr* r : es) {
            if (seq.str.is_unit(r, u)) {
                expr_ref is_digit = m_ax.is_digit(u);
                if (!m.is_true(ctx.expr2rep(is_digit)))
                    add_consequence(is_digit);
            }
        }
        if (!all_units(es, 0, es.size()))
            return false;

        expr_ref num(m);
        for (expr* r : es) {
            VERIFY(seq.str.is_unit(r, u));
            expr_ref digit = m_ax.sk().mk_digit2int(u);
            if (!num)
                num = digit;
            else
                num = a.mk_add(a.mk_mul(a.mk_int(10), num), digit);
        }

        expr_ref eq(m.mk_eq(n, num), m);
        m_ax.rewrite(eq);
        add_consequence(eq);
        if (es.size() > 1) {
            VERIFY(seq.str.is_unit(es[0], u));
            expr_ref digit = m_ax.sk().mk_digit2int(u);
            add_consequence(m_ax.mk_ge(digit, 1));
        }
	    expr_ref y(seq.str.mk_concat(es, es[0]->get_sort()), m);
	    ctx.add_solution(seq.str.mk_itos(n), y);
        return true;
    }

    /**
     *    x = t, where x does not occur in t.
     */
    bool eq_solver::reduce_unit(eqr const& e, eq_ptr& r) {
        if (e.ls == e.rs)
            return true;
        if (e.ls.size() == 1 && is_var(e.ls[0]) && !occurs(e.ls[0], e.rs)) {
            expr_ref y(seq.str.mk_concat(e.rs, e.ls[0]->get_sort()), m);
            ctx.add_solution(e.ls[0], y);
            return true;
        }
        if (e.rs.size() == 1 && is_var(e.rs[0]) && !occurs(e.rs[0], e.ls)) {
            expr_ref y(seq.str.mk_concat(e.ls, e.rs[0]->get_sort()), m);
            ctx.add_solution(e.rs[0], y);
            return true;
        }
        return false;
    }



    /**
     * from_ubv(s) == from_ubv(t)
     * --------------------------
     * s = t
     */

    bool eq_solver::match_ubv2s1(eqr const& e, expr*& a, expr*& b) {
        return
            e.ls.size() == 1 && e.rs.size() == 1 &&
            seq.str.is_ubv2s(e.ls[0], a) && seq.str.is_ubv2s(e.rs[0], b);
        return false;
    }

    bool eq_solver::reduce_ubv2s1(eqr const& e, eq_ptr& r) {
        expr* s = nullptr, * t = nullptr;
        if (!match_ubv2s1(e, s, t))
            return false;
        expr_ref eq = mk_eq(s, t);
        add_consequence(eq);
        return true;        
    }

    /**
    *
    *          bv2s(n) = [d1]+[d2]+...+[dk]
    *       ---------------------------------
    *           n = 10^{k-1}*d1 + ... + dk
    *
    *           k > 1 => d1 > 0
    */
    bool eq_solver::match_ubv2s2(eqr const& e, expr*& n, expr_ref_vector const*& es) {
        if (e.ls.size() == 1 && seq.str.is_ubv2s(e.ls[0], n)) {
            es = &e.rs;
            return true;
        }
        if (e.rs.size() == 1 && seq.str.is_ubv2s(e.rs[0], n)) {
            es = &e.ls;
            return true;
        }
        return false;
    }

    bool eq_solver::reduce_ubv2s2(eqr const& e, eq_ptr& r) {
        expr* n = nullptr;
        expr_ref_vector const* _es = nullptr;
        if (!match_ubv2s2(e, n, _es))
            return false;

        expr_ref_vector const& es = *_es;
        if (es.empty()) {
            set_conflict();
            return true;
        }
        expr* u = nullptr;
        for (expr* r : es) {
            if (seq.str.is_unit(r, u)) {
                expr_ref is_digit = m_ax.is_digit(u);
                if (!m.is_true(ctx.expr2rep(is_digit)))
                    add_consequence(is_digit);
            }
        }
        if (!all_units(es, 0, es.size()))
            return false;

        expr_ref num(m);
        bv_util bv(m);
        sort* bv_sort = n->get_sort();
        unsigned sz = bv.get_bv_size(n);
        if (es.size() > (sz + log2(10)-1)/log2(10)) {
            set_conflict();
            return true;
        }

        for (expr* r : es) {
            VERIFY(seq.str.is_unit(r, u));
            expr_ref digit = m_ax.sk().mk_digit2bv(u, bv_sort);
            if (!num)
                num = digit;
            else
                num = bv.mk_bv_add(bv.mk_bv_mul(bv.mk_numeral(10, sz), num), digit);
        }

        expr_ref eq(m.mk_eq(n, num), m);
        m_ax.rewrite(eq);
        add_consequence(eq);
        if (es.size() > 1) {
            VERIFY(seq.str.is_unit(es[0], u));
            expr_ref digit = m_ax.sk().mk_digit2bv(u, bv_sort);
            expr_ref eq0(m.mk_eq(digit, bv.mk_numeral(0, sz)), m);
            expr_ref neq0(m.mk_not(eq0), m);
            add_consequence(neq0);
        }
        expr_ref y(seq.str.mk_concat(es, es[0]->get_sort()), m);
        ctx.add_solution(seq.str.mk_ubv2s(n), y);
        return true;     
    }


    /**
     * Equation is of the form x ++ xs = ys ++ x
     * where |xs| = |ys| are units of same length
     * then xs is a wrap-around of ys
     * x ++ ab = ba ++ x
     *
     * When it is of the form x ++ a = b ++ x
     * Infer that a = b
     * It is also the case that x is a repetition of a's
     * But this information is not exposed with this inference.
     *
     */
    bool eq_solver::reduce_binary_eq(eqr const& e, eq_ptr& r) {
        ptr_vector<expr> xs, ys;
        expr_ref x(m), y(m);
        if (!match_binary_eq(e, x, xs, ys, y))
            return false;

        if (xs.size() != ys.size()) {
            set_conflict();
            return true;
        }
        if (xs.empty())
            return true;

        if (xs.size() != 1)
            return false;

        if (ctx.expr2rep(xs[0]) == ctx.expr2rep(ys[0]))
            return false;
        expr_ref eq(m.mk_eq(xs[0], ys[0]), m);
        expr* veq = ctx.expr2rep(eq);
        if (m.is_true(veq))
            return false;
        add_consequence(eq);
        return m.is_false(veq);
    }

    /**
    *   x = nth(unit(x, 0)) ++ ... ++ nth(unit(x,i))
    * ------------------------------------------------
    *   x -> nth(unit(x, 0)) ++ ... ++ nth(unit(x,i))
    */

    bool eq_solver::reduce_nth_solved(eqr const& e, eq_ptr& r) {
        expr_ref x(m), y(m);
        if (match_nth_solved(e, x, y)) {
            ctx.add_solution(x, y);
            return true;
        }
        return false;
    }

    bool eq_solver::match_nth_solved(eqr const& e, expr_ref& x, expr_ref& y) {
        if (match_nth_solved_aux(e.ls, e.rs, x, y))
            return true;
        if (match_nth_solved_aux(e.rs, e.ls, x, y))
            return true;
        return false;
    }

    bool eq_solver::match_nth_solved_aux(expr_ref_vector const& ls, expr_ref_vector const& rs, expr_ref& x, expr_ref& y) {
        if (ls.size() != 1 || !is_var(ls[0]))
            return false;
        expr* n = nullptr, * u = nullptr;
        unsigned j = 0, i = 0;
        for (expr* r : rs) {
            if (seq.str.is_unit(r, u) && seq.str.is_nth_i(u, n, i) && i == j && n == ls[0])
                ++j;
            else
                return false;
        }
        x = ls[0];
        y = seq.str.mk_concat(rs, x->get_sort());
        return true;
    }

    /**
    *  XV == abcdef, where V is an arbitrary string
    * ---------------------------------------------
    *          |X| <= |abcdef|
    * 
    *     |X| = k => X = a_1...a_k
    */

    bool eq_solver::branch_unit_variable(expr* X, expr_ref_vector const& units) {
        SASSERT(is_var(X));
        rational lenX;
        ctx.get_length(X, lenX);

        if (lenX > units.size()) {
            add_consequence(m_ax.mk_le(seq.str.mk_length(X), units.size()));
            return true;
        }

        expr_ref eq_length(m.mk_eq(a.mk_int(lenX), seq.str.mk_length(X)), m);
        expr* val = ctx.expr2rep(eq_length);
        if (!m.is_false(val)) {
            expr_ref Y(seq.str.mk_concat(lenX.get_unsigned(), units.data(), X->get_sort()), m);
            expr_ref eq = m_ax.sk().mk_eq(X, Y);
            add_consequence(~eq_length, eq);
            return true;
        }     
        return false;
    }

    bool eq_solver::branch_unit_variable(eqr const& e) {
        if (!e.ls.empty() && is_var(e.ls[0]) && all_units(e.rs, 0, e.rs.size()))
            return branch_unit_variable(e.ls[0], e.rs);
        if (!e.rs.empty() && is_var(e.rs[0]) && all_units(e.ls, 0, e.ls.size()))
            return branch_unit_variable(e.rs[0], e.ls);
        return false;
    }


    bool eq_solver::is_var(expr* a) const {
        return
            seq.is_seq(a) &&
            !seq.str.is_concat(a) &&
            !seq.str.is_empty(a) &&
            !seq.str.is_string(a) &&
            !seq.str.is_unit(a) &&
            !seq.str.is_itos(a) &&
            !seq.str.is_nth_i(a) &&
            !m.is_ite(a);
    }

    bool eq_solver::occurs(expr* a, expr_ref_vector const& b) {
        for (auto const& elem : b)
            if (a == elem || m.is_ite(elem))
                return true;
        return false;
    }

    bool eq_solver::occurs(expr* a, expr* b) {
        // true if a occurs under an interpreted function or under left/right selector.
        SASSERT(is_var(a));
        SASSERT(m_todo.empty());
        expr* e1 = nullptr, * e2 = nullptr;
        m_todo.push_back(b);
        while (!m_todo.empty()) {
            b = m_todo.back();
            if (a == b || m.is_ite(b)) {
                m_todo.reset();
                return true;
            }
            m_todo.pop_back();
            if (seq.str.is_concat(b, e1, e2)) {
                m_todo.push_back(e1);
                m_todo.push_back(e2);
            }
            else if (seq.str.is_unit(b, e1)) {
                m_todo.push_back(e1);
            }
            else if (seq.str.is_nth_i(b, e1, e2)) {
                m_todo.push_back(e1);
            }
        }
        return false;
    }

    void eq_solver::set_prefix(expr_ref& x, expr_ref_vector const& xs, unsigned sz) const {
        SASSERT(0 < xs.size() && sz <= xs.size());
        x = seq.str.mk_concat(sz, xs.data(), xs[0]->get_sort());
    }

    void eq_solver::set_suffix(expr_ref& x, expr_ref_vector const& xs, unsigned sz) const {
        SASSERT(0 < xs.size() && sz <= xs.size());
        x = seq.str.mk_concat(sz, xs.data() + xs.size() - sz, xs[0]->get_sort());
    }

    unsigned eq_solver::count_units_l2r(expr_ref_vector const& es, unsigned offset) const {
        unsigned i = offset, sz = es.size();
        for (; i < sz && seq.str.is_unit(es[i]); ++i);
        return i - offset;
    }

    unsigned eq_solver::count_units_r2l(expr_ref_vector const& es, unsigned offset) const {
        SASSERT(offset < es.size());
        unsigned i = offset, count = 0;
        do {
            if (!seq.str.is_unit(es[i]))
                break;
            ++count;
        } while (i-- > 0);
        return count;
    }

    unsigned eq_solver::count_non_units_l2r(expr_ref_vector const& es, unsigned offset) const {
        unsigned i = offset, sz = es.size();
        for (; i < sz && !seq.str.is_unit(es[i]); ++i);
        return i - offset;
    }

    unsigned eq_solver::count_non_units_r2l(expr_ref_vector const& es, unsigned offset) const {
        SASSERT(offset < es.size());
        unsigned i = offset, count = 0;
        do {
            if (seq.str.is_unit(es[i]))
                break;
            ++count;
        } while (i-- > 0);
        return count;
    }

    /**
     * match: .. X abc  = Y .. Z def U
     * where U is a variable or concatenation of variables
     */

    bool eq_solver::match_ternary_eq_r(expr_ref_vector const& ls, expr_ref_vector const& rs,
        expr_ref& x, expr_ref_vector& xs, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2) {
        if (ls.size() > 1 && rs.size() > 1 && is_var(rs[0]) && is_var(rs.back())) {
            unsigned num_ls_units = count_units_r2l(ls, ls.size() - 1);
            if (num_ls_units == 0 || num_ls_units == ls.size())
                return false;
            unsigned num_rs_non_units = count_non_units_r2l(rs, rs.size() - 1);
            if (num_rs_non_units == rs.size())
                return false;
            SASSERT(num_rs_non_units > 0);
            unsigned num_rs_units = count_units_r2l(rs, rs.size() - 1 - num_rs_non_units);
            if (num_rs_units == 0)
                return false;
            set_prefix(x, ls, ls.size() - num_ls_units);
            set_suffix(xs, ls, num_ls_units);
            unsigned offset = rs.size() - num_rs_non_units - num_rs_units;
            set_prefix(y1, rs, offset);
            set_extract(ys, rs, offset, num_rs_units);
            set_suffix(y2, rs, num_rs_non_units);
            return true;
        }
        return false;
    }

    bool eq_solver::match_ternary_eq_rhs(expr_ref_vector const& ls, expr_ref_vector const& rs,
        expr_ref& x, expr_ref_vector& xs, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2) {
        if (match_ternary_eq_r(ls, rs, x, xs, y1, ys, y2))
            return true;
        if (match_ternary_eq_r(rs, ls, x, xs, y1, ys, y2))
            return true;
        return false;
    }

    /*
      match: abc X ..  = Y def Z ..
         where Y is a variable or concatenation of variables
    */

    bool eq_solver::match_ternary_eq_l(expr_ref_vector const& ls, expr_ref_vector const& rs,
        expr_ref_vector& xs, expr_ref& x, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2) {
        if (ls.size() > 1 && rs.size() > 1 && is_var(rs[0]) && is_var(rs.back())) {
            unsigned num_ls_units = count_units_l2r(ls, 0);
            if (num_ls_units == 0 || num_ls_units == ls.size())
                return false;
            unsigned num_rs_non_units = count_non_units_l2r(rs, 0);
            if (num_rs_non_units == rs.size() || num_rs_non_units == 0)
                return false;
            unsigned num_rs_units = count_units_l2r(rs, num_rs_non_units);
            if (num_rs_units == 0)
                return false;
            set_prefix(xs, ls, num_ls_units);
            set_suffix(x, ls, ls.size() - num_ls_units);
            set_prefix(y1, rs, num_rs_non_units);
            set_extract(ys, rs, num_rs_non_units, num_rs_units);
            set_suffix(y2, rs, rs.size() - num_rs_non_units - num_rs_units);
            return true;
        }
        return false;
    }

    bool eq_solver::match_ternary_eq_lhs(expr_ref_vector const& ls, expr_ref_vector const& rs,
        expr_ref_vector& xs, expr_ref& x, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2) {
        if (match_ternary_eq_l(ls, rs, xs, x, y1, ys, y2))
            return true;
        if (match_ternary_eq_l(rs, ls, xs, x, y1, ys, y2))
            return true;
        return false;
    }


    bool eq_solver::all_units(expr_ref_vector const& es, unsigned start, unsigned end) const {
        for (unsigned i = start; i < end; ++i)
            if (!seq.str.is_unit(es[i]))
                return false;
        return true;
    }

    /**
       match X abc = defg Y, for abc, defg non-empty
    */

    bool eq_solver::match_binary_eq(expr_ref_vector const& ls, expr_ref_vector const& rs,
        expr_ref& x, ptr_vector<expr>& xs, ptr_vector<expr>& ys, expr_ref& y) {
        if (ls.size() > 1 && is_var(ls[0]) &&
            rs.size() > 1 && is_var(rs.back()) &&
            all_units(ls, 1, ls.size()) &&
            all_units(rs, 0, rs.size() - 1)) {
            x = ls[0];
            y = rs.back();
            set_suffix(xs, ls, ls.size() - 1);
            set_prefix(ys, rs, rs.size() - 1);
            return true;
        }
        return false;
    }

    bool eq_solver::match_binary_eq(eqr const& e, expr_ref& x, ptr_vector<expr>& xs, ptr_vector<expr>& ys, expr_ref& y) {
        if (match_binary_eq(e.ls, e.rs, x, xs, ys, y) && x == y)
            return true;
        if (match_binary_eq(e.rs, e.ls, x, xs, ys, y) && x == y)
            return true;
        return false;
    }

    /**
     * match: X abc Y..Y' = Z def T..T', where X,Z are variables or concatenation of variables
     */

    bool eq_solver::match_quat_eq(expr_ref_vector const& ls, expr_ref_vector const& rs,
        expr_ref& x1, expr_ref_vector& xs, expr_ref& x2,
        expr_ref& y1, expr_ref_vector& ys, expr_ref& y2) {
        if (ls.size() > 1 && is_var(ls[0]) && is_var(ls.back()) &&
            rs.size() > 1 && is_var(rs[0]) && is_var(rs.back())) {
            unsigned ls_non_unit = count_non_units_l2r(ls, 0);
            unsigned rs_non_unit = count_non_units_l2r(rs, 0);
            if (ls_non_unit == ls.size())
                return false;
            if (rs_non_unit == rs.size())
                return false;
            unsigned ls_unit = count_units_l2r(ls, ls_non_unit);
            unsigned rs_unit = count_units_l2r(rs, rs_non_unit);
            if (ls_unit == 0)
                return false;
            if (rs_unit == 0)
                return false;
            set_prefix(x1, ls, ls_non_unit);
            set_extract(xs, ls, ls_non_unit, ls_unit);
            set_suffix(x2, ls, ls.size() - ls_non_unit - ls_unit);
            set_prefix(y1, rs, rs_non_unit);
            set_extract(ys, rs, rs_non_unit, rs_unit);
            set_suffix(y2, rs, rs.size() - rs_non_unit - rs_unit);
            return true;
        }
        return false;
    }


    // exists x, y, rs' != empty s.t.  (ls = x ++ rs ++ y) || (ls = rs' ++ y && rs = x ++ rs')
    bool eq_solver::can_align_from_lhs_aux(expr_ref_vector const& ls, expr_ref_vector const& rs) {
        SASSERT(!ls.empty() && !rs.empty());

        for (unsigned i = 0; i < ls.size(); ++i) {
            if (m.are_distinct(ls[i], rs.back()))
                continue;
            
            if (i == 0)
                return true;
            // ls = rs' ++ y && rs = x ++ rs', diff = |x|
            bool same = true;
            if (rs.size() > i) {
                unsigned diff = rs.size() - (i + 1);
                for (unsigned j = 0; same && j < i; ++j) 
                    same = !m.are_distinct(ls[j], rs[diff + j]);                               
            }
            // ls = x ++ rs ++ y, diff = |x|
            else {
                unsigned diff = (i + 1) - rs.size();
                for (unsigned j = 0; same && j + 1 < rs.size(); ++j) 
                    same = !m.are_distinct(ls[diff + j], rs[j]);                              
            }
            if (same)
                return true;
        }
        return false;
    }

    // exists x, y, rs' != empty s.t.  (ls = x ++ rs ++ y) || (ls = x ++ rs' && rs = rs' ++ y)
    bool eq_solver::can_align_from_rhs_aux(expr_ref_vector const& ls, expr_ref_vector const& rs) {
        SASSERT(!ls.empty() && !rs.empty());

        for (unsigned i = 0; i < ls.size(); ++i) {
            unsigned diff = ls.size() - 1 - i;
            if (m.are_distinct(ls[diff], rs[0]))
                continue;
            
            if (i == 0) 
                return true;
            
            bool same = true;
            // ls = x ++ rs' && rs = rs' ++ y, diff = |x|
            if (rs.size() > i) {
                for (unsigned j = 1; same && j <= i; ++j) 
                    same = !m.are_distinct(ls[diff + j], rs[j]);                
            }
            // ls = x ++ rs ++ y, diff = |x|
            else {
                for (unsigned j = 1; same && j < rs.size(); ++j)
                    same = !m.are_distinct(ls[diff + j], rs[j]);
            }
            if (same)
                return true;
        }
        return false;
    }




};

