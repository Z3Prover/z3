/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    seq_eq_solver.cpp

Abstract:

    Features from theory_seq that are specific to solving equations.

Author:

    Nikolaj Bjorner (nbjorner) 2015-6-12
    Thai Minh Trinh 2017
*/

#include <typeinfo>
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_trail.h"
#include "ast/for_each_expr.h"
#include "smt/smt_context.h"
#include "smt/theory_seq.h"
#include "smt/theory_arith.h"

using namespace smt;


bool theory_seq::solve_eqs(unsigned i) {
    bool change = false;
    for (; !ctx.inconsistent() && i < m_eqs.size(); ++i) {
        if (solve_eq(i)) {
            m_eqs.erase_and_swap(i--);
            ++m_stats.m_num_reductions;
            change = true;
        }
        TRACE("seq_verbose", display_equations(tout););
    }
    return change || m_new_propagation || ctx.inconsistent();
}

bool theory_seq::solve_eq(unsigned idx) {
    const depeq& e = m_eqs[idx];
    expr_ref_vector& ls = m_ls;
    expr_ref_vector& rs = m_rs;
    m_ls.reset();
    m_rs.reset();
    dependency* dep2 = nullptr;
    bool change = false;
    if (!canonize(e.ls, ls, dep2, change)) return false;
    if (!canonize(e.rs, rs, dep2, change)) return false;
    dependency* deps = m_dm.mk_join(dep2, e.dep());
    TRACE("seq_verbose", 
          tout << e.ls << " = " << e.rs << " ==> ";
          tout << ls << " = " << rs << "\n";
          display_deps(tout, deps););

    if (!ctx.inconsistent() && simplify_eq(ls, rs, deps)) {
        TRACE("seq", tout << "simplified\n";);
        return true;
    }

    if (!ctx.inconsistent() && lift_ite(ls, rs, deps)) {
        return true;
    }
    seq::eq_ptr r;
    m_eq_deps = deps;
    seq::eqr er(ls, rs);
    if (!ctx.inconsistent() && m_eq.reduce(er, r)) {
        if (!r) 
            return true;
        m_eqs.set(idx, depeq(m_eq_id++, r->ls, r->rs, deps));
        return false;
    }

    TRACE("seq_verbose", tout << ls << " = " << rs << "\n";);
    if (!ctx.inconsistent() && solve_nth_eq(ls, rs, deps)) {
        return true;
    }
    if (!ctx.inconsistent() && solve_nth_eq(rs, ls, deps)) {
        return true;
    }
    if (!ctx.inconsistent() && change) {
        // The propagation step from arithmetic state (e.g. length offset) to length constraints
        TRACE("seq", tout << "inserting equality\n";);
        m_eqs.set(idx, depeq(m_eq_id++, ls, rs, deps));        
    }
    return false;
}

void theory_seq::add_consequence(bool uses_eq, expr_ref_vector const& clause) {
    dependency* dep = uses_eq ? m_eq_deps : nullptr;
    m_new_propagation = true;
    if (clause.size() == 1) {
        propagate_lit(dep, 0, nullptr, mk_literal(clause[0]));
        return;
    }
    enode_pair_vector eqs;
    literal_vector lits;
    linearize(dep, eqs, lits);
    for (auto& lit : lits)
        lit.neg();
    for (auto eq : eqs)
        lits.push_back(~mk_eq(eq.first->get_expr(), eq.second->get_expr(), false));
    for (auto f : clause)
        lits.push_back(mk_literal(f));    
    add_axiom(lits);
}

expr* theory_seq::expr2rep(expr* e) { 
    if (m.is_bool(e) && ctx.b_internalized(e)) {
        bool_var b = ctx.get_bool_var(e);
        switch (ctx.get_assignment(b)) {
        case l_true:
            return m.mk_true();
        case l_false:
            return m.mk_false();
        default:
            break;
        }
    }        
    if (!ctx.e_internalized(e))
        return e;
    return ctx.get_enode(e)->get_root()->get_expr();
}

bool theory_seq::has_len_offset(expr_ref_vector const& ls, expr_ref_vector const& rs, int & offset) {

    if (ls.empty() || rs.empty()) 
        return false;
    expr* l_fst = ls[0];
    expr* r_fst = rs[0];
    if (!is_var(l_fst) || !is_var(r_fst)) 
        return false;

    expr_ref len_l_fst = mk_len(l_fst);
    if (!ctx.e_internalized(len_l_fst)) 
        return false;
    enode * root1 = get_root(len_l_fst);

    expr_ref len_r_fst = mk_len(r_fst);
    if (!ctx.e_internalized(len_r_fst))
        return false;
    enode* root2 = get_root(len_r_fst);

    if (root1 == root2) {
        TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst,m) << ")\n";);
        offset = 0;
        return true;
    }

    if (m_offset_eq.find(root1, root2, offset)) {
        TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst,m) << " " << offset << ")\n";);
        return true;
    }
    return false;
}

bool theory_seq::len_based_split() {
    for (auto const& e : m_eqs) 
        if (len_based_split(e)) 
            return true;
    return false;
}

/*
   
   ls = x11 + x12                for len(x11) = len(y11)
   rs = y11 + y12

   ls = x11     + Z + x12        for len(x11) = len(y11) + offset
   rs = y11 + Z + y12

   ls = x11 + Z + x12            for len(x11) = len(y11) - offset
   rs = y11     + Z + y12

   Use last case as sample:

   propagate ls = rs & len(x12 + Z) == len(y11) => x11 + Z == y11
   propagate ls = rs & len(x11 + Z) == len(y11) => x12 == Z + y12
   propagate ls = rs & len(x12 + Z) == len(y11) => len(Z) = offset
   
*/

bool theory_seq::len_based_split(depeq const& e) {
    expr_ref_vector const& ls = e.ls;
    expr_ref_vector const& rs = e.rs;
    
    int offset = 0;
    if (!has_len_offset(ls, rs, offset))
        return false;
        
    TRACE("seq", tout << "split based on length\n";);
    TRACE("seq", display_equation(tout, e););
    sort* srt = ls[0]->get_sort();
    expr_ref x11 = expr_ref(ls[0], m);
    expr_ref x12 = mk_concat(ls.size()-1, ls.data()+1, srt);
    expr_ref y11 = expr_ref(rs[0], m);
    expr_ref y12 = mk_concat(rs.size()-1, rs.data()+1, srt);

    expr_ref lenX11 = mk_len(x11);
    expr_ref lenY11 = mk_len(y11);
    expr_ref Z(m);
    if (offset != 0) {
        lenY11 = m_autil.mk_add(lenY11, m_autil.mk_int(offset));
        if (offset > 0) {
            Z = m_sk.mk_align(y12, x12, x11, y11);
            y11 = mk_concat(y11, Z);
            x12 = mk_concat(Z, x12);
        }
        else {
            offset = -offset;
            Z = m_sk.mk_align(x12, y12, y11, x11);
            x11 = mk_concat(x11, Z);
            y12 = mk_concat(Z, y12);
        }
    }

    dependency* dep = e.dep();
    literal_vector lits;
    literal lit1 = mk_eq(lenX11, lenY11, false);
    if (ctx.get_assignment(lit1) != l_true) {
        return false;
    }
    lits.push_back(lit1);

    if (offset != 0) {
        expr_ref lenZ = mk_len(Z);
        propagate_eq(dep, lits, lenZ, m_autil.mk_int(offset), false);
    }
    propagate_eq(dep, lits, y11, x11, true);
    propagate_eq(dep, lits, x12, y12, false);

    return true;
}

/**
   \brief select branching on variable equality.
   preference mb > eq > ternary > quat
   this performs much better on #1628
*/
bool theory_seq::branch_variable() {
    if (branch_ternary_variable()) {
        TRACE("seq", tout << "branch_ternary_variable\n";);
        return true;
    }
    if (branch_quat_variable()) {
        TRACE("seq", tout << "branch_quat_variable\n";);
        return true;
    }

    bool turn = ctx.get_random_value() % 2 == 0;
    for (unsigned i = 0; i < 2; ++i, turn = !turn) {
        if (turn && branch_variable_mb()) {
            TRACE("seq", tout << "branch_variable_mb\n";);
            return true;
        }
        if (!turn && branch_variable_eq()) {
            TRACE("seq", tout << "branch_variable_eq\n";);
            return true;
        }
    }
    return false;
}

bool theory_seq::branch_variable_mb() {
    bool change = false;
    unsigned sz = m_eqs.size();
    int start = ctx.get_random_value();
    for (unsigned i = 0; i < sz; ++i) {
        unsigned k = (i + start) % sz;
        depeq const& e = m_eqs[k];
        vector<rational> len1, len2;
        if (!is_complex(e)) {
            continue;
        }
        if (e.ls.empty() || e.rs.empty() || 
            (!is_var(e.ls[0]) && !is_var(e.rs[0]))) {
            continue;
        }

        if (!enforce_length(e.ls, len1) || !enforce_length(e.rs, len2)) {
            // change = true;
            continue;
        }
        rational l1, l2;
        for (const auto& elem : len1) l1 += elem;
        for (const auto& elem : len2) l2 += elem;
        if (l1 == l2 && split_lengths(e.dep(), e.ls, e.rs, len1, len2)) {
            TRACE("seq", tout << "split lengths\n";);
            change = true;
            break;
        }

        expr_ref l = mk_concat(e.ls);
        expr_ref r = mk_concat(e.rs);
        expr_ref lnl = mk_len(l), lnr = mk_len(r);
        if (propagate_eq(e.dep(), lnl, lnr, false)) 
            change = true;
    }
    return change;
}


bool theory_seq::is_complex(depeq const& e) {
    unsigned num_vars1 = 0, num_vars2 = 0;
    for (auto const& elem : e.ls) {
        if (is_var(elem)) ++num_vars1;
    }
    for (auto const& elem : e.rs) {
        if (is_var(elem)) ++num_vars2;
    }
    return num_vars1 > 0 && num_vars2 > 0 && num_vars1 + num_vars2 > 2;
}

/*
  \brief Decompose ls = rs into Xa = bYc, such that 
   1. 
    - X != Y
    - |b| <= |X| <= |bY| in current model
    - b is non-empty.
   2. X != Y
    - b is empty
    - |X| <= |Y|
   3. |X| = 0
      - propagate X = empty      
*/
bool theory_seq::split_lengths(dependency* dep,
                               expr_ref_vector const& ls, expr_ref_vector const& rs, 
                               vector<rational> const& ll, vector<rational> const& rl) {
    expr_ref X(m), Y(m), b(m);
    if (ls.empty() || rs.empty()) {
        return false;
    } 
    if (is_var(ls[0]) && ll[0].is_zero()) {
        return set_empty(ls[0]);
    }
    if (is_var(rs[0]) && rl[0].is_zero()) {
        return set_empty(rs[0]);
    }
    if (is_var(rs[0]) && !is_var(ls[0])) {
        return split_lengths(dep, rs, ls, rl, ll);
    }
    if (!is_var(ls[0])) {
        return false;
    }
    X = ls[0];
    rational lenX = ll[0];
    expr_ref_vector bs(m);
    SASSERT(lenX.is_pos());
    rational lenB(0), lenY(0);
    for (unsigned i = 0; lenX > lenB && i < rs.size(); ++i) {
        bs.push_back(rs[i]);
        lenY = rl[i];
        lenB += lenY;
    }
    SASSERT(lenX <= lenB);
    SASSERT(!bs.empty());
    Y = bs.back();
    bs.pop_back();
    if (!is_var(Y) && !m_util.str.is_unit(Y)) {
        TRACE("seq", tout << "TBD: non variable or unit split: " << Y << "\n";);
        return false;
    }
    if (X == Y) {
        TRACE("seq", tout << "Cycle: " << X << "\n";);
        return false;
    }
    if (lenY.is_zero()) {
        return set_empty(Y);
    }
    b = mk_concat(bs, X->get_sort());

    SASSERT(X != Y);

    // |b| < |X| <= |b| + |Y| => x = bY1, Y = Y1Y2
    expr_ref lenXE = mk_len(X);
    expr_ref lenYE = mk_len(Y);
    expr_ref lenb = mk_len(b);
    literal  lit1 = ~m_ax.mk_le(mk_sub(lenXE, lenb), 0);
    literal  lit2 =  m_ax.mk_le(mk_sub(mk_sub(lenXE, lenb), lenYE), 0);
    literal_vector lits;
    lits.push_back(lit1);
    lits.push_back(lit2);
    
    if (ctx.get_assignment(lit1) != l_true ||
        ctx.get_assignment(lit2) != l_true) {
        ctx.mark_as_relevant(lit1);
        ctx.mark_as_relevant(lit2);
    }
    else if (m_util.str.is_unit(Y)) {
        SASSERT(lenB == lenX);
        bs.push_back(Y);
        expr_ref bY = mk_concat(bs, Y->get_sort());
        propagate_eq(dep, lits, X, bY, true);
    }
    else {
        SASSERT(is_var(Y));
        expr_ref Y1 = m_sk.mk_left(X, b, Y);
        expr_ref Y2 = m_sk.mk_right(X, b, Y);
        TRACE("seq", tout << Y1 << "\n" << Y2 << "\n" << ls << "\n" << rs << "\n";);
        expr_ref bY1 = mk_concat(b, Y1);
        expr_ref Y1Y2 = mk_concat(Y1, Y2);
        propagate_eq(dep, lits, X, bY1, true);
        propagate_eq(dep, lits, Y, Y1Y2, true);
    }
    return true;
}


bool theory_seq::branch_binary_variable() {
    for (auto const& e : m_eqs) {
        if (branch_binary_variable(e)) {
            TRACE("seq", display_equation(tout, e););
            return true;
        }
    }
    return false;
}

bool theory_seq::branch_binary_variable(depeq const& e) {
    if (is_complex(e)) {
        return false;
    }
    ptr_vector<expr> xs, ys;
    expr_ref x(m), y(m);
    if (!m_eq.match_binary_eq(e.ls, e.rs, x, xs, ys, y) &&
        !m_eq.match_binary_eq(e.rs, e.ls, x, xs, ys, y))
        return false;
    if (x == y) {
        return false;
    }
        
    // Equation is of the form x ++ xs = ys ++ y
    // where xs, ys are units.
    // x is either a prefix of ys, all of ys ++ y or ys ++ y1, such that y = y1 ++ y2, y2 = xs 
    
    rational lenX, lenY;
    if (branch_variable_eq(e)) {
        return true;
    }
    if (!get_length(x, lenX)) {
        add_length_to_eqc(x);
        return true;
    }
    if (!get_length(y, lenY)) {
        add_length_to_eqc(y);
        return true;
    }
    if (lenX + rational(xs.size()) != lenY + rational(ys.size())) {
        // |x| - |y| = |ys| - |xs|
        expr_ref a(mk_sub(mk_len(x), mk_len(y)), m);
        expr_ref b(m_autil.mk_int(rational(ys.size())-rational(xs.size())), m);
        propagate_lit(e.dep(), 0, nullptr, mk_eq(a, b, false));
        return true;
    }
    if (lenX <= rational(ys.size())) {
        expr_ref_vector Ys(m);
        Ys.append(ys.size(), ys.data());
        m_eq_deps = e.dep();
        if (m_eq.branch_unit_variable(x, Ys))
            return true;
    }
    expr_ref le(m_autil.mk_le(mk_len(x), m_autil.mk_int(ys.size())), m);
    literal lit = mk_literal(le);
    if (l_false == ctx.get_assignment(lit)) {
        // |x| > |ys| => x = ys ++ y1, y = y1 ++ y2, y2 = xs
        expr_ref Y1 = m_sk.mk_left(x, y);
        expr_ref Y2 = m_sk.mk_right(x, y);
        TRACE("seq", tout << Y1 << "\n" << Y2 << "\n";);
        ys.push_back(Y1);
        expr_ref ysY1 = mk_concat(ys);
        expr_ref xsE = mk_concat(xs);
        expr_ref Y1Y2 = mk_concat(Y1, Y2); 
        dependency* dep = e.dep();
        propagate_eq(dep, ~lit, x, ysY1);
        propagate_eq(dep, ~lit, y, Y1Y2);
        propagate_eq(dep, ~lit, Y2, xsE);
    }
    else {
        ctx.mark_as_relevant(lit);
    }
    return true;
}

bool theory_seq::branch_unit_variable() {
    bool result = false;
    for (auto const& e : m_eqs) {
        seq::eqr er(e.ls, e.rs);
        m_eq_deps = e.dep();
        if (m_eq.branch(0, er)) {
            result = true;
            break;
        }
    }
    CTRACE("seq", result, tout << "branch unit variable\n";);
    return result;
}


bool theory_seq::branch_ternary_variable() {
    for (auto const& e : m_eqs) {
        if (branch_ternary_variable_rhs(e) || branch_ternary_variable_lhs(e)) {
            return true;
        }
    }
    return false;
}


// exists x, y, rs' != empty s.t.  (ls = x ++ rs ++ y) || (ls = rs' ++ y && rs = x ++ rs')
bool theory_seq::can_align_from_lhs(expr_ref_vector const& ls, expr_ref_vector const& rs) {
    SASSERT(!ls.empty() && !rs.empty());
    expr_ref l = mk_concat(ls);
    expr_ref r = mk_concat(rs);
    expr_ref pair(m.mk_eq(l,r), m);
    bool result;
    if (!m_overlap_lhs.find(pair, result)) {
        result = m_eq.can_align_from_lhs_aux(ls, rs);
        m_overlap_lhs.insert(pair, result);
    }
    return result;
}

// exists x, y, rs' != empty s.t.  (ls = x ++ rs ++ y) || (ls = x ++ rs' && rs = rs' ++ y)
bool theory_seq::can_align_from_rhs(expr_ref_vector const& ls, expr_ref_vector const& rs) {
    SASSERT(!ls.empty() && !rs.empty());
    expr_ref l = mk_concat(ls);
    expr_ref r = mk_concat(rs);
    expr_ref pair(m.mk_eq(l, r), m);
    bool result;
    if (!m_overlap_rhs.find(pair, result)) {
        result = m_eq.can_align_from_rhs_aux(ls, rs);
        m_overlap_rhs.insert(pair, result);
    }
    return result;
}


// Equation is of the form x ++ xs = y1 ++ ys ++ y2 where xs, ys are units.
// If xs and ys cannot align then
//     x ++ xs = y1 ++ ys ++ y2 => x = y1 ++ ys ++ z, z ++ xs = y2
bool theory_seq::branch_ternary_variable_rhs(depeq const& e) {
    expr_ref_vector xs(m), ys(m);
    expr_ref x(m), y1(m), y2(m);
    if (!m_eq.match_ternary_eq_rhs(e.ls, e.rs, x, xs, y1, ys, y2))
        return false;
    if (m_sk.is_align_l(y1) || m_sk.is_align_r(y1))
        return false;

    rational lenX, lenY1, lenY2;
    if (!get_length(x, lenX)) 
        add_length_to_eqc(x);
    if (!get_length(y1, lenY1)) 
        add_length_to_eqc(y1);
    if (!get_length(y2, lenY2)) 
        add_length_to_eqc(y2);

    SASSERT(!xs.empty() && !ys.empty());
    if (can_align_from_lhs(xs, ys)) 
        return false;
    expr_ref xsE = mk_concat(xs);
    expr_ref ysE = mk_concat(ys);
    expr_ref y1ys = mk_concat(y1, ysE);
    expr_ref Z = m_sk.mk_align_r(xsE, y1, ysE, y2);
    expr_ref ZxsE = mk_concat(Z, xsE);
    expr_ref y1ysZ = mk_concat(y1ys, Z);
    
    dependency* dep = e.dep();
    bool propagated = false;
    if (propagate_lit(dep, 0, nullptr, m_ax.mk_ge(mk_len(y2), xs.size())))
        propagated = true;
    if (propagate_lit(dep, 0, nullptr, m_ax.mk_ge(mk_sub(mk_len(x), mk_len(y1)), ys.size())))
        propagated = true;
    if (propagate_eq(dep, x, y1ysZ, true))
        propagated = true;
    if (propagate_eq(dep, y2, ZxsE, true))
        propagated = true;
    return propagated;
}

// Equation is of the form xs ++ x = y1 ++ ys ++ y2 where xs, ys are units.
// If xs and ys cannot align then
//      xs ++ x = y1 ++ ys ++ y2 => xs ++ z = y1, x = z ++ ys ++ y2
bool theory_seq::branch_ternary_variable_lhs(depeq const& e) {
    expr_ref_vector xs(m), ys(m);
    expr_ref x(m), y1(m), y2(m);
    if (!m_eq.match_ternary_eq_lhs(e.ls, e.rs, xs, x, y1, ys, y2))
        return false;
    if (m_sk.is_align_l(y1) || m_sk.is_align_r(y1))
        return false;

    rational lenX, lenY1, lenY2;
    if (!get_length(x, lenX)) 
        add_length_to_eqc(x);
    if (!get_length(y1, lenY1)) 
        add_length_to_eqc(y1);
    if (!get_length(y2, lenY2)) 
        add_length_to_eqc(y2);
    SASSERT(!xs.empty() && !ys.empty());

    if (can_align_from_rhs(xs, ys)) 
        return false;
    expr_ref xsE = mk_concat(xs);
    expr_ref ysE = mk_concat(ys);
    expr_ref ysy2 = mk_concat(ysE, y2);
    expr_ref Z = m_sk.mk_align_l(xsE, y1, ysE, y2);
    expr_ref xsZ = mk_concat(xsE, Z);
    expr_ref Zysy2 = mk_concat(Z, ysy2);
    
    dependency* dep = e.dep();
    bool propagated = false;
    if (propagate_lit(dep, 0, nullptr, m_ax.mk_ge(mk_len(y1), xs.size())))
        propagated = true;
    if (propagate_lit(dep, 0, nullptr, m_ax.mk_ge(mk_sub(mk_len(x), mk_len(y2)), ys.size())))
        propagated = true;
    if (propagate_eq(dep, x, Zysy2, true))
        propagated = true;
    if (propagate_eq(dep, y1, xsZ, true))
        propagated = true;
    return propagated;
}

bool theory_seq::branch_quat_variable() {
    for (auto const& e : m_eqs) {
        if (branch_quat_variable(e)) {
            return true;
        }
    }
    return false;
}

/*
 * Two properties of align_m
 *      align_m(align_m(x1, x, _, _), align_m(y1, x, _, _), z, t) = align_m(x1, y1, z, t)
 *      align_m(x1, x, _, _) - align_m(y1, x, _, _) = x1 - y1
 */
literal theory_seq::mk_alignment(expr* e1, expr* e2) {
    expr* x1 = nullptr, *x2 = nullptr, *y1 = nullptr, *y2 = nullptr;
    if (m_sk.is_align(e1, x1, x2) && m_sk.is_align(e2, y1, y2) && x2 == y2 && x1 != y1) {
        return mk_alignment(x1, y1);
    }
    return mk_simplified_literal(m_autil.mk_le(mk_sub(mk_len(e1), mk_len(e2)), m_autil.mk_int(0)));
}

// Equation is of the form x1 ++ xs ++ x2 = y1 ++ ys ++ y2 where xs, ys are units.
// If xs and ys cannot align then
//      x1 ++ xs ++ x2 = y1 ++ ys ++ y2 =>    |x1| >= |y1 ++ ys|  V  |x1 ++ xs| <= |y1|
bool theory_seq::branch_quat_variable(depeq const& e) {
    expr_ref_vector xs(m), ys(m);
    expr_ref x1(m), x2(m), y1(m), y2(m);
    if (!m_eq.match_quat_eq(e.ls, e.rs, x1, xs, x2, y1, ys, y2))
        return false;
    dependency* dep = e.dep();

    rational lenX1, lenX2, lenY1, lenY2;
    if (!get_length(x1, lenX1)) {
        add_length_to_eqc(x1);
    }
    if (!get_length(y1, lenY1)) {
        add_length_to_eqc(y1);
    }
    if (!get_length(x2, lenX2)) {
        add_length_to_eqc(x2);
    }
    if (!get_length(y2, lenY2)) {
        add_length_to_eqc(y2);
    }
    SASSERT(!xs.empty() && !ys.empty());

    bool cond = false;

    // xs = ys and xs and ys cannot align except the case xs = ys
    if (xs == ys) {
        expr_ref_vector xs1(m), xs2(m);
        xs1.reset();
        xs1.append(xs.size()-1, xs.data()+1);
        xs2.reset();
        xs2.append(xs.size()-1, xs.data());
        if (xs1.empty() || xs2.empty())
            cond = true;
        else if (!can_align_from_lhs(xs2, ys) && !can_align_from_rhs(xs1, ys))
            cond = true;
    }
    // xs and ys cannot align
    else if (!can_align_from_lhs(xs, ys) && !can_align_from_rhs(xs, ys))
        cond = true;

    if (!cond)
        return false;
    
    literal_vector lits;
    if (xs == ys) {
        literal lit = mk_eq(mk_len(x1), mk_len(y1), false);
        if (ctx.get_assignment(lit) == l_undef) {
            TRACE("seq", tout << mk_pp(x1, m) << " = " << mk_pp(y1, m) << "?\n";);
            ctx.mark_as_relevant(lit);
            return true;
        }
        else if (ctx.get_assignment(lit) == l_true) {
            TRACE("seq", tout << mk_pp(x1, m) << " = " << mk_pp(y1, m) << "\n";);
            propagate_eq(dep, lit, x1, y1, true);
            propagate_eq(dep, lit, x2, y2, true);
            return true;
        }
        TRACE("seq", tout << mk_pp(x1, m) << " != " << mk_pp(y1, m) << "\n";);
        lits.push_back(~lit);
    }
    
    literal lit1 = mk_alignment(x1, y1);
    literal lit2 = m_ax.mk_ge(mk_sub(mk_len(y1), mk_len(x1)), xs.size());
    literal lit3 = m_ax.mk_ge(mk_sub(mk_len(x1), mk_len(y1)), ys.size());
    if (ctx.get_assignment(lit1) == l_undef) {
        TRACE("seq", tout << mk_pp(x1, m) << " <= " << mk_pp(y1, m) << "?\n";);
        ctx.mark_as_relevant(lit1);
        return true;
    }
    if (ctx.get_assignment(lit1) == l_true) {
        TRACE("seq", tout << mk_pp(x1, m) << " <= " << mk_pp(y1, m) << "\n";);
        if (ctx.get_assignment(lit2) == l_undef) {
            ctx.mark_as_relevant(lit2);
            return true;
        }
    }
    else {
        TRACE("seq", tout << mk_pp(x1, m) << " > " << mk_pp(y1, m) << "\n";);
        if (ctx.get_assignment(lit3) == l_undef) {
            ctx.mark_as_relevant(lit3);
            return true;
        }
    }
    
    expr_ref xsE = mk_concat(xs);
    expr_ref ysE = mk_concat(ys);
    expr_ref x1xs = mk_concat(x1, xsE);
    expr_ref y1ys = mk_concat(y1, ysE);
    expr_ref xsx2 = mk_concat(xsE, x2);
    expr_ref ysy2 = mk_concat(ysE, y2);
    if (ctx.get_assignment(lit1) == l_true && ctx.get_assignment(lit2) == l_true) {
        // |x1++xs| <= |y1| => x1 ++ xs ++ z2 = y1, x2 = z2 ++ ys ++ y2
        expr_ref Z2 = m_sk.mk_align_m(y1, x1, xsE, x2);
        expr_ref x1xsZ2 = mk_concat(x1xs, Z2);
        expr_ref Z2ysy2 = mk_concat(Z2, ysy2);
        propagate_eq(dep, lit2, x1xsZ2, y1, true);
        propagate_eq(dep, lit2, x2, Z2ysy2, true);
        return true;
    }
    if (ctx.get_assignment(lit1) == l_false && ctx.get_assignment(lit3) == l_true) {
        // |x1| >= |y1++ys| => x1 = y1 ++ ys ++ z1, z1 ++ xs ++ x2 = y2
        expr_ref Z1 = m_sk.mk_align_m(x1, y1, ysE, y2);
        expr_ref y1ysZ1 = mk_concat(y1ys, Z1);
        expr_ref Z1xsx2 = mk_concat(Z1, xsx2);
        propagate_eq(dep, lit3, x1, y1ysZ1, true);
        propagate_eq(dep, lit3, Z1xsx2, y2, true);
        return true;
    }
    // Infeasible cases because xs and ys cannot align
    if (ctx.get_assignment(lit1) == l_false && ctx.get_assignment(lit2) == l_true) {
        lits.push_back(~lit1);
        lits.push_back(lit2);
        return propagate_lit(nullptr, lits.size(), lits.data(), false_literal);
    }
    if (ctx.get_assignment(lit1) == l_true && ctx.get_assignment(lit3) == l_true) {
        lits.push_back(lit1);
        lits.push_back(lit3);
        return propagate_lit(nullptr, lits.size(), lits.data(), false_literal);
    }
    if (ctx.get_assignment(lit1) == l_true && ctx.get_assignment(lit2) == l_false) {
        lits.push_back(lit1);
        lits.push_back(~lit2);
        return propagate_lit(dep, lits.size(), lits.data(), false_literal);
    }
    if (ctx.get_assignment(lit1) == l_false && ctx.get_assignment(lit3) == l_false) {
        lits.push_back(~lit1);
        lits.push_back(~lit3);
        return propagate_lit(dep, lits.size(), lits.data(), false_literal);
    }
    UNREACHABLE();
    return false;
}


bool theory_seq::branch_variable_eq() {
    unsigned sz = m_eqs.size();
    int start = ctx.get_random_value();

    for (unsigned i = 0; i < sz; ++i) {
        unsigned k = (i + start) % sz;
        depeq const& e = m_eqs[k];

        if (branch_variable_eq(e)) {
            TRACE("seq", tout << "branch variable\n";);
            return true;
        }
    }
    return ctx.inconsistent();
}

bool theory_seq::branch_variable_eq(depeq const& e) {
    unsigned id = e.id();
    unsigned s = find_branch_start(2*id);
    TRACE("seq", tout << s << " " << id << ": " << e.ls << " = " << e.rs << "\n";);
    bool found = find_branch_candidate(s, e.dep(), e.ls, e.rs);
    insert_branch_start(2*id, s);
    if (!found) {
        s = find_branch_start(2*id + 1);
        found = find_branch_candidate(s, e.dep(), e.rs, e.ls);
        insert_branch_start(2*id + 1, s);
    }
    return found;
}

void theory_seq::insert_branch_start(unsigned k, unsigned s) {
    m_branch_start.insert(k, s);
    m_trail_stack.push(pop_branch(*this, k));
}

unsigned theory_seq::find_branch_start(unsigned k) {
    unsigned s = 0;
    if (m_branch_start.find(k, s)) {
        return s;
    }
    return 0;
}

bool theory_seq::find_branch_candidate(unsigned& start, dependency* dep, expr_ref_vector const& ls, expr_ref_vector const& rs) {
    if (ls.empty()) {
        return false;
    }
    expr* l = ls.get(0);

    if (!is_var(l)) {
        return false;
    }

    TRACE("seq", tout << mk_pp(l, m) << ": " << ctx.get_scope_level() << " - start:" << start << "\n";);

    expr_ref v0(m);
    v0 = m_util.str.mk_empty(l->get_sort());
    if (can_be_equal(ls.size() - 1, ls.data() + 1, rs.size(), rs.data())) {
        if (assume_equality(l, v0)) {
            TRACE("seq", tout << mk_pp(l, m) << " " << v0 << "\n";);
            return true;
        }
    }
    for (; start < rs.size(); ++start) {
        unsigned j = start;
        SASSERT(!m_util.str.is_concat(rs.get(j)));
        SASSERT(!m_util.str.is_string(rs.get(j)));
        if (l == rs.get(j)) {
            return false;
        }
        if (!can_be_equal(ls.size() - 1, ls.data() + 1, rs.size() - j - 1, rs.data() + j + 1)) {
            continue;
        }
        v0 = mk_concat(j + 1, rs.data());
        if (assume_equality(l, v0)) {
            TRACE("seq", tout << mk_pp(l, m) << " " << v0 << "\n";);
            ++start;
            return true;
        }
    }

    bool all_units = true;
    for (expr* r : rs) {
        all_units &= m_util.str.is_unit(r);
    }
    if (all_units) {
        literal_vector lits;
        lits.push_back(~mk_eq_empty(l));
        for (unsigned i = 0; i < rs.size(); ++i) {
            if (can_be_equal(ls.size() - 1, ls.data() + 1, rs.size() - i - 1, rs.data() + i + 1)) {
                v0 = mk_concat(i + 1, rs.data());
                lits.push_back(~mk_eq(l, v0, false));
            }
        }
        for (literal lit : lits) {
            switch (ctx.get_assignment(lit)) {
            case l_true:  break;
            case l_false: start = 0; return false;
            case l_undef: ctx.mark_as_relevant(lit); ctx.force_phase(~lit); start = 0; return true;
            }
        }
        set_conflict(dep, lits);
        TRACE("seq", 
              tout << "start: " << start << "\n";
              for (literal lit : lits) {
                  ctx.display_literal_verbose(tout << lit << ": ", lit) << "\n";
                  ctx.display(tout, ctx.get_justification(lit.var())); tout << "\n";
              });
        return true;
    }
    return false;
}

bool theory_seq::can_be_equal(unsigned szl, expr* const* ls, unsigned szr, expr* const* rs) const {
    unsigned i = 0;
    for (; i < szl && i < szr; ++i) {
        if (m.are_distinct(ls[i], rs[i])) {
            return false;
        }
        if (!m.are_equal(ls[i], rs[i])) {
            break;
        }
    }
    if (i == szr) {
        std::swap(ls, rs);
        std::swap(szl, szr);
    }
    if (i == szl && i < szr) {
        for (; i < szr; ++i) {
            if (m_util.str.is_unit(rs[i])) {
                return false;
            }
        }
    }
    return true;
}


bool theory_seq::assume_equality(expr* l, expr* r) {
    if (m_exclude.contains(l, r)) {
        return false;
    }

    expr_ref eq(m.mk_eq(l, r), m);
    m_rewrite(eq);
    if (m.is_true(eq)) {
        return false;
    }
    if (m.is_false(eq)) {
        return false;
    }

    enode* n1 = ensure_enode(l);
    enode* n2 = ensure_enode(r);
    if (n1->get_root() == n2->get_root()) {
        TRACE("seq", tout << mk_pp(l, m) << " = " << mk_pp(r, m) << " roots eq\n";);
        return false;
    }
    if (ctx.is_diseq(n1, n2)) {
        TRACE("seq", tout << mk_pp(l, m) << " = " << mk_pp(r, m) << " is_diseq\n";);
        return false;
    }
    ctx.mark_as_relevant(n1);
    ctx.mark_as_relevant(n2);
    if (!ctx.assume_eq(n1, n2)) {
        TRACE("seq", tout << mk_pp(l, m) << " = " << mk_pp(r, m) << " can't assume\n";);
        return false;
    }
    lbool res = ctx.get_assignment(mk_eq(l, r, false));
    TRACE("seq", tout << mk_pp(l, m) << " = " << mk_pp(r, m) << " literal assigned " << res << "\n";);
    return res != l_false;
}


bool theory_seq::propagate_length_coherence(expr* e) {
    expr_ref head(m), tail(m);
    rational lo, hi;

    if (!is_var(e) || !m_rep.is_root(e)) {
        return false;
    }
    if (!lower_bound2(e, lo) || !lo.is_pos() || lo >= rational(2048)) {
        return false;
    }
    TRACE("seq", tout << "Unsolved " << mk_pp(e, m);
          if (!lower_bound2(e, lo)) lo = -rational::one();
          if (!upper_bound(mk_len(e), hi)) hi = -rational::one();
          tout << " lo: " << lo << " hi: " << hi << "\n";
          );

    expr_ref seq(e, m);
    expr_ref_vector elems(m);
    unsigned _lo = lo.get_unsigned();
    for (unsigned j = 0; j < _lo; ++j) {
        m_sk.decompose(seq, head, tail);
        elems.push_back(head);
        seq = tail;
    }
    expr_ref emp(m_util.str.mk_empty(e->get_sort()), m);
    elems.push_back(seq);
    tail = mk_concat(elems.size(), elems.data());
    // len(e) >= low => e = tail;
    expr_ref lo_e(m_autil.mk_numeral(lo, true), m);
    expr_ref len_e_ge_lo(m_autil.mk_ge(mk_len(e), lo_e), m);
    literal low = mk_literal(len_e_ge_lo);
    literal eq = mk_seq_eq(e, tail);
    bool added = false;
    if (ctx.get_assignment(eq) != l_true) {
        add_axiom(~low, eq);
        added = true;
    }
    expr_ref len_e = mk_len(e);
    if (upper_bound(len_e, hi)) {
        // len(e) <= hi => len(tail) <= hi - lo
        expr_ref high1(m_autil.mk_le(len_e, m_autil.mk_numeral(hi, true)), m);
        if (hi == lo) {
            add_axiom(~mk_literal(high1), mk_seq_eq(seq, emp));
            added = true;
        }
        else {
            expr_ref high2(m_autil.mk_le(mk_len(seq), m_autil.mk_numeral(hi-lo, true)), m);
            literal h2 = mk_literal(high2);
            if (ctx.get_assignment(h2) != l_true) {
                add_axiom(~mk_literal(high1), h2);
                added = true;
            }
        }
    }
    else {
        assume_equality(seq, emp);
        added = true;
    }
    return added;
}


bool theory_seq::check_length_coherence(expr* e) {
    if (is_var(e) && m_rep.is_root(e)) {
        if (!check_length_coherence0(e)) {
            expr_ref emp(m_util.str.mk_empty(e->get_sort()), m);
            expr_ref head(m), tail(m);
            // e = emp \/ e = unit(head.elem(e))*tail(e)
            m_sk.decompose(e, head, tail);
            expr_ref conc = mk_concat(head, tail);
            if (propagate_is_conc(e, conc)) {
                assume_equality(tail, emp);
            }
        }
        return true;
    }
    return false;
}

bool theory_seq::check_length_coherence0(expr* e) {
    if (is_var(e) && m_rep.is_root(e)) {
        expr_ref emp(m_util.str.mk_empty(e->get_sort()), m);
        bool p = propagate_length_coherence(e);

        if (p || assume_equality(e, emp)) {
            if (!ctx.at_base_level()) {
                m_trail_stack.push(push_replay(*this, alloc(replay_length_coherence, m, e)));
            }
            return true;
        }
    }
    return false;
}

bool theory_seq::check_length_coherence() {

    for (expr* l : m_length) {
        expr* e = nullptr;
        VERIFY(m_util.str.is_length(l, e));
        if (check_length_coherence0(e)) {
            return true;
        }
    }
    bool change = false;
    unsigned sz = m_length.size();
    for (unsigned i = 0; i < sz; ++i) {
        expr* l = m_length.get(i);
        expr* e = nullptr;
        VERIFY(m_util.str.is_length(l, e));
        if (check_length_coherence(e)) {
            return true;
        }
        if (!ctx.e_internalized(e))
            change = true;
        enode* n = ensure_enode(e);
        enode* r = n->get_root();
        if (r != n && has_length(r->get_expr())) {
            continue;
        }
        if (add_length_to_eqc(e)) {
            change = true;
        }
    }
    return change;
}

bool theory_seq::reduce_length_eq() {
    int start = ctx.get_random_value();

    for (unsigned i = 0; !ctx.inconsistent() && i < m_eqs.size(); ++i) {
        depeq const& e = m_eqs[(i + start) % m_eqs.size()];
        if (reduce_length_eq(e.ls, e.rs, e.dep())) {
            TRACE("seq", tout << "reduce length eq\n";);
            return true;
        }
    }
    return false;
}


/**
  \brief ls := X... == rs := abcdef
*/
bool theory_seq::is_unit_eq(expr_ref_vector const& ls, expr_ref_vector const& rs) {
    if (ls.empty() || !is_var(ls[0])) {
        return false;
    }

    for (auto const& elem : rs) {
        if (!m_util.str.is_unit(elem)) {
            return false;
        }
    }
    return true;
}
 

struct remove_obj_pair_map : public trail {
    ast_manager& m;
    obj_pair_hashtable<expr, expr> & m_map;
    expr* a, *b;
    remove_obj_pair_map(ast_manager& m, obj_pair_hashtable<expr, expr> & map, expr* a, expr* b):
        m(m), m_map(map), a(a), b(b) {}
    void undo() override {
        m.dec_ref(a);
        m.dec_ref(b);
        m_map.erase(std::make_pair(a, b));
    }
};

/**
   nth(x,idx) = rhs => 
   x = pre(x, idx) ++ unit(rhs) ++ post(x, idx + 1)
   NB: need 0 <= idx < len(rhs)   
*/
bool theory_seq::solve_nth_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* deps) {
    expr* s = nullptr, *idx = nullptr;
    if (ls.size() == 1 && m_util.str.is_nth_i(ls[0], s, idx)) {
        rational r;
        bool idx_is_zero = m_autil.is_numeral(idx, r) && r.is_zero();
        expr_ref_vector ls1(m), rs1(m); 
        expr_ref idx1(m_autil.mk_add(idx, m_autil.mk_int(1)), m);
        m_rewrite(idx1);
        expr_ref rhs = mk_concat(rs.size(), rs.data(), ls[0]->get_sort());
        if (m_nth_eq2_cache.contains(std::make_pair(rhs, ls[0])))
            return false;
        m.inc_ref(rhs);
        m.inc_ref(ls[0]);
        m_nth_eq2_cache.insert(std::make_pair(rhs, ls[0]));
        ctx.push_trail(remove_obj_pair_map(m, m_nth_eq2_cache, rhs, ls[0]));
        ls1.push_back(s);        
        if (!idx_is_zero) rs1.push_back(m_sk.mk_pre(s, idx)); 
        rs1.push_back(m_util.str.mk_unit(rhs)); 
        rs1.push_back(m_sk.mk_post(s, idx1));
        TRACE("seq", tout << ls1 << "\n"; tout << rs1 << "\n";);
        m_eqs.push_back(depeq(m_eq_id++, ls1, rs1, deps));
        return true;
    }   
    return false;
}





#if 0

/**
   \brief

   This step performs destructive superposition

   Based on the implementation it would do the following:
  
   e:   l1 + l2 + l3 + l = r1 + r2 + r
   G |- len(l1) = len(l2) = len(r1) = 0
   e':  l1 + l2 + l3 + l = r3 + r'         occurs prior to e among equations
   G |- len(r3) = len(r2)
   r2, r3 are not identical
   ----------------------------------
   e'' : r3 + r' = r1 + r2 + r

   e:   l1 + l2 + l3 + l = r1 + r2 + r
   G |- len(l1) = len(l2) = len(r1) = 0
   e':  l1 + l2 + l3 + l = r3 + r'         occurs prior to e among equations
   G |- len(r3) = len(r2) + offset
   r2, r3 are not identical
   ----------------------------------
   e'' : r3 + r' = r1 + r2 + r

   NB, this doesn't make sense because e'' is just e', which already occurs.
   It doesn't inherit the constraints from e either, which would get lost.

   NB, if len(r3) = len(r2) would be used, then the justification for the equality
   needs to be tracked in dependencies.
    
   TODO: propagate length offsets for last vars

*/
bool theory_seq::find_better_rep(expr_ref_vector const& ls, expr_ref_vector const& rs, unsigned idx,
                                 dependency*& deps, expr_ref_vector & res) {

    // disabled until functionality is clarified
    return false;

    if (ls.empty() || rs.empty())
        return false;
    expr* l_fst = find_fst_non_empty_var(ls);
    expr* r_fst = find_fst_non_empty_var(rs);
    if (!r_fst) return false;
    expr_ref len_r_fst = mk_len(r_fst);
    expr_ref len_l_fst(m);
    enode * root2;
    if (!ctx.e_internalized(len_r_fst)) {
        return false;
    }
    if (l_fst) {
        len_l_fst = mk_len(l_fst);
    }

    root2 = get_root(len_r_fst);

    // Offset = 0, No change
    if (l_fst && get_root(len_l_fst) == root2) {
        TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst, m) << ")\n";);
        return false;
    }

    // Offset = 0, Changed

    for (unsigned i = 0; i < idx; ++i) {
        depeq const& e = m_eqs[i];
        if (e.ls != ls) continue;
        expr* nl_fst = nullptr;
        if (e.rs.size() > 1 && is_var(e.rs.get(0)))
            nl_fst = e.rs.get(0);
        if (nl_fst && nl_fst != r_fst && root2 == get_root(mk_len(nl_fst))) {
            res.reset();
            res.append(e.rs);
            deps = m_dm.mk_join(e.dep(), deps);
            return true;
        }
    }
    // Offset != 0, No change
    if (l_fst && ctx.e_internalized(len_l_fst)) {
        enode * root1 = get_root(len_l_fst);
        if (m_offset_eq.contains(root1, root2)) {
            TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst,m) << ")\n";);
            return false;
        }
    }
    // Offset != 0, Changed
    if (m_offset_eq.contains(root2)) {
        for (unsigned i = 0; i < idx; ++i) {
            depeq const& e = m_eqs[i];
            if (e.ls != ls) continue;
            expr* nl_fst = nullptr;
            if (e.rs.size() > 1 && is_var(e.rs.get(0)))
                nl_fst = e.rs.get(0);
            if (nl_fst && nl_fst != r_fst) {
                expr_ref len_nl_fst = mk_len(nl_fst);
                if (ctx.e_internalized(len_nl_fst)) {
                    enode * root1 = get_root(len_nl_fst);
                    if (m_offset_eq.contains(root2, root1)) {
                        res.reset();
                        res.append(e.rs);
                        deps = m_dm.mk_join(e.dep(), deps);
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

int theory_seq::find_fst_non_empty_idx(expr_ref_vector const& xs) {
    for (unsigned i = 0; i < xs.size(); ++i) {
        expr* x = xs[i];
        if (!is_var(x)) 
            return -1;
        expr_ref e = mk_len(x);
        if (ctx.e_internalized(e)) {
            enode* root = ctx.get_enode(e)->get_root();
            rational val;
            if (m_autil.is_numeral(root->get_expr(), val) && val.is_zero()) {
                continue;
            }
        }
        return i;
    }
    return -1;
}

expr* theory_seq::find_fst_non_empty_var(expr_ref_vector const& x) {
    int i = find_fst_non_empty_idx(x);
    if (i >= 0)
        return x[i];
    return nullptr;
}

#endif
