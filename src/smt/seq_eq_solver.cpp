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
    context& ctx = get_context();
    bool change = false;
    for (; !ctx.inconsistent() && i < m_eqs.size(); ++i) {
        eq const& e = m_eqs[i];
        if (solve_eq(e.ls(), e.rs(), e.dep(), i)) {
            if (i + 1 != m_eqs.size()) {
                eq e1 = m_eqs[m_eqs.size()-1];
                m_eqs.set(i, e1);
                --i;
            }
            ++m_stats.m_num_reductions;
            m_eqs.pop_back();
            change = true;
        }
        TRACE("seq_verbose", display_equations(tout););
    }
    return change || m_new_propagation || ctx.inconsistent();
}

bool theory_seq::solve_eq(expr_ref_vector const& l, expr_ref_vector const& r, dependency* deps, unsigned idx) {
    context& ctx = get_context();
    expr_ref_vector& ls = m_ls;
    expr_ref_vector& rs = m_rs;
    rs.reset(); ls.reset();
    dependency* dep2 = nullptr;
    bool change = false;
    if (!canonize(l, ls, dep2, change)) return false;
    if (!canonize(r, rs, dep2, change)) return false;
    deps = m_dm.mk_join(dep2, deps);
    TRACE("seq_verbose", tout << l << " = " << r << " ==> ";
          tout << ls << " = " << rs << "\n";
          display_deps(tout, deps);
          );
    if (!ctx.inconsistent() && simplify_eq(ls, rs, deps)) {
        TRACE("seq", tout << "simplified\n";);
        return true;
    }
    if (!ctx.inconsistent() && lift_ite(ls, rs, deps)) {
        return true;
    }
    TRACE("seq_verbose", tout << ls << " = " << rs << "\n";);
    if (ls.empty() && rs.empty()) {
        return true;
    }
    if (!ctx.inconsistent() && solve_unit_eq(ls, rs, deps)) {
        TRACE("seq", tout << "unit\n";);
        return true;
    }
    if (!ctx.inconsistent() && solve_binary_eq(ls, rs, deps)) {
        TRACE("seq", tout << "binary\n";);
        return true;
    }
    if (!ctx.inconsistent() && solve_nth_eq1(ls, rs, deps)) {
        return true;
    }
    if (!ctx.inconsistent() && solve_nth_eq1(rs, ls, deps)) {
        return true;
    }
    if (!ctx.inconsistent() && solve_itos(rs, ls, deps)) {
        return true;
    }
    if (!ctx.inconsistent() && change) {
        // The propagation step from arithmetic state (e.g. length offset) to length constraints
        if (get_context().get_scope_level() == 0) {
            prop_arith_to_len_offset();
        }
        TRACE("seq", tout << "inserting equality\n";);
        bool updated = false;
        expr_ref_vector new_ls(m);
        if (!m_len_offset.empty() && 
            find_better_rep(ls, rs, idx, deps, new_ls)) {
            // Find a better equivalent term for lhs of an equation based on length constraints            
            m_eqs.push_back(eq(m_eq_id++, new_ls, rs, deps));
        }
        else {
            m_eqs.push_back(eq(m_eq_id++, ls, rs, deps));
        }
        TRACE("seq", tout << "simplified\n";);
        return true;
    }
    return false;
}

bool theory_seq::solve_unit_eq(expr* l, expr* r, dependency* deps) {
    if (l == r) {
        return true;
    }
    if (is_var(l) && !occurs(l, r) && add_solution(l, r, deps)) {
        return true;
    }
    if (is_var(r) && !occurs(r, l) && add_solution(r, l, deps)) {
        return true;
    }
    return false;
}

bool theory_seq::solve_unit_eq(expr_ref_vector const& l, expr_ref_vector const& r, dependency* deps) {
    if (l.size() == 1 && is_var(l[0]) && !occurs(l[0], r) && add_solution(l[0], mk_concat(r, m.get_sort(l[0])), deps)) {
        return true;
    }
    if (r.size() == 1 && is_var(r[0]) && !occurs(r[0], l) && add_solution(r[0], mk_concat(l, m.get_sort(r[0])), deps)) {
        return true;
    }
    return false;
}

bool theory_seq::solve_binary_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* dep) {
    context& ctx = get_context();
    ptr_vector<expr> xs, ys;
    expr_ref x(m), y(m);
    bool is_binary = 
        is_binary_eq(ls, rs, x, xs, ys, y) || 
        is_binary_eq(rs, ls, x, xs, ys, y);
    if (!is_binary) {
        return false;
    }
    // Equation is of the form x ++ xs = ys ++ y
    // where xs, ys are units.
    if (x != y) {
        return false;
    }
    if (xs.size() != ys.size()) {
        TRACE("seq", tout << "binary conflict\n";);
        set_conflict(dep);
        return false;
    }
    if (xs.empty()) {
        // this should have been solved already
        UNREACHABLE();
        return false;
    }

    // Equation is of the form x ++ xs = ys ++ x
    // where |xs| = |ys| are units of same length
    // then xs is a wrap-around of ys
    // x ++ ab = ba ++ x
    // 
    if (xs.size() == 1) {
        enode* n1 = ensure_enode(xs[0]);
        enode* n2 = ensure_enode(ys[0]);
        if (n1->get_root() == n2->get_root()) {
            return false;
        }
        literal eq = mk_eq(xs[0], ys[0], false);
        switch (ctx.get_assignment(eq)) {
        case l_false: {
            literal_vector conflict;
            conflict.push_back(~eq);
            TRACE("seq", tout << conflict << "\n";);
            set_conflict(dep, conflict);
            break;
        }
        case l_true:
            break;
        case l_undef: 
            ctx.mark_as_relevant(eq);
            propagate_lit(dep, 0, nullptr, eq);
            m_new_propagation = true;
            break;
        }
    }
    return false;
}


bool theory_seq::occurs(expr* a, expr_ref_vector const& b) {
    for (auto const& elem : b) {
        if (a == elem || m.is_ite(elem)) return true;
    }
    return false;
}

bool theory_seq::occurs(expr* a, expr* b) {
     // true if a occurs under an interpreted function or under left/right selector.
    SASSERT(is_var(a));
    SASSERT(m_todo.empty());
    expr* e1 = nullptr, *e2 = nullptr;
    m_todo.push_back(b);
    while (!m_todo.empty()) {
        b = m_todo.back();
        if (a == b || m.is_ite(b)) {
            m_todo.reset();
            return true;
        }
        m_todo.pop_back();
        if (m_util.str.is_concat(b, e1, e2)) {
            m_todo.push_back(e1);
            m_todo.push_back(e2);
        }
        else if (m_util.str.is_unit(b, e1)) {
            m_todo.push_back(e1);
        }
        else if (m_util.str.is_nth_i(b, e1, e2)) {
            m_todo.push_back(e1);
        }
    }
    return false;
}

// TODO: propagate length offsets for last vars
bool theory_seq::find_better_rep(expr_ref_vector const& ls, expr_ref_vector const& rs, unsigned idx,
                                 dependency*& deps, expr_ref_vector & res) {
    context& ctx = get_context();

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
        TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst,m) << ")\n";);
        return false;
    }

    // Offset = 0, Changed

    for (unsigned i = 0; i < idx; ++i) {
        eq const& e = m_eqs[i];
        if (e.ls() != ls) continue;
        expr* nl_fst = nullptr;
        if (e.rs().size() > 1 && is_var(e.rs().get(0)))
            nl_fst = e.rs().get(0);
        if (nl_fst && nl_fst != r_fst && root2 == get_root(mk_len(nl_fst))) {
            res.reset();
            res.append(e.rs().size(), e.rs().c_ptr());
            deps = m_dm.mk_join(e.dep(), deps);
            return true;
        }
    }
    // Offset != 0, No change
    if (l_fst && ctx.e_internalized(len_l_fst)) {
        enode * root1 = get_root(len_l_fst);
        obj_map<enode, int> tmp;
        int offset;
        if (!m_autil.is_numeral(root1->get_owner()) && !m_autil.is_numeral(root2->get_owner())) {
            if (m_len_offset.find(root1, tmp) && tmp.find(root2, offset)) {
                TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst,m) << ")\n";);
                find_max_eq_len(ls, rs);
                return false;
            }
            else if (m_len_offset.find(root2, tmp) && tmp.find(root1, offset)) {
                TRACE("seq", tout << "(" << mk_pp(r_fst, m) << ", " << mk_pp(l_fst,m) << ")\n";);
                find_max_eq_len(ls ,rs);
                return false;
            }
        }
    }
    // Offset != 0, Changed
    obj_map<enode, int> tmp;
    if (!m_autil.is_numeral(root2->get_owner()) && m_len_offset.find(root2, tmp)) {
        for (unsigned i = 0; i < idx; ++i) {
            eq const& e = m_eqs[i];
            if (e.ls() != ls) continue;
            expr* nl_fst = nullptr;
            if (e.rs().size()>1 && is_var(e.rs().get(0)))
                nl_fst = e.rs().get(0);
            if (nl_fst && nl_fst != r_fst) {
                int offset;
                expr_ref len_nl_fst = mk_len(nl_fst);
                if (ctx.e_internalized(len_nl_fst)) {
                    enode * root1 = ctx.get_enode(len_nl_fst)->get_root();
                    if (!m_autil.is_numeral(root1->get_owner()) && tmp.find(root1, offset)) {
                        res.reset();
                        res.append(e.rs().size(), e.rs().c_ptr());
                        deps = m_dm.mk_join(e.dep(), deps);
                        find_max_eq_len(res, rs);
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

bool theory_seq::has_len_offset(expr_ref_vector const& ls, expr_ref_vector const& rs, int & offset) {
    context& ctx = get_context();

    if (ls.empty() || rs.empty()) 
        return false;
    expr* l_fst = ls[0];
    expr* r_fst = rs[0];
    if (!is_var(l_fst) || !is_var(r_fst)) 
        return false;

    expr_ref len_l_fst = mk_len(l_fst);
    if (!ctx.e_internalized(len_l_fst)) 
        return false;
    enode * root1 = ctx.get_enode(len_l_fst)->get_root();

    expr_ref len_r_fst = mk_len(r_fst);
    if (!ctx.e_internalized(len_r_fst))
        return false;
    enode* root2 = ctx.get_enode(len_r_fst)->get_root();

    if (root1 == root2) {
        TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst,m) << ")\n";);
        offset = 0;
        return true;
    }

    if (m_autil.is_numeral(root1->get_owner()) || m_autil.is_numeral(root2->get_owner())) 
        return false;

    obj_map<enode, int> tmp;
    if (m_len_offset.find(root1, tmp) && tmp.find(root2, offset)) {
        TRACE("seq", tout << "(" << mk_pp(l_fst, m) << ", " << mk_pp(r_fst,m) << ")\n";);
        return true;
    }
    if (m_len_offset.find(root2, tmp) && tmp.find(root1, offset)) {
        offset = -offset;
        TRACE("seq", tout << "(" << mk_pp(r_fst, m) << ", " << mk_pp(l_fst,m) << ")\n";);
        return true;
    }
    return false;
}

bool theory_seq::len_based_split() {
    unsigned sz = m_eqs.size();
    if (sz == 0)
        return false;

    if ((int) get_context().get_scope_level() > m_len_prop_lvl) {
        m_len_prop_lvl = get_context().get_scope_level();
        prop_arith_to_len_offset();
        if (!m_len_offset.empty()) {
            for (unsigned i = sz-1; i > 0; --i) {
                eq const& e = m_eqs[i];
                expr_ref_vector new_ls(m);
                dependency *deps = e.dep();
                if (find_better_rep(e.ls(), e.rs(), i, deps, new_ls)) {
                    expr_ref_vector rs(m);
                    rs.append(e.rs().size(), e.rs().c_ptr());
                    m_eqs.set(i, eq(m_eq_id++, new_ls, rs, deps));
                    TRACE("seq", display_equation(tout, m_eqs[i]););
                }
            }
        }
    }

    for (auto const& e : m_eqs) {
        if (len_based_split(e)) {
            return true;
        }
    }
    return false;
}

bool theory_seq::len_based_split(eq const& e) {
    context& ctx = get_context();
    expr_ref_vector const& ls = e.ls();
    expr_ref_vector const& rs = e.rs();
    
    int offset_orig = 0;
    if (!has_len_offset(ls, rs, offset_orig))
        return false;
        
    TRACE("seq", tout << "split based on length\n";);
    TRACE("seq", display_equation(tout, e););
    expr_ref x11(m_util.str.mk_concat(1, ls.c_ptr()), m);
    expr_ref x12(m_util.str.mk_concat(ls.size()-1, ls.c_ptr()+1), m);
    expr_ref y11(m_util.str.mk_concat(1, rs.c_ptr()), m);
    expr_ref y12(m_util.str.mk_concat(rs.size()-1, rs.c_ptr()+1), m);

    expr_ref lenX11 = mk_len(x11);
    expr_ref lenY11(m);
    expr_ref Z(m);
    int offset = 0;
    if (offset_orig != 0) {
        lenY11 = m_autil.mk_add(mk_len(y11), m_autil.mk_int(offset_orig));
        if (offset_orig > 0) {
            offset = offset_orig;
            Z = m_sk.mk_align(y12, x12, x11, y11);
            y11 = mk_concat(y11, Z);
            x12 = mk_concat(Z, x12);
        }
        else {
            offset = -offset_orig;
            Z = m_sk.mk_align(x12, y12, y11, x11);
            x11 = mk_concat(x11, Z);
            y12 = mk_concat(Z, y12);
        }
    }
    else {
        lenY11 = mk_len(y11);
    }

    dependency* dep = e.dep();
    literal_vector lits;
    literal lit1 = mk_eq(lenX11, lenY11, false);
    if (ctx.get_assignment(lit1) != l_true) {
        return false;
    }
    lits.push_back(lit1);

    if (ls.size() >= 2 && rs.size() >= 2 && (ls.size() > 2 || rs.size() > 2)) {
        expr_ref len1(m_autil.mk_int(0),m), len2(m_autil.mk_int(0),m);
        for (unsigned i = 2; i < ls.size(); ++i) {
            len1 = mk_add(len1, mk_len(ls[i]));
        }
        for (unsigned i = 2; i < rs.size(); ++i) {
            len2 = mk_add(len2, mk_len(rs[i]));
        }
        literal lit2;
        if (!m_autil.is_numeral(len1) && !m_autil.is_numeral(len2)) {
            lit2 = mk_eq(len1, len2, false);           
        }
        else {
            expr_ref eq_len(m.mk_eq(len1, len2), m);
            lit2 = mk_literal(eq_len);            
        }
        
        if (ctx.get_assignment(lit2) == l_true) {           
            lits.push_back(lit2);
            TRACE("seq", tout << mk_pp(len1, m) << " = " << mk_pp(len2, m) << "\n";);
            expr_ref lhs(m), rhs(m);
            if (ls.size() > 2)
                lhs = m_util.str.mk_concat(ls.size()-2, ls.c_ptr()+2);
            else
                lhs = m_util.str.mk_empty(m.get_sort(x11));
            if (rs.size() > 2)
                rhs = m_util.str.mk_concat(rs.size()-2, rs.c_ptr()+2);
            else
                rhs = m_util.str.mk_empty(m.get_sort(x11));
            propagate_eq(dep, lits, lhs, rhs, true);
            lits.pop_back();
        }
    }

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
    if (branch_variable_mb()) return true;
    if (branch_variable_eq()) return true;
    if (branch_ternary_variable1()) return true;
    if (branch_ternary_variable2()) return true;
    if (branch_quat_variable()) return true;
    return false;
}

bool theory_seq::branch_variable_mb() {
    bool change = false;
    for (auto const& e : m_eqs) {
        vector<rational> len1, len2;
        if (!is_complex(e)) {
            continue;
        }
        if (e.ls().empty() || e.rs().empty() || 
            (!is_var(e.ls()[0]) && !is_var(e.rs()[0]))) {
            continue;
        }

        if (!enforce_length(e.ls(), len1) || !enforce_length(e.rs(), len2)) {
            // change = true;
            continue;
        }
        rational l1, l2;
        for (const auto& elem : len1) l1 += elem;
        for (const auto& elem : len2) l2 += elem;
        if (l1 != l2) {
            expr_ref l = mk_concat(e.ls());
            expr_ref r = mk_concat(e.rs());
            expr_ref lnl = mk_len(l), lnr = mk_len(r);
            if (propagate_eq(e.dep(), lnl, lnr, false)) {
                change = true;
            }
            continue;
        }
        if (split_lengths(e.dep(), e.ls(), e.rs(), len1, len2)) {
            TRACE("seq", tout << "split lengths\n";);
            change = true;
            break;
        }
    }
    return change;
}


bool theory_seq::is_complex(eq const& e) {
    unsigned num_vars1 = 0, num_vars2 = 0;
    for (auto const& elem : e.ls()) {
        if (is_var(elem)) ++num_vars1;
    }
    for (auto const& elem : e.rs()) {
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
    context& ctx = get_context();
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
    b = mk_concat(bs, m.get_sort(X));

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
        expr_ref bY(m_util.str.mk_concat(bs), m);
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

bool theory_seq::branch_binary_variable(eq const& e) {
    if (is_complex(e)) {
        return false;
    }
    ptr_vector<expr> xs, ys;
    expr_ref x(m), y(m);
    bool is_binary = is_binary_eq(e.ls(), e.rs(), x, xs, ys, y);
    if (!is_binary) {
        is_binary = is_binary_eq(e.rs(), e.ls(), x, xs, ys, y);
    }
    if (!is_binary) {
        return false;
    }
    if (x == y) {
        return false;
    }
        
    // Equation is of the form x ++ xs = ys ++ y
    // where xs, ys are units.
    // x is either a prefix of ys, all of ys ++ y or ys ++ y1, such that y = y1 ++ y2, y2 = xs 
    
    rational lenX, lenY;
    context& ctx = get_context();
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
        expr_ref b(m_autil.mk_int(ys.size()-xs.size()), m);
        propagate_lit(e.dep(), 0, nullptr, mk_eq(a, b, false));
        return true;
    }
    if (lenX <= rational(ys.size())) {
        expr_ref_vector Ys(m);
        Ys.append(ys.size(), ys.c_ptr());
        branch_unit_variable(e.dep(), x, Ys);
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
        if (is_unit_eq(e.ls(), e.rs())) {
            branch_unit_variable(e.dep(), e.ls()[0], e.rs());
            result = true;
            break;
        }
        else if (is_unit_eq(e.rs(), e.ls())) {
            branch_unit_variable(e.dep(), e.rs()[0], e.ls());
            result = true;
            break;
        }
    }
    CTRACE("seq", result, tout << "branch unit variable\n";);
    return result;
}

void theory_seq::branch_unit_variable(dependency* dep, expr* X, expr_ref_vector const& units) {
    SASSERT(is_var(X));
    context& ctx = get_context();
    rational lenX;
    if (!get_length(X, lenX)) {
        TRACE("seq", tout << "enforce length on " << mk_bounded_pp(X, m, 2) << "\n";);
        add_length_to_eqc(X);
        return;
    }
    if (lenX > rational(units.size())) {
        expr_ref le(m_autil.mk_le(mk_len(X), m_autil.mk_int(units.size())), m);
        TRACE("seq", tout << "propagate length on " << mk_bounded_pp(X, m, 2) << "\n";);
        propagate_lit(dep, 0, nullptr, mk_literal(le));
        return;
    }
    SASSERT(lenX.is_unsigned());
    unsigned lX = lenX.get_unsigned();
    if (lX == 0) {
        TRACE("seq", tout << "set empty length " << mk_bounded_pp(X, m, 2) << "\n";);
        set_empty(X);
    }
    else {
        literal lit = mk_eq(m_autil.mk_int(lX), mk_len(X), false);
        if (l_true == ctx.get_assignment(lit)) {
            expr_ref R(m_util.str.mk_concat(lX, units.c_ptr()), m);
            propagate_eq(dep, lit, X, R);
            TRACE("seq", tout << "propagate " << mk_pp(X, m) << " " << R << "\n";);
        }
        else {
            TRACE("seq", tout << "set phase " << mk_pp(X, m) << "\n";);
            ctx.mark_as_relevant(lit);
            ctx.force_phase(lit);
        }
    }
}

bool theory_seq::branch_ternary_variable1() {
    int start = get_context().get_random_value();
    for (unsigned i = 0; i < m_eqs.size(); ++i) {
        eq const& e = m_eqs[(i + start) % m_eqs.size()];
        if (branch_ternary_variable(e) || branch_ternary_variable2(e)) {
            return true;
        }
    }
    return false;
}

bool theory_seq::branch_ternary_variable2() {
    int start = get_context().get_random_value();
    for (unsigned i = 0; i < m_eqs.size(); ++i) {
        eq const& e = m_eqs[(i + start) % m_eqs.size()];
        if (branch_ternary_variable(e, true)) {
            return true;
        }
    }
    return false;
}

bool theory_seq::eq_unit(expr* const& l, expr* const &r) const {
    return l == r || is_unit_nth(l) || is_unit_nth(r);
}

// exists x, y, rs' != empty s.t.  (ls = x ++ rs' ++ y & rs = rs') || (ls = rs' ++ x && rs = y ++ rs')
// TBD: spec comment above doesn't seem to match what this function does.
unsigned_vector theory_seq::overlap(expr_ref_vector const& ls, expr_ref_vector const& rs) {
    SASSERT(!ls.empty() && !rs.empty());
    unsigned_vector result;
    expr_ref l = mk_concat(ls);
    expr_ref r = mk_concat(rs);
    expr_ref pair(m.mk_eq(l,r), m);
    if (m_overlap.find(pair, result)) {
        return result;
    }
    result.reset();
    for (unsigned i = 0; i < ls.size(); ++i) {
        if (eq_unit(ls[i], rs.back())) {
            bool same = rs.size() > i;
            for (unsigned j = 0; same && j < i; ++j) {
                same = eq_unit(ls[j], rs[rs.size() - 1 - i + j]);        
            }
            if (same)
                result.push_back(i+1);
        }
#if 0
        if (eq_unit(ls[i], rs[0])) {
            bool same = ls.size() - i >= rs.size();
            for (unsigned j = 0; same && j < rs.size(); ++j) {
                same = eq_unit(ls[i+j], rs[j]);
            }
            if (same)
                result.push_back(i);
        }
#endif
    }
    m_overlap.insert(pair, result);
    return result;
}

// exists x, y, rs' != empty s.t.  (ls = x ++ rs' ++ y & rs = rs') || (ls = x ++ rs' && rs = rs' ++ y)
unsigned_vector theory_seq::overlap2(expr_ref_vector const& ls, expr_ref_vector const& rs) {
    SASSERT(!ls.empty() && !rs.empty());
    unsigned_vector res;
    expr_ref l = mk_concat(ls);
    expr_ref r = mk_concat(rs);
    expr_ref pair(m.mk_eq(l,r), m);
    if (m_overlap2.find(pair, res)) {
        return res;
    }
    unsigned_vector result;
    for (unsigned i = 0; i < ls.size(); ++i) {
        if (eq_unit(ls[i], rs[0])) {
            bool same = true;
            unsigned j = i+1;
            while (j < ls.size() && j-i < rs.size()) {
                if (!eq_unit(ls[j], rs[j-i])) {
                    same = false;
                    break;
                }
                ++j;
            }
            if (same)
                result.push_back(i);
        }
    }
    m_overlap2.insert(pair, result);
    return result;
}

bool theory_seq::branch_ternary_variable_base(
    dependency* dep, unsigned_vector const& indexes,
    expr* const& x, expr_ref_vector const& xs, expr* const& y1, expr_ref_vector const& ys, expr* const& y2) {
    context& ctx = get_context();
    bool change = false;
    for (auto ind : indexes) {
        TRACE("seq", tout << "ind = " << ind << "\n";);
        expr_ref xs2E(m);
        if (xs.size() > ind) {
            xs2E = m_util.str.mk_concat(xs.size()-ind, xs.c_ptr()+ind);
        }
        else {
            xs2E = m_util.str.mk_empty(m.get_sort(x));
        }
        literal lit1 = mk_literal(m_autil.mk_le(mk_len(y2), m_autil.mk_int(xs.size()-ind)));
        if (ctx.get_assignment(lit1) == l_undef) {
            TRACE("seq", tout << "base case init\n";);
            ctx.mark_as_relevant(lit1);
            ctx.force_phase(lit1);
            change = true;
            continue;
        }
        else if (ctx.get_assignment(lit1) == l_true) {
            TRACE("seq", tout << "base case: true branch\n";);
            literal_vector lits;
            lits.push_back(lit1);
            propagate_eq(dep, lits, y2, xs2E, true);
            if (ind > ys.size()) {
                expr_ref xs1E(m_util.str.mk_concat(ind-ys.size(), xs.c_ptr()), m);
                expr_ref xxs1E = mk_concat(x, xs1E);
                propagate_eq(dep, lits, xxs1E, y1, true);
            }
            else if (ind == ys.size()) {
                propagate_eq(dep, lits, x, y1, true);
            }
            else {
                expr_ref ys1E(m_util.str.mk_concat(ys.size()-ind, ys.c_ptr()), m);
                expr_ref y1ys1E = mk_concat(y1, ys1E);
                propagate_eq(dep, lits, x, y1ys1E, true);
            }
            return true;
        }
        else {
            TRACE("seq", tout << "base case: false branch\n";);
            continue;
        }
    }
    return change;
}

// Equation is of the form x ++ xs = y1 ++ ys ++ y2 where xs, ys are units.
bool theory_seq::branch_ternary_variable(eq const& e, bool flag1) {
    expr_ref_vector xs(m), ys(m);
    expr_ref x(m), y1(m), y2(m);
    bool is_ternary = is_ternary_eq(e.ls(), e.rs(), x, xs, y1, ys, y2, flag1);
    if (!is_ternary) {
        is_ternary = is_ternary_eq(e.rs(), e.ls(), x, xs, y1, ys, y2, flag1);
    }
    if (!is_ternary) {
        return false;
    }

    rational lenX, lenY1, lenY2;
    context& ctx = get_context();
    if (!get_length(x, lenX)) {
        add_length_to_eqc(x);
    }
    if (!get_length(y1, lenY1)) {
        add_length_to_eqc(y1);
    }
    if (!get_length(y2, lenY2)) {
        add_length_to_eqc(y2);
    }

    SASSERT(!xs.empty() && !ys.empty());
    unsigned_vector indexes = overlap(xs, ys);
    if (branch_ternary_variable_base(e.dep(), indexes, x, xs, y1, ys, y2))
        return true;
    
    // x ++ xs = y1 ++ ys ++ y2 => x = y1 ++ ys ++ z, z ++ xs = y2 
    expr_ref xsE = mk_concat(xs);
    expr_ref ysE = mk_concat(ys);
    expr_ref y1ys = mk_concat(y1, ysE);
    expr_ref Z = m_sk.mk_align(y2, xsE, x, y1ys);
    expr_ref ZxsE = mk_concat(Z, xsE);
    expr_ref y1ysZ = mk_concat(y1ys, Z);
    if (indexes.empty()) {
        return false;
#if 0
        TRACE("seq", display_equation(tout << "one case\n", e);
              tout << "xs: " << xs << "\n";
              tout << "ys: " << ys << "\n";);
        literal_vector lits;
        dependency* dep = e.dep();
        propagate_eq(dep, lits, x, y1ysZ, true);
        propagate_eq(dep, lits, y2, ZxsE, true);
#endif
    }

    literal ge = m_ax.mk_ge(mk_len(y2), xs.size());
    dependency* dep = e.dep();
    literal_vector lits;
    switch (ctx.get_assignment(ge)) {
    case l_undef:
        TRACE("seq", tout << "rec case init\n";);
        ctx.mark_as_relevant(ge);
        ctx.force_phase(ge);
        break;
    case l_true:
        TRACE("seq", tout << "true branch\n";);
        TRACE("seq", display_equation(tout, e););
        lits.push_back(ge);
        propagate_eq(dep, lits, x, y1ysZ, true);
        propagate_eq(dep, lits, y2, ZxsE, true);
        break;
    default:
        return branch_ternary_variable_base(e.dep(), indexes, x, xs, y1, ys, y2);
    }
    return true;
}

bool theory_seq::branch_ternary_variable_base2(dependency* dep, unsigned_vector const& indexes,
        expr_ref_vector const& xs, expr* const& x, expr* const& y1, expr_ref_vector const& ys, expr* const& y2) {
    context& ctx = get_context();
    bool change = false;
    for (auto ind : indexes) {
        expr_ref xs1E(m);
        if (ind > 0) {
            xs1E = m_util.str.mk_concat(ind, xs.c_ptr());
        }
        else {
            xs1E = m_util.str.mk_empty(m.get_sort(x));
        }
        literal lit1 = mk_literal(m_autil.mk_le(mk_len(y1), m_autil.mk_int(ind)));
        if (ctx.get_assignment(lit1) == l_undef) {
            TRACE("seq", tout << "base case init\n";);
            ctx.mark_as_relevant(lit1);
            ctx.force_phase(lit1);
            change = true;
            continue;
        }
        else if (ctx.get_assignment(lit1) == l_true) {
            TRACE("seq", tout << "base case: true branch\n";);
            literal_vector lits;
            lits.push_back(lit1);
            propagate_eq(dep, lits, y1, xs1E, true);
            if (xs.size() - ind > ys.size()) {
                expr_ref xs2E(m_util.str.mk_concat(xs.size()-ind-ys.size(), xs.c_ptr()+ind+ys.size()), m);
                expr_ref xs2x = mk_concat(xs2E, x);
                propagate_eq(dep, lits, xs2x, y2, true);
            }
            else if (xs.size() - ind == ys.size()) {
                propagate_eq(dep, lits, x, y2, true);
            }
            else {
                expr_ref ys1E(m_util.str.mk_concat(ys.size()-xs.size()+ind, ys.c_ptr()+xs.size()-ind), m);
                expr_ref ys1y2 = mk_concat(ys1E, y2);
                propagate_eq(dep, lits, x, ys1y2, true);
            }
            return true;
        }
        else {
            TRACE("seq", tout << "base case: false branch\n";);
            continue;
        }
    }
    return change;
}

// Equation is of the form xs ++ x = y1 ++ ys ++ y2 where xs, ys are units.
bool theory_seq::branch_ternary_variable2(eq const& e, bool flag1) {
    expr_ref_vector xs(m), ys(m);
    expr_ref x(m), y1(m), y2(m);
    bool is_ternary = is_ternary_eq2(e.ls(), e.rs(), xs, x, y1, ys, y2, flag1);
    if (!is_ternary) {
        is_ternary = is_ternary_eq2(e.rs(), e.ls(), xs, x, y1, ys, y2, flag1);
    }
    if (!is_ternary) {
        return false;
    }

    rational lenX, lenY1, lenY2;
    context& ctx = get_context();
    if (!get_length(x, lenX)) {
        add_length_to_eqc(x);
    }
    if (!get_length(y1, lenY1)) {
        add_length_to_eqc(y1);
    }
    if (!get_length(y2, lenY2)) {
        add_length_to_eqc(y2);
    }
    SASSERT(!xs.empty() && !ys.empty());
    unsigned_vector indexes = overlap2(xs, ys);
    if (branch_ternary_variable_base2(e.dep(), indexes, xs, x, y1, ys, y2))
        return true;
    
    // xs ++ x = y1 ++ ys ++ y2 => xs ++ z = y1, x = z ++ ys ++ y2 
    expr_ref xsE = mk_concat(xs);
    expr_ref ysE = mk_concat(ys);
    expr_ref ysy2 = mk_concat(ysE, y2);
    expr_ref Z = m_sk.mk_align(x, ysy2, y1, xsE);
    expr_ref xsZ = mk_concat(xsE, Z);
    expr_ref Zysy2 = mk_concat(Z, ysy2);
    if (indexes.empty()) {
        TRACE("seq", tout << "one case\n";);
        TRACE("seq", display_equation(tout, e););
        literal_vector lits;
        dependency* dep = e.dep();
        propagate_eq(dep, lits, x, Zysy2, true);
        propagate_eq(dep, lits, y1, xsZ, true);
    }
    else {
        literal ge = m_ax.mk_ge(mk_len(y1), xs.size());
        if (ctx.get_assignment(ge) == l_undef) {
            TRACE("seq", tout << "rec case init\n";);
            ctx.mark_as_relevant(ge);
            ctx.force_phase(ge);
        }
        else if (ctx.get_assignment(ge) == l_true) {
            TRACE("seq", tout << "true branch\n";);
            TRACE("seq", display_equation(tout, e););
            literal_vector lits;
            lits.push_back(ge);
            dependency* dep = e.dep();
            propagate_eq(dep, lits, x, Zysy2, true);
            propagate_eq(dep, lits, y1, xsZ, true);
        }
        else {
            return branch_ternary_variable_base2(e.dep(), indexes, xs, x, y1, ys, y2);
        }
    }

    return true;
}

bool theory_seq::branch_quat_variable() {
    for (auto const& e : m_eqs) {
        if (branch_quat_variable(e)) {
            return true;
        }
    }
    return false;
}

// Equation is of the form x1 ++ xs ++ x2 = y1 ++ ys ++ y2 where xs, ys are units.
bool theory_seq::branch_quat_variable(eq const& e) {
    expr_ref_vector xs(m), ys(m);
    expr_ref x1_l(m), x2(m), y1_l(m), y2(m);
    bool is_quat = is_quat_eq(e.ls(), e.rs(), x1_l, xs, x2, y1_l, ys, y2);
    if (!is_quat) {
        return false;
    }
    
    rational lenX1, lenX2, lenY1, lenY2;
    context& ctx = get_context();
    if (!get_length(x1_l, lenX1)) {
        add_length_to_eqc(x1_l);
    }
    if (!get_length(y1_l, lenY1)) {
        add_length_to_eqc(y1_l);
    }
    if (!get_length(x2, lenX2)) {
        add_length_to_eqc(x2);
    }
    if (!get_length(y2, lenY2)) {
        add_length_to_eqc(y2);
    }
    SASSERT(!xs.empty() && !ys.empty());
    
    xs.push_back(x2);
    expr_ref xsx2 = mk_concat(xs);
    ys.push_back(y2);
    expr_ref ysy2 = mk_concat(ys);
    expr_ref x1(x1_l, m);
    expr_ref y1(y1_l, m);
    expr_ref sub(mk_sub(mk_len(x1_l), mk_len(y1_l)), m);
    literal le = m_ax.mk_le(sub, 0);
    literal_vector lits;
    if (ctx.get_assignment(le) == l_undef) {
        TRACE("seq", tout << "init branch\n";);
        TRACE("seq", display_equation(tout, e););
        ctx.mark_as_relevant(le);
        ctx.force_phase(le);
    }
    else if (ctx.get_assignment(le) == l_false) {
        // |x1| > |y1| => x1 = y1 ++ z1, z1 ++ xs ++ x2 = ys ++ y2
        TRACE("seq", tout << "false branch\n";);
        TRACE("seq", display_equation(tout, e););
        expr_ref Z1 = m_sk.mk_align(ysy2, xsx2, x1, y1);
        expr_ref y1Z1 = mk_concat(y1, Z1);
        expr_ref Z1xsx2 = mk_concat(Z1, xsx2);
        lits.push_back(~le);
        dependency* dep = e.dep();
        propagate_eq(dep, lits, x1, y1Z1, true);
        propagate_eq(dep, lits, Z1xsx2, ysy2, true);
    }
    else if (ctx.get_assignment(le) == l_true) {
        // |x1| <= |y1| => x1 ++ z2 = y1, xs ++ x2 = z2 ++ ys ++ y2
        TRACE("seq", tout << "true branch\n";);
        TRACE("seq", display_equation(tout, e););
        expr_ref Z2 = m_sk.mk_align(xsx2, ysy2, y1, x1);
        expr_ref x1Z2 = mk_concat(x1, Z2);
        expr_ref Z2ysy2 = mk_concat(Z2, ysy2);
        lits.push_back(le);
        dependency* dep = e.dep();
        propagate_eq(dep, lits, x1Z2, y1, true);
        propagate_eq(dep, lits, xsx2, Z2ysy2, true);
    }
    return true;
}

void theory_seq::len_offset(expr* e, rational val) {
    context & ctx = get_context();
    expr *l1 = nullptr, *l2 = nullptr, *l21 = nullptr, *l22 = nullptr;
    rational fact;
    if (m_autil.is_add(e, l1, l2) && m_autil.is_mul(l2, l21, l22) &&
        m_autil.is_numeral(l21, fact) && fact.is_minus_one()) {
        if (ctx.e_internalized(l1) && ctx.e_internalized(l22)) {
            enode* r1 = get_root(l1), *n1 = r1;
            enode* r2 = get_root(l22), *n2 = r2;
            expr *e1 = nullptr, *e2 = nullptr;
            do {
                if (m_util.str.is_length(n1->get_owner(), e1))
                    break;
                n1 = n1->get_next();               
            }
            while (n1 != r1);
            do {
                if (m_util.str.is_length(n2->get_owner(), e2)) 
                    break;
                n2 = n2->get_next();                
            }
            while (n2 != r2);
            obj_map<enode, int> tmp;
            if (m_util.str.is_length(n1->get_owner(), e1)
                && m_util.str.is_length(n2->get_owner(), e2) &&                
                m_len_offset.find(r1, tmp)) {
                tmp.insert(r2, val.get_int32());
                m_len_offset.insert(r1, tmp);
                TRACE("seq", tout << "a length pair: " << mk_pp(e1, m) << ", " << mk_pp(e2, m) << "\n";);
                return;
            }
        }
    }
}

// Find the length offset from the congruence closure core
void theory_seq::prop_arith_to_len_offset() {
    context & ctx = get_context();
    obj_hashtable<enode> const_set;
    ptr_vector<enode>::const_iterator it  = ctx.begin_enodes();
    ptr_vector<enode>::const_iterator end = ctx.end_enodes();
    for (; it != end; ++it) {
        enode * root = (*it)->get_root();
        rational val;
        if (m_autil.is_numeral(root->get_owner(), val) && val.is_neg()) {
            if (const_set.contains(root)) continue;
            const_set.insert(root);
            TRACE("seq", tout << "offset: " << mk_pp(root->get_owner(), m) << "\n";);
            enode *next = root->get_next();
            while (next != root) {
                TRACE("seq", tout << "eqc: " << mk_pp(next->get_owner(), m) << "\n";);
                len_offset(next->get_owner(), val);
                next = next->get_next();
            }
        }
    }
}

int theory_seq::find_fst_non_empty_idx(expr_ref_vector const& xs) {
    context & ctx = get_context();    
    for (unsigned i = 0; i < xs.size(); ++i) {
        expr* x = xs[i];
        if (!is_var(x)) return -1;
        expr_ref e = mk_len(x);
        if (ctx.e_internalized(e)) {
            enode* root = ctx.get_enode(e)->get_root();
            rational val;
            if (m_autil.is_numeral(root->get_owner(), val) && val.is_zero()) {
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

void theory_seq::find_max_eq_len(expr_ref_vector const& ls, expr_ref_vector const& rs) {
    context& ctx = get_context();
    if (ls.size() >= 2 && rs.size() >= 2) {
        expr_ref len1(m_autil.mk_int(0), m), len2(m_autil.mk_int(0), m);
        int l_fst = find_fst_non_empty_idx(ls);
        int r_fst = find_fst_non_empty_idx(rs);
        if (l_fst<0 || r_fst<0)
            return;
        unsigned j = 2 + l_fst;
        rational lo1(-1), hi1(-1), lo2(-1), hi2(-1);
        if (j >= ls.size()) {
            lo1 = 0;
            hi1 = 0;
        }
        while (j < ls.size()) {
            rational lo(-1), hi(-1);
            if (m_util.str.is_unit(ls.get(j))) {
                lo = 1;
                hi = 1;
            }
            else {
                expr_ref len_s = mk_len(ls.get(j));
                lower_bound(len_s, lo);
                upper_bound(len_s, hi);
            }
            if (!lo.is_minus_one()) {
                if (lo1.is_minus_one())
                    lo1 = lo;
                else
                    lo1 += lo;
            }
            if (!hi.is_minus_one()) {
                if (hi1.is_minus_one())
                    hi1 = hi;
                else if (hi1.is_nonneg())
                    hi1 += hi;
            }
            else {
                hi1 = rational(-2);
            }
            len1 = mk_add(len1, mk_len(ls.get(j)));
            j++;
        }
        j = 2 + r_fst;
        if (j >= rs.size()) {
            lo2 = 0;
            hi2 = 0;
        }
        while (j < rs.size()) {
            rational lo(-1), hi(-1);
            if (m_util.str.is_unit(rs.get(j))) {
                lo = 1;
                hi = 1;
            }
            else {
                expr_ref len_s = mk_len(rs.get(j));
                lower_bound(len_s, lo);
                upper_bound(len_s, hi);
            }
            if (!lo.is_minus_one()) {
                if (lo2.is_minus_one())
                    lo2 = lo;
                else
                    lo2 += lo;
            }
            if (!hi.is_minus_one()) {
                if (hi2.is_minus_one())
                    hi2 = hi;
                else if (hi1.is_nonneg())
                    hi2 += hi;
            }
            else {
                hi2 = rational(-2);
            }
            len2 = mk_add(len2, mk_len(rs.get(j)));
            j++;
        }
        if (m_autil.is_numeral(len1) && m_autil.is_numeral(len2))
            return;
        TRACE("seq", tout << lo1 << ", " << hi1 << ", " << lo2 << ", " << hi2 << "\n";);
        if (!lo1.is_neg() && !hi2.is_neg() && lo1 > hi2)
            return;
        if (!lo2.is_neg() && !hi1.is_neg() && lo2 > hi1)
            return;

        literal lit1 = null_literal;
        if (hi1.is_zero()) {
            if (!is_var(rs[1 + r_fst]))
                return;
            lit1 = mk_literal(m_autil.mk_le(len2, len1));
            TRACE("seq", tout << mk_pp(len1, m) << " >= " << mk_pp(len2, m) << "\n";);
        }
        else if (hi2.is_zero()) {
            if (!is_var(ls[1 + l_fst]))
                return;
            lit1 = mk_literal(m_autil.mk_le(len1, len2));
            TRACE("seq", tout << mk_pp(len1, m) << " <= " << mk_pp(len2, m) << "\n";);
        }
        else {
            lit1 = mk_eq(len1, len2, false);
            TRACE("seq", tout << mk_pp(len1, m) << " = " << mk_pp(len2, m) << "\n";);
        }
        if (ctx.get_assignment(lit1) == l_undef) {
            ctx.mark_as_relevant(lit1);
            ctx.force_phase(lit1);
        }
    }
}


bool theory_seq::branch_variable_eq() {
    context& ctx = get_context();
    unsigned sz = m_eqs.size();
    int start = ctx.get_random_value();

    for (unsigned i = 0; i < sz; ++i) {
        unsigned k = (i + start) % sz;
        eq const& e = m_eqs[k];

        if (branch_variable_eq(e)) {
            TRACE("seq", tout << "branch variable\n";);
            return true;
        }
    }
    return ctx.inconsistent();
}

bool theory_seq::branch_variable_eq(eq const& e) {
    unsigned id = e.id();
    unsigned s = find_branch_start(2*id);
    TRACE("seq", tout << s << " " << id << ": " << e.ls() << " = " << e.rs() << "\n";);
    bool found = find_branch_candidate(s, e.dep(), e.ls(), e.rs());
    insert_branch_start(2*id, s);
    if (found) {
        return true;
    }
    s = find_branch_start(2*id + 1);
    found = find_branch_candidate(s, e.dep(), e.rs(), e.ls());
    insert_branch_start(2*id + 1, s);
    
    return found;
}

void theory_seq::insert_branch_start(unsigned k, unsigned s) {
    m_branch_start.insert(k, s);
    m_trail_stack.push(pop_branch(k));
}

unsigned theory_seq::find_branch_start(unsigned k) {
    unsigned s = 0;
    if (m_branch_start.find(k, s)) {
        return s;
    }
    return 0;
}

expr_ref_vector theory_seq::expand_strings(expr_ref_vector const& es) {
    expr_ref_vector ls(m);
    for (expr* e : es) {
        zstring s;
        if (m_util.str.is_string(e, s)) {
            for (unsigned i = 0; i < s.length(); ++i) {
                ls.push_back(m_util.str.mk_unit(m_util.str.mk_char(s, i)));
            }
        }
        else {
            ls.push_back(e);
        }
    }
    return ls;
}

bool theory_seq::find_branch_candidate(unsigned& start, dependency* dep, expr_ref_vector const& _ls, expr_ref_vector const& _rs) {
    expr_ref_vector ls = expand_strings(_ls);
    expr_ref_vector rs = expand_strings(_rs);

    if (ls.empty()) {
        return false;
    }
    expr* l = ls.get(0);

    if (!is_var(l)) {
        return false;
    }

    TRACE("seq", tout << mk_pp(l, m) << ": " << get_context().get_scope_level() << " - start:" << start << "\n";);

    expr_ref v0(m);
    v0 = m_util.str.mk_empty(m.get_sort(l));
    if (can_be_equal(ls.size() - 1, ls.c_ptr() + 1, rs.size(), rs.c_ptr())) {
        if (l_false != assume_equality(l, v0)) {
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
        if (!can_be_equal(ls.size() - 1, ls.c_ptr() + 1, rs.size() - j - 1, rs.c_ptr() + j + 1)) {
            continue;
        }
        v0 = mk_concat(j + 1, rs.c_ptr());
        if (l_false != assume_equality(l, v0)) {
            TRACE("seq", tout << mk_pp(l, m) << " " << v0 << "\n";);
            ++start;
            return true;
        }
    }

    bool all_units = true;
    for (expr* r : rs) {
        if (!m_util.str.is_unit(r)) {
            all_units = false;
            break;
        }
    }
    if (all_units) {
        context& ctx = get_context();
        literal_vector lits;
        lits.push_back(~mk_eq_empty(l));
        for (unsigned i = 0; i < rs.size(); ++i) {
            if (can_be_equal(ls.size() - 1, ls.c_ptr() + 1, rs.size() - i - 1, rs.c_ptr() + i + 1)) {
                v0 = mk_concat(i + 1, rs.c_ptr());
                lits.push_back(~mk_eq(l, v0, false));
            }
        }
        for (literal lit : lits) {
            switch (ctx.get_assignment(lit)) {
            case l_true:  break;
            case l_false: start = 0; return true;
            case l_undef: ctx.force_phase(~lit); start = 0; return true;
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


lbool theory_seq::assume_equality(expr* l, expr* r) {
    context& ctx = get_context();
    if (m_exclude.contains(l, r)) {
        return l_false;
    }

    expr_ref eq(m.mk_eq(l, r), m);
    m_rewrite(eq);
    if (m.is_true(eq)) {
        return l_true;
    }
    if (m.is_false(eq)) {
        return l_false;
    }

    enode* n1 = ensure_enode(l);
    enode* n2 = ensure_enode(r);
    if (n1->get_root() == n2->get_root()) {
        TRACE("seq", tout << mk_pp(l, m) << " = " << mk_pp(r, m) << " roots eq\n";);
        return l_true;
    }
    if (ctx.is_diseq(n1, n2)) {
        TRACE("seq", tout << mk_pp(l, m) << " = " << mk_pp(r, m) << " is_diseq\n";);
        return l_false;
    }
    if (false && ctx.is_diseq_slow(n1, n2)) {
        return l_false;
    }
    ctx.mark_as_relevant(n1);
    ctx.mark_as_relevant(n2);
    if (!ctx.assume_eq(n1, n2)) {
        TRACE("seq", tout << mk_pp(l, m) << " = " << mk_pp(r, m) << " can't assume\n";);
        return l_false;
    }
    lbool res = ctx.get_assignment(mk_eq(l, r, false));
    TRACE("seq", tout << mk_pp(l, m) << " = " << mk_pp(r, m) << " literal assigned " << res << "\n";);
    return res;
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
        mk_decompose(seq, head, tail);
        elems.push_back(head);
        seq = tail;
    }
    expr_ref emp(m_util.str.mk_empty(m.get_sort(e)), m);
    elems.push_back(seq);
    tail = mk_concat(elems.size(), elems.c_ptr());
    // len(e) >= low => e = tail;
    expr_ref lo_e(m_autil.mk_numeral(lo, true), m);
    expr_ref len_e_ge_lo(m_autil.mk_ge(mk_len(e), lo_e), m);
    literal low = mk_literal(len_e_ge_lo);
    add_axiom(~low, mk_seq_eq(e, tail));
    expr_ref len_e = mk_len(e);
    if (upper_bound(len_e, hi)) {
        // len(e) <= hi => len(tail) <= hi - lo
        expr_ref high1(m_autil.mk_le(len_e, m_autil.mk_numeral(hi, true)), m);
        if (hi == lo) {
            add_axiom(~mk_literal(high1), mk_seq_eq(seq, emp));
        }
        else {
            expr_ref high2(m_autil.mk_le(mk_len(seq), m_autil.mk_numeral(hi-lo, true)), m);
            add_axiom(~mk_literal(high1), mk_literal(high2));
        }
    }
    else {
        assume_equality(seq, emp);
    }
    return true;
}


bool theory_seq::check_length_coherence(expr* e) {
    if (is_var(e) && m_rep.is_root(e)) {
        if (!check_length_coherence0(e)) {
            expr_ref emp(m_util.str.mk_empty(m.get_sort(e)), m);
            expr_ref head(m), tail(m);
            // e = emp \/ e = unit(head.elem(e))*tail(e)
            mk_decompose(e, head, tail);
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
        expr_ref emp(m_util.str.mk_empty(m.get_sort(e)), m);
        lbool r = l_false;
        bool p = propagate_length_coherence(e);

        if (!p) {
            r = assume_equality(e, emp);
        }

        if (p || r != l_false) {
            if (!get_context().at_base_level()) {
                m_trail_stack.push(push_replay(alloc(replay_length_coherence, m, e)));
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
        enode* n = ensure_enode(e);
        enode* r = n->get_root();
        if (r != n && has_length(r->get_owner())) {
            continue;
        }
        if (add_length_to_eqc(e)) {
            change = true;
        }
    }
    return change;
}

bool theory_seq::reduce_length_eq() {
    context& ctx = get_context();
    int start = ctx.get_random_value();

    for (unsigned i = 0; !ctx.inconsistent() && i < m_eqs.size(); ++i) {
        eq const& e = m_eqs[(i + start) % m_eqs.size()];
        if (reduce_length_eq(e.ls(), e.rs(), e.dep())) {
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

/**
   match X abc = defg Y, for abc, defg non-empty
*/

bool theory_seq::is_binary_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, expr_ref& x, ptr_vector<expr>& xs, ptr_vector<expr>& ys, expr_ref& y) {
    if (ls.size() > 1 && is_var(ls[0]) &&
        rs.size() > 1 && is_var(rs.back())) {
        xs.reset();
        ys.reset();
        x = ls[0];
        y = rs.back();
        for (unsigned i = 1; i < ls.size(); ++i) {
            if (!m_util.str.is_unit(ls[i])) return false;
        }
        for (unsigned i = 0; i < rs.size()-1; ++i) {
            if (!m_util.str.is_unit(rs[i])) return false;
        }
        xs.append(ls.size()-1, ls.c_ptr() + 1);
        ys.append(rs.size()-1, rs.c_ptr());
        return true;
    }
    return false;
}

/*
  match: Description TBD
*/

bool theory_seq::is_quat_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, 
                            expr_ref& x1, expr_ref_vector& xs, expr_ref& x2, 
                            expr_ref& y1, expr_ref_vector& ys, expr_ref& y2) {
    if (ls.size() > 1 && is_var(ls[0]) && is_var(ls.back()) &&
        rs.size() > 1 && is_var(rs[0]) && is_var(rs.back())) {
        unsigned l_start = 1;
        for (; l_start < ls.size()-1; ++l_start) {
            if (m_util.str.is_unit(ls[l_start])) break;
        }
        if (l_start == ls.size()-1) return false;
        unsigned l_end = l_start;
        for (; l_end < ls.size()-1; ++l_end) {
            if (!m_util.str.is_unit(ls[l_end])) break;
        }
        --l_end;
        unsigned r_start = 1;
        for (; r_start < rs.size()-1; ++r_start) {
            if (m_util.str.is_unit(rs[r_start])) break;
        }
        if (r_start == rs.size()-1) return false;
        unsigned r_end = r_start;
        for (; r_end < rs.size()-1; ++r_end) {
            if (!m_util.str.is_unit(rs[r_end])) break;
        }
        --r_end;
        for (unsigned i = l_start; i < l_end+1; ++i) {
            if (!m_util.str.is_unit(ls[i])) return false;
        }
        for (unsigned i = r_start; i < r_end+1; ++i) {
            if (!m_util.str.is_unit(rs[i])) return false;
        }
        xs.reset();
        xs.append(l_end-l_start+1, ls.c_ptr()+l_start);
        x1 = m_util.str.mk_concat(l_start, ls.c_ptr());
        x2 = m_util.str.mk_concat(ls.size()-l_end-1, ls.c_ptr()+l_end+1);
        ys.reset();
        ys.append(r_end-r_start+1, rs.c_ptr()+r_start);
        y1 = m_util.str.mk_concat(r_start, rs.c_ptr());
        y2 = m_util.str.mk_concat(rs.size()-r_end-1, rs.c_ptr()+r_end+1);
        return true;
    }
    return false;
}

/*
  match: Description TBD
*/

bool theory_seq::is_ternary_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, 
                               expr_ref& x, expr_ref_vector& xs, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2, bool flag1) {
    if (ls.size() > 1 && (is_var(ls[0]) || flag1) &&
        rs.size() > 1 && is_var(rs[0]) && is_var(rs.back())) {
        unsigned l_start = ls.size()-1;
        for (; l_start > 0; --l_start) {
            if (!m_util.str.is_unit(ls[l_start])) break;
        }
        if (l_start == ls.size()-1) return false;
        ++l_start;
        unsigned r_end = rs.size()-2;
        for (; r_end > 0; --r_end) {
            if (m_util.str.is_unit(rs[r_end])) break;
        }
        if (r_end == 0) return false;
        unsigned r_start = r_end;
        for (; r_start > 0; --r_start) {
            if (!m_util.str.is_unit(rs[r_start])) break;
        }
        ++r_start;
        for (unsigned i = l_start; i < ls.size(); ++i) {
            if (!m_util.str.is_unit(ls[i])) return false;
        }
        for (unsigned i = r_start; i < r_end+1; ++i) {
            if (!m_util.str.is_unit(rs[i])) return false;
        }
        xs.reset();
        xs.append(ls.size()-l_start, ls.c_ptr()+l_start);
        x = m_util.str.mk_concat(l_start, ls.c_ptr());
        ys.reset();
        ys.append(r_end-r_start+1, rs.c_ptr()+r_start);
        y1 = m_util.str.mk_concat(r_start, rs.c_ptr());
        y2 = m_util.str.mk_concat(rs.size()-r_end-1, rs.c_ptr()+r_end+1);
        return true;
    }
    return false;
}

/*
  match: Description TBD
*/

bool theory_seq::is_ternary_eq2(expr_ref_vector const& ls, expr_ref_vector const& rs, 
                                expr_ref_vector& xs, expr_ref& x, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2, bool flag1) {
    if (ls.size() > 1 && (is_var(ls.back()) || flag1) &&
        rs.size() > 1 && is_var(rs[0]) && is_var(rs.back())) {
        unsigned l_start = 0;
        for (; l_start < ls.size()-1; ++l_start) {
            if (!m_util.str.is_unit(ls[l_start])) break;
        }
        if (l_start == 0) return false;
        unsigned r_start = 1;
        for (; r_start < rs.size()-1; ++r_start) {
            if (m_util.str.is_unit(rs[r_start])) break;
        }
        if (r_start == rs.size()-1) return false;
        unsigned r_end = r_start;
        for (; r_end < rs.size()-1; ++r_end) {
            if (!m_util.str.is_unit(rs[r_end])) break;
        }
        --r_end;
        for (unsigned i = 0; i < l_start; ++i) {
            if (!m_util.str.is_unit(ls[i])) return false;
        }
        for (unsigned i = r_start; i < r_end+1; ++i) {
            if (!m_util.str.is_unit(rs[i])) return false;
        }
        xs.reset();
        xs.append(l_start, ls.c_ptr());
        x = m_util.str.mk_concat(ls.size()-l_start, ls.c_ptr()+l_start);
        ys.reset();
        ys.append(r_end-r_start+1, rs.c_ptr()+r_start);
        y1 = m_util.str.mk_concat(r_start, rs.c_ptr());
        y2 = m_util.str.mk_concat(rs.size()-r_end-1, rs.c_ptr()+r_end+1);
        return true;
    }
    return false;
}

/**
   nth(x,idx) = rhs => 
   x = pre(x, idx) ++ unit(rhs) ++ post(x, idx + 1)
   NB: need 0 <= idx < len(rhs)   
*/
bool theory_seq::solve_nth_eq2(expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* deps) {
    expr* s = nullptr, *idx = nullptr;
    if (ls.size() == 1 && m_util.str.is_nth_i(ls[0], s, idx)) {
        rational r;
        bool idx_is_zero = m_autil.is_numeral(idx, r) && r.is_zero();
        expr_ref_vector ls1(m), rs1(m); 
        expr_ref idx1(m_autil.mk_add(idx, m_autil.mk_int(1)), m);
        m_rewrite(idx1);
        expr_ref rhs(m_util.str.mk_concat(rs.size(), rs.c_ptr()), m);
        ls1.push_back(s);        
        if (!idx_is_zero) rs1.push_back(m_sk.mk_pre(s, idx)); 
        rs1.push_back(m_util.str.mk_unit(rhs)); 
        rs1.push_back(m_sk.mk_post(s, idx1));
        TRACE("seq", tout << ls1 << "\n"; tout << rs1 << "\n";);
        m_eqs.push_back(eq(m_eq_id++, ls1, rs1, deps));        
        return true;
    }   
    return false;
}

/**
   match 
   x = unit(nth_i(x,0)) + unit(nth_i(x,1)) + .. + unit(nth_i(x,k-1))
 */

bool theory_seq::solve_nth_eq1(expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* dep) {
    if (solve_nth_eq2(ls, rs, dep)) {
        return true;
    }
    if (ls.size() != 1 || rs.size() <= 1) {
        return false;
    }
    expr* l = ls.get(0);
    rational val;
    if (!get_length(l, val) || val != rational(rs.size())) {
        return false;
    }
    for (unsigned i = 0; i < rs.size(); ++i) {
        unsigned k = 0;
        expr* ru = nullptr, *r = nullptr;
        if (m_util.str.is_unit(rs.get(i), ru) && m_util.str.is_nth_i(ru, r, k) && k == i && r == l) {
            continue;
        }
        return false;
    }
    add_solution(l, mk_concat(rs, m.get_sort(l)), dep);
    return true;
}

