/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bound_simplifier.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2023-01-22

Description:

Extract bounds for sub-expressions and use the bounds for propagation and simplification.
It applies the simplificaitons from the bounds_propagator and it applies nested rewriting
of sub-expressions based on bounds information. Initially, rewriting amounts to eliminating 
occurrences of mod N.

From the description of propagate_ineqs_tactic:

     - Propagate bounds using the bound_propagator.
     - Eliminate subsumed inequalities.
       For example:
          x - y >= 3
          can be replaced with true if we know that
          x >= 3 and y <= 0

     - Convert inequalities of the form p <= k and p >= k into p = k,
       where p is a polynomial and k is a constant.

    This strategy assumes the input is in arith LHS mode.
    This can be achieved by using option :arith-lhs true in the
    simplifier.

--*/


#include "ast/ast_pp.h"
#include "ast/simplifiers/bound_simplifier.h"
#include "ast/rewriter/rewriter_def.h"

struct bound_simplifier::rw_cfg : public default_rewriter_cfg {
    bound_simplifier& s;
    rw_cfg(bound_simplifier& s): s(s) {}
    br_status reduce_app(func_decl* f, unsigned num_args, expr * const* args, expr_ref& result, proof_ref& pr) {
        return s.reduce_app(f, num_args, args, result, pr);
    }
};  

struct bound_simplifier::rw : public rewriter_tpl<rw_cfg> {
    rw_cfg m_cfg;
    rw(bound_simplifier& s):
        rewriter_tpl<rw_cfg>(s.m, false, m_cfg),
        m_cfg(s) {
    }
};    

br_status bound_simplifier::reduce_app(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result, proof_ref& pr) {
    rational N, hi, lo;
    if (a.is_mod(f) && num_args == 2 && a.is_numeral(args[1], N)) {
        auto& im = m_interval;
        scoped_dep_interval i(im);
        expr* x = args[0];
        get_bounds(x, i);
        if (im.upper_is_inf(i) || im.lower_is_inf(i))
            return BR_FAILED;
        if (im.upper_is_open(i) || im.lower_is_open(i))
            return BR_FAILED;
        lo = im.lower(i);
        hi = im.upper(i);
        if (hi - lo >= N)
            return BR_FAILED;
        if (N > hi && lo >= 0) {
            result = x;
            TRACE("propagate-ineqs", tout << expr_ref(m.mk_app(f, num_args, args), m) << " -> " << result << "\n");
            return BR_DONE;
        }
        if (2 * N > hi && lo >= N) {
            result = a.mk_sub(x, a.mk_int(N));
            m_rewriter(result);
            TRACE("propagate-ineqs", tout << expr_ref(m.mk_app(f, num_args, args), m) << " -> " << result << "\n");
            return BR_DONE;
        }
        IF_VERBOSE(2, verbose_stream() << "potentially missed simplification: " << mk_pp(x, m) << " " << lo << " " << hi << " not reduced\n");
    }

    expr_ref_buffer new_args(m);
    expr_ref new_arg(m);
    bool change = false;
    for (unsigned i = 0; i < num_args; ++i) {
        expr* arg = args[i];
        change = reduce_arg(arg, new_arg) || change;
        new_args.push_back(new_arg);
    }
    if (!change)
        return BR_FAILED;

    result = m.mk_app(f, num_args, new_args.data());

    return BR_DONE;
}

bool bound_simplifier::reduce_arg(expr* arg, expr_ref& result) {
    result = arg;
    expr* x, *y;
    rational N, lo, hi;
    bool strict;
    if ((a.is_le(arg, x, y) && a.is_numeral(y, N)) ||
        (a.is_ge(arg, y, x) && a.is_numeral(y, N))) {

        if (has_upper(x, hi, strict) && !strict && N >= hi) {
            result = m.mk_true();
            return true;
        }
        if (has_lower(x, lo, strict) && !strict && N < lo) {
            result = m.mk_false();
            return true;
        }
        return false;
    }
    
    if ((a.is_le(arg, y, x) && a.is_numeral(y, N)) ||
        (a.is_ge(arg, x, y) && a.is_numeral(y, N))) {
        if (has_lower(x, lo, strict) && !strict && N <= lo) {
            result = m.mk_true();
            return true;
        }
        if (has_upper(x, hi, strict) && !strict && N > hi) {
            result = m.mk_false();
            return true;
        }
        return false;
    }
    return false;
}

void bound_simplifier::reduce() {
    
    bool updated = true, found_bound = false;
    for (unsigned i = 0; i < 5 && updated; ++i) {
        updated = false;
        found_bound = false;
        reset();
        for (unsigned idx : indices()) {
            if (insert_bound(m_fmls[idx])) {
                m_fmls.update(idx, dependent_expr(m, m.mk_true(), nullptr, nullptr));
                found_bound = true;
            }
        }
        if (!found_bound)
            break;
        
        for (unsigned idx : indices()) 
            tighten_bound(m_fmls[idx]);
        
        bp.propagate();
        
        proof_ref pr(m);
        expr_ref r(m);
        rw rw(*this);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            if (d.pr())
                continue;
            rw(d.fml(), r, pr);
            if (r != d.fml()) {
                m_fmls.update(idx, dependent_expr(m, r, mp(d.pr(), pr), d.dep()));
                ++m_num_reduced;
                updated = true;
            }
        }
        restore_bounds();
    }
}

// generalization to summations?

bool bound_simplifier::is_offset(expr* e, expr* x, rational& n) {
    expr* y, *z;
    if (a.is_add(e, y, z)) {
        if (x != y)
            std::swap(y, z);
        return x == y && a.is_numeral(z, n);
    }
    return false;
}

bool bound_simplifier::insert_bound(dependent_expr const& de) {
    if (de.pr())
        return false;
    if (de.dep())
        return false;
    rational n, n0;
    expr* x, *y, *f = de.fml();

    if (m.is_eq(f, x, y)) {
        if (a.is_numeral(y))
            std::swap(x, y);
        if (a.is_numeral(x, n)) {
            assert_lower(y, n, false);
            assert_upper(y, n, false);
            return true;
        }
    }
    else if (a.is_le(f, x, y)) {
        if (a.is_numeral(x, n)) 
            assert_lower(y, n, false);
        else if (a.is_numeral(y, n))
            assert_upper(x, n, false);
        else 
            return false;
        return true;
    }
    else if (a.is_ge(f, x, y)) {
        if (a.is_numeral(x, n))
            assert_upper(y, n, false);
        else if (a.is_numeral(y, n))
            assert_lower(x, n, false);
        else 
            return false;
        return true;
    }
    else if (m.is_not(f, f)) {
        if (a.is_le(f, x, y)) {
            if (a.is_numeral(x, n)) 
                assert_upper(y, n, true);
            else if (a.is_numeral(y, n))
                assert_lower(x, n, true);
            else
                return false;
            return true;
        }
        else if (a.is_ge(f, x, y)) {
            if (a.is_numeral(x, n))
                assert_lower(y, n, true);
            else if (a.is_numeral(y, n))
                assert_upper(x, n, true);
            else 
                return false;
            return true;
        }
    }
    return false;
}

void bound_simplifier::tighten_bound(dependent_expr const& de) {
    if (de.pr())
        return;
    if (de.dep())
        return;
    rational n, k;
    expr* x, *y, *f = de.fml();
    expr* z, * u, * v, * w;
    bool strict;
    if (a.is_le(f, x, y)) {
        // x <= (x + k) mod N && x >= 0 -> x + k < N
        if (a.is_mod(y, z, u) && a.is_numeral(u, n) && has_lower(x, k, strict) && k >= 0 && is_offset(z, x, k) && k > 0 && k < n) 
            assert_upper(x, n - k, true);
        // x <= (x + y) mod N && x >= 0 && 0 <= y < N => x + y < N
        if (a.is_mod(y, z, u) && a.is_numeral(u, n) && n > 0) {
            assert_upper(x, n, true);
            if (has_lower(x, k, strict) && k >= 0 && a.is_add(z, v, w)) {
                if (x == v && has_upper(w, k, strict) && k < n)
                    assert_upper(z, n, true);
                if (x == w && has_upper(v, k, strict) && k < n)
                    assert_upper(z, n, true);
            }
        }
    }


    // x != k, k <= x -> k < x
    if (m.is_not(f, f) && m.is_eq(f, x, y)) {
        if (a.is_numeral(x))
            std::swap(x, y);
        if (a.is_numeral(y, n)) {
            scoped_dep_interval i(m_interval);
            get_bounds(x, i);
            scoped_mpq k(nm);
            if (!i.m().lower_is_inf(i) && !i.m().lower_is_open(i) && i.m().lower(i) == n)
                assert_lower(x, n, true);
            else if (!i.m().upper_is_inf(i) && !i.m().upper_is_open(i) && i.m().upper(i) == n)
                assert_upper(x, n, true);
        }
    }

}

void bound_simplifier::assert_upper(expr* x, rational const& n, bool strict) {
    scoped_mpq c(nm);
    nm.set(c, n.to_mpq());
    TRACE("propagate-ineqs", tout << to_var(x) << ": " << mk_pp(x, m) << (strict ? " < " : " <= ") << n << "\n");
    bp.assert_upper(to_var(x), c, strict);
}


void bound_simplifier::assert_lower(expr* x, rational const& n, bool strict) {
    scoped_mpq c(nm);
    nm.set(c, n.to_mpq());
    TRACE("propagate-ineqs", tout <<  to_var(x) << ": " << mk_pp(x, m) << (strict ? " > " : " >= ") << n << "\n");
    bp.assert_lower(to_var(x), c, strict);
}

bool bound_simplifier::has_lower(expr* x, rational& n, bool& strict) {
    scoped_dep_interval i(m_interval);
    get_bounds(x, i);
    if (m_interval.lower_is_inf(i))
        return false;
    strict = m_interval.lower_is_open(i);
    n = m_interval.lower(i);
    TRACE("propagate-ineqs", tout <<  to_var(x) << ": " << mk_pp(x, m) << (strict ? " > " : " >= ") << n << "\n");
    return true;
}

bool bound_simplifier::has_upper(expr* x, rational& n, bool& strict) {
    scoped_dep_interval i(m_interval);
    get_bounds(x, i);
    if (m_interval.upper_is_inf(i))
        return false;
    strict = m_interval.upper_is_open(i);
    n = m_interval.upper(i);
    TRACE("propagate-ineqs", tout << to_var(x) << ": " << mk_pp(x, m) << (strict ? " < " : " <= ") << n << "\n");
    return true;  
}

void bound_simplifier::get_bounds(expr* x, scoped_dep_interval& i) {    
    auto& im = m_interval;    
    im.reset(i);
    scoped_dep_interval arg_i(im);
    rational n;
    if (a.is_numeral(x, n)) {
        im.set_value(i, n);
        return;
    }

    if (is_var(x)) {
        unsigned v = to_var(x);
        bool strict;
        if (bp.has_upper(v)) {
            im.set_upper(i, bp.upper(v, strict));
            im.set_upper_is_inf(i, false);
            im.set_upper_is_open(i, strict);
            
        }
        if (bp.has_lower(v)) {
            im.set_lower(i, bp.lower(v, strict));
            im.set_lower_is_inf(i, false);
            im.set_lower_is_open(i, strict);            
        }
    }

    if (a.is_add(x)) {
        scoped_dep_interval tmp_i(im), sum_i(im);
        im.set_value(sum_i, rational::zero());
        for (expr* arg : *to_app(x)) {
            get_bounds(arg, arg_i);
            im.add(sum_i, arg_i, tmp_i);
            im.set<dep_intervals::without_deps>(sum_i, tmp_i);
        }
        im.intersect <dep_intervals::without_deps>(i, sum_i, i);
    }

    if (a.is_mul(x)) {
        scoped_dep_interval tmp_i(im);
        im.set_value(tmp_i, rational::one());
        for (expr* arg : *to_app(x)) {
            get_bounds(arg, arg_i);
            im.mul(tmp_i, arg_i, tmp_i);
        }
        im.intersect <dep_intervals::without_deps>(i, tmp_i, i);
    }

    expr* y, * z, * u, * v;
    if (a.is_mod(x, y, z) && a.is_numeral(z, n) && n > 0) {
        scoped_dep_interval tmp_i(im);
        im.set_lower_is_inf(tmp_i, false);
        im.set_lower_is_open(tmp_i, false);
        im.set_lower(tmp_i, mpq(0));
        im.set_upper_is_inf(tmp_i, false);
        im.set_upper_is_open(tmp_i, false);
        im.set_upper(tmp_i, n - 1);
        im.intersect <dep_intervals::without_deps>(i, tmp_i, i);
    }

    // x = y*(u div y), y > 0 -> x <= u
    if (a.is_mul(x, y, z) && a.is_idiv(z, u, v) && v == y) {
        scoped_dep_interval iy(im), iu(im), tmp_i(im);
        get_bounds(y, iy);
        get_bounds(u, iu);
        if (!im.lower_is_inf(iy) && im.lower(iy) > 0 &&
            !im.upper_is_inf(iu) && im.upper(iu) >= 0) {
            im.set_upper_is_inf(tmp_i, false);
            im.set_upper_is_open(tmp_i, im.upper_is_open(iu));
            im.set_upper(tmp_i, im.upper(iu));
            im.intersect<dep_intervals::without_deps>(i, tmp_i, i);
        }
    }

    // x = y div z, z > 0 => x <= y
    if (a.is_idiv(x, y, z)) {
        scoped_dep_interval iy(im), iz(im), tmp_i(im);
        get_bounds(y, iy);
        get_bounds(z, iz);
        if (!im.lower_is_inf(iz) && im.lower(iz) > 0 && 
            !im.upper_is_inf(iy) && im.upper(iy) >= 0) {
            im.set_upper_is_inf(tmp_i, false);
            im.set_upper_is_open(tmp_i, im.upper_is_open(iy));
            im.set_upper(tmp_i, im.upper(iy));
            im.set_lower_is_inf(tmp_i, false);
            im.set_lower_is_open(tmp_i, false); // TODO - could be refined
            im.set_lower(tmp_i, rational::zero());
            im.intersect<dep_intervals::without_deps>(i, tmp_i, i);
        }
    }   
    if (a.is_div(x, y, z)) {
        scoped_dep_interval iy(im), iz(im), tmp_i(im);
        get_bounds(y, iy);
        get_bounds(z, iz);
        im.div<dep_intervals::without_deps>(iy, iz, tmp_i);
        im.intersect<dep_intervals::without_deps>(i, tmp_i, i);
    }
}

void bound_simplifier::expr2linear_pol(expr* t, mpq_buffer& as, var_buffer& xs) {
    scoped_mpq c_mpq_val(nm);
    if (a.is_add(t)) {
        rational c_val;
        for (expr* mon : *to_app(t)) {
            expr* c, * x;
            if (a.is_mul(mon, c, x) && a.is_numeral(c, c_val)) {
                nm.set(c_mpq_val, c_val.to_mpq());
                as.push_back(c_mpq_val);
                xs.push_back(to_var(x));
            }
            else {
                as.push_back(mpq(1));
                xs.push_back(to_var(mon));
            }
        }
    }
    else {
        as.push_back(mpq(1));
        xs.push_back(to_var(t));
    }
}

bool bound_simplifier::lower_subsumed(expr* p, mpq const& k, bool strict) {
    if (!a.is_add(p))
        return false;
    m_num_buffer.reset();
    m_var_buffer.reset();
    expr2linear_pol(p, m_num_buffer, m_var_buffer);
    scoped_mpq  implied_k(nm);
    bool implied_strict;
    return
        bp.lower(m_var_buffer.size(), m_num_buffer.data(), m_var_buffer.data(), implied_k, implied_strict) &&
        (nm.gt(implied_k, k) || (nm.eq(implied_k, k) && (!strict || implied_strict)));
}

bool bound_simplifier::upper_subsumed(expr* p, mpq const& k, bool strict) {
    if (!a.is_add(p))
        return false;
    m_num_buffer.reset();
    m_var_buffer.reset();
    expr2linear_pol(p, m_num_buffer, m_var_buffer);
    scoped_mpq implied_k(nm);
    bool implied_strict;
    return
        bp.upper(m_var_buffer.size(), m_num_buffer.data(), m_var_buffer.data(), implied_k, implied_strict) &&
        (nm.lt(implied_k, k) || (nm.eq(implied_k, k) && (!strict || implied_strict)));
}

void bound_simplifier::restore_bounds() {
    scoped_mpq l(nm), u(nm);
    bool strict_l, strict_u, has_l, has_u;
    unsigned ts;
    unsigned sz = m_var2expr.size();

    rw rw(*this);
    auto add = [&](expr* fml) {
        expr_ref tmp(fml, m);
        rw(tmp, tmp);
        m_rewriter(tmp);
        m_fmls.add(dependent_expr(m, tmp, nullptr, nullptr));
    };

    for (unsigned x = 0; x < sz; x++) {
        expr* p = m_var2expr.get(x);
        has_l = bp.lower(x, l, strict_l, ts);
        has_u = bp.upper(x, u, strict_u, ts);
        if (!has_l && !has_u)
            continue;
        if (has_l && has_u && nm.eq(l, u) && !strict_l && !strict_u) {
            // l <= p <= l -->  p = l
            add(m.mk_eq(p, a.mk_numeral(rational(l), a.is_int(p))));            
            continue;
        }
        if (has_l && !lower_subsumed(p, l, strict_l)) {
            if (strict_l)
                add(m.mk_not(a.mk_le(p, a.mk_numeral(rational(l), a.is_int(p)))));
            else
                add(a.mk_ge(p, a.mk_numeral(rational(l), a.is_int(p))));
        }
        if (has_u && !upper_subsumed(p, u, strict_u)) {
            if (strict_u)
                add(m.mk_not(a.mk_ge(p, a.mk_numeral(rational(u), a.is_int(p)))));
            else
                add(a.mk_le(p, a.mk_numeral(rational(u), a.is_int(p))));
        }
    }
}


void bound_simplifier::reset() {
    bp.reset();
    m_var2expr.reset();
    m_expr2var.reset();
    m_trail.reset();
}

#if 0
void find_ite_bounds(expr* root) {
    TRACE("find_ite_bounds_bug", display_bounds(tout););
    expr* n = root;
    expr* target = nullptr;
    expr* c, * t, * e;
    expr* x, * y;
    bool has_l, has_u;
    mpq l_min, u_max;
    bool l_strict, u_strict;
    mpq curr;
    bool curr_strict;
    while (true) {
        TRACE("find_ite_bounds_bug", tout << mk_ismt2_pp(n, m) << "\n";);

        if (m.is_ite(n, c, t, e)) {
            if (is_x_minus_y_eq_0(t, x, y))
                n = e;
            else if (is_x_minus_y_eq_0(e, x, y))
                n = t;
            else
                break;
        }
        else if (is_x_minus_y_eq_0(n, x, y)) {
            n = nullptr;
        }
        else {
            break;
        }

        TRACE("find_ite_bounds_bug", tout << "x: " << mk_ismt2_pp(x, m) << ", y: " << mk_ismt2_pp(y, m) << "\n";
        if (target) {
            tout << "target: " << mk_ismt2_pp(target, m) << "\n";
            tout << "has_l: " << has_l << " " << nm.to_string(l_min) << " has_u: " << has_u << " " << nm.to_string(u_max) << "\n";
        });

        if (is_unbounded(y))
            std::swap(x, y);

        if (!is_unbounded(x)) {
            TRACE("find_ite_bounds_bug", tout << "x is already bounded\n";);
            break;
        }

        if (target == nullptr) {
            target = x;
            if (lower(y, curr, curr_strict)) {
                has_l = true;
                nm.set(l_min, curr);
                l_strict = curr_strict;
            }
            else {
                has_l = false;
                TRACE("find_ite_bounds_bug", tout << "y does not have lower\n";);
            }
            if (upper(y, curr, curr_strict)) {
                has_u = true;
                nm.set(u_max, curr);
                u_strict = curr_strict;
            }
            else {
                has_u = false;
                TRACE("find_ite_bounds_bug", tout << "y does not have upper\n";);
            }
        }
        else if (target == x) {
            if (has_l) {
                if (lower(y, curr, curr_strict)) {
                    if (nm.lt(curr, l_min) || (!curr_strict && l_strict && nm.eq(curr, l_min))) {
                        nm.set(l_min, curr);
                        l_strict = curr_strict;
                    }
                }
                else {
                    has_l = false;
                    TRACE("find_ite_bounds_bug", tout << "y does not have lower\n";);
                }
            }
            if (has_u) {
                if (upper(y, curr, curr_strict)) {
                    if (nm.gt(curr, u_max) || (curr_strict && !u_strict && nm.eq(curr, u_max))) {
                        nm.set(u_max, curr);
                        u_strict = curr_strict;
                    }
                }
                else {
                    has_u = false;
                    TRACE("find_ite_bounds_bug", tout << "y does not have upper\n";);
                }
            }
        }
        else {
            break;
        }

        if (!has_l && !has_u)
            break;

        if (n == nullptr) {
            TRACE("find_ite_bounds", tout << "found bounds for: " << mk_ismt2_pp(target, m) << "\n";
            tout << "has_l: " << has_l << " " << nm.to_string(l_min) << " l_strict: " << l_strict << "\n";
            tout << "has_u: " << has_u << " " << nm.to_string(u_max) << " u_strict: " << u_strict << "\n";
            tout << "root:\n" << mk_ismt2_pp(root, m) << "\n";);
            a_var x = mk_var(target);
            if (has_l)
                bp.assert_lower(x, l_min, l_strict);
            if (has_u)
                bp.assert_upper(x, u_max, u_strict);
            break;
        }
    }
    nm.del(l_min);
    nm.del(u_max);
    nm.del(curr);
}

void find_ite_bounds() {
    unsigned sz = m_new_goal->size();
    for (unsigned i = 0; i < sz; i++) {
        expr* f = m_new_goal->form(i);
        if (m.is_ite(f))
            find_ite_bounds(to_app(f));
    }
    bp.propagate();
    TRACE("find_ite_bounds", display_bounds(tout););
}

#endif
