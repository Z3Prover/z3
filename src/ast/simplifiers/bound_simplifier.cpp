/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bounds_simplifier.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2023-01-22

--*/


#include "ast/ast_pp.h"
#include "ast/simplifiers/bound_simplifier.h"
#include "ast/rewriter/rewriter_def.h"

struct bound_simplifier::rw_cfg : public default_rewriter_cfg {
    ast_manager& m;
    bound_propagator& bp;
    bound_simplifier& s;
    arith_util a;
    rw_cfg(bound_simplifier& s):m(s.m), bp(s.bp), s(s), a(m) {}

    br_status reduce_app(func_decl* f, unsigned num_args, expr * const* args, expr_ref& result, proof_ref& pr) {
        rational N, hi, lo;
        bool strict;
        if (a.is_mod(f) && num_args == 2 && a.is_numeral(args[1], N)) {
            expr* x = args[0];
            if (!s.has_upper(x, hi, strict) || strict)
                return BR_FAILED;
            if (!s.has_lower(x, lo, strict) || strict)
                return BR_FAILED;
            if (hi - lo >= N)
                return BR_FAILED;
            if (N > hi && lo >= 0) {
                result = x;
                return BR_DONE;
            }
            if (2*N > hi && lo >= N) {
                result = a.mk_sub(x, a.mk_int(N));
                s.m_rewriter(result);
                return BR_DONE;
            }
            IF_VERBOSE(2, verbose_stream() << "potentially missed simplification: " << mk_pp(x, m) << " " << lo << " " << hi << " not reduced\n");
        }
        return BR_FAILED;
    }
};  

struct bound_simplifier::rw : public rewriter_tpl<rw_cfg> {
    rw_cfg m_cfg;

    rw(bound_simplifier& s):
        rewriter_tpl<rw_cfg>(s.m, false, m_cfg),
        m_cfg(s) {
    }
};    

void bound_simplifier::reduce() {
    
    m_updated = true;
    for (unsigned i = 0; i < 5 && m_updated; ++i) {
        m_updated = false;
        reset();
        for (unsigned idx : indices()) 
            insert_bound(m_fmls[idx]);
        for (unsigned idx : indices()) 
            tighten_bound(m_fmls[idx]);
        
        rw rw(*this);

        // TODO: take over propagate_ineq:
        // bp.propagate();
        // serialize bounds
        
        proof_ref pr(m);
        expr_ref r(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            rw(d.fml(), r, pr);
            if (r != d.fml()) {
                m_fmls.update(idx, dependent_expr(m, r, mp(d.pr(), pr), d.dep()));
                m_updated = true;
            }
        }
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
    expr* z, *u;
    bool strict;
    if (a.is_le(f, x, y)) {
        // x <= (x + k) mod N && x >= 0 -> x + k < N
        if (a.is_mod(y, z, u) && a.is_numeral(u, n) && has_lower(x, k, strict) && k >= 0 && is_offset(z, x, k) && k > 0 && k < n) {
            assert_upper(x, n - k, true);
        }
    }
    if (m.is_not(f, f) && m.is_eq(f, x, y)) {
        if (a.is_numeral(x))
            std::swap(x, y);
        bool strict;
        if (a.is_numeral(y, n)) {
            if (has_lower(x, k, strict) && !strict && k == n) 
                assert_lower(x, k, true);
            else if (has_upper(x, k, strict) && !strict && k == n) 
                assert_upper(x, k, true);
        }
    }
}

void bound_simplifier::assert_upper(expr* x, rational const& n, bool strict) {
    scoped_mpq c(nm);
    nm.set(c, n.to_mpq());    
    bp.assert_upper(to_var(x), c, strict);
}


void bound_simplifier::assert_lower(expr* x, rational const& n, bool strict) {
    scoped_mpq c(nm);
    nm.set(c, n.to_mpq());
    bp.assert_lower(to_var(x), c, strict);
}

//
// TODO: Use math/interval/interval.h
//

bool bound_simplifier::has_lower(expr* x, rational& n, bool& strict) {
    if (is_var(x)) {
        unsigned v = to_var(x);
        if (bp.has_lower(v)) { 
            mpq const & q = bp.lower(v, strict);
            n = rational(q);
            return true;
        }
    }
    if (a.is_numeral(x, n)) {
        strict = false;
        return true;
    }
    if (a.is_mod(x)) {
        n = rational::zero();
        strict = false;
        return true;
    }
    expr* y, *z;
    if (a.is_idiv(x, y, z) && has_lower(z, n, strict) && n > 0 && has_lower(y, n, strict))
        return true;

    if (a.is_add(x)) {
        rational bound;
        strict = false;
        n = 0;
        bool is_strict;
        for (expr* arg : *to_app(x)) {
            if (!has_lower(arg, bound, is_strict))
                return false;
            strict |= is_strict;
            n += bound;
        }
        return true;
    }

    if (a.is_mul(x, y, z)) {
        // TODO: this is done generally using math/interval/interval.h
        rational bound1, bound2;
        bool strict1, strict2;
        if (has_lower(y, bound1, strict1) && !strict1 &&
            has_lower(z, bound1, strict2) && !strict2 &&
            bound1 >= 0 && bound2 >= 0) {
            n = bound1*bound2;
            strict = false;
            return true;
        }
    }

    return false;
}


bool bound_simplifier::has_upper(expr* x, rational& n, bool& strict) {
    if (is_var(x)) {
        unsigned v = to_var(x);
        if (bp.has_upper(v)) { 
            mpq const & q = bp.upper(v, strict);
            n = rational(q);
            return true;
        }
    }

    // perform light-weight abstract analysis
    // y * (u / y) is bounded by u, if y > 0

    if (a.is_numeral(x, n)) {
        strict = false;
        return true;
    }

    if (a.is_add(x)) {
        rational bound;
        strict = false;
        n = 0;
        bool is_strict;
        for (expr* arg : *to_app(x)) {
            if (!has_upper(arg, bound, is_strict))
                return false;
            strict |= is_strict;
            n += bound;
        }
        return true;
    }

    expr* y, *z, *u, *v;
    if (a.is_mul(x, y, z) && a.is_idiv(z, u, v) && v == y && has_lower(y, n, strict) && n > 0 && has_upper(u, n, strict))
        return true;
    if (a.is_idiv(x, y, z) && has_lower(z, n, strict) && n > 0 && has_upper(y, n, strict))
        return true;

    return false;
}

void bound_simplifier::get_bounds(expr* x, scoped_interval& i) {
    i.m().reset_upper(i);
    i.m().reset_lower(i);
    
    rational n;
    if (a.is_numeral(x, n)) {
        i.m().set(i, n.to_mpq());
        return;
    }

    if (is_var(x)) {
        unsigned v = to_var(x);
        bool strict;
        if (bp.has_upper(v)) {
            mpq const& q = bp.upper(v, strict);
            i_cfg.set_upper_is_open(i, strict);
            i_cfg.set_upper(i, q);
        }
        if (bp.has_lower(v)) {
            mpq const& q = bp.lower(v, strict);
            i_cfg.set_lower_is_open(i, strict);
            i_cfg.set_lower(i, q);
        }
    }

    if (a.is_add(x)) {
        scoped_interval sum_i(i.m());
        scoped_interval arg_i(i.m());
        i.m().set(sum_i, mpq(0));
        for (expr* arg : *to_app(x)) {
            get_bounds(arg, arg_i);
            i.m().add(sum_i, arg_i, sum_i);
        }
        // TODO: intersect
        i.m().set(i, sum_i);
    }

    if (a.is_mul(x)) {
        scoped_interval mul_i(i.m());
        scoped_interval arg_i(i.m());
        i.m().set(mul_i, mpq(1));
        for (expr* arg : *to_app(x)) {
            get_bounds(arg, arg_i);
            i.m().add(mul_i, arg_i, mul_i);
        }
        // TODO: intersect
        i.m().set(i, mul_i);
    }

    // etc:
    // import interval from special case code for lower and upper.

    
    
}

void bound_simplifier::reset() {
    bp.reset();
    m_var2expr.reset();
    m_expr2var.reset();
    m_num_vars = 0;
}
