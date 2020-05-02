/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv2int_rewriter.cpp

Abstract:

    Basic rewriting rules for bv2int propagation.

Author:

    Nikolaj (nbjorner) 2011-05-05

Notes:

--*/
#include "tactic/arith/bv2int_rewriter.h"
#include "tactic/tactic_exception.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"

void bv2int_rewriter_ctx::update_params(params_ref const& p) {
    m_max_size = p.get_uint("max_bv_size", m_max_size);
}

struct lt_rational {
    bool operator()(rational const& a, rational const& b) const { return a < b; }
};

void bv2int_rewriter_ctx::collect_power2(goal const& s) {
    ast_manager& m = m_trail.get_manager();
    arith_util arith(m);
    bv_util bv(m);
    
    for (unsigned j = 0; j < s.size(); ++j) {
        expr* f = s.form(j);
        if (!m.is_or(f)) continue;
        unsigned sz = to_app(f)->get_num_args();
        expr* x, *y, *v = nullptr;
        rational n;
        vector<rational> bounds;
        bool is_int, ok = true;

        for (unsigned i = 0; ok && i < sz; ++i) {
            expr* e = to_app(f)->get_arg(i);
            if (!m.is_eq(e, x, y)) {
                ok = false;
                break;
            }
            if (arith.is_numeral(y, n, is_int) && is_int &&
                (x == v || v == nullptr)) {
                v = x;
                bounds.push_back(n);
            }
            else if (arith.is_numeral(x, n, is_int) && is_int &&
                     (y == v || v == nullptr)) {
                v = y;
                bounds.push_back(n);
            }
            else {
                ok = false;
                break;
            }
        }
        if (!ok || !v) continue;
        SASSERT(!bounds.empty());
        lt_rational lt;
        // lt is a total order on rationals.
        std::sort(bounds.begin(), bounds.end(), lt);
        rational p(1);
        unsigned num_bits = 0;
        for (unsigned i = 0; ok && i < bounds.size(); ++i) {
            ok = (p == bounds[i]); 
            p *= rational(2);
            ++num_bits;
        }
        if (!ok) continue;
        unsigned log2 = 0;
        for (unsigned i = 1; i <= num_bits; i *= 2) ++log2;
        if(log2 == 0) continue;
        expr* logx = m.mk_fresh_const("log2_v", bv.mk_sort(log2));
        logx = bv.mk_zero_extend(num_bits - log2, logx);
        m_trail.push_back(logx);
        TRACE("bv2int_rewriter", tout << mk_pp(v, m) << " |-> " << mk_pp(logx, m) << "\n";);
        m_power2.insert(v, logx);
    }
}

bool bv2int_rewriter_ctx::is_power2(expr* x, expr*& log_x) {
    return m_power2.find(x, log_x);
}

bv2int_rewriter::bv2int_rewriter(ast_manager & m, bv2int_rewriter_ctx& ctx)
    :m_manager(m), m_ctx(ctx), m_bv(m), m_arith(m) {    
}


br_status bv2int_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    if (f->get_family_id() == m_arith.get_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_NUM:  return BR_FAILED;
        case OP_LE:   SASSERT(num_args == 2); return mk_le(args[0], args[1], result);
        case OP_GE:   SASSERT(num_args == 2); return mk_ge(args[0], args[1], result);
        case OP_LT:   SASSERT(num_args == 2); return mk_lt(args[0], args[1], result);
        case OP_GT:   SASSERT(num_args == 2); return mk_gt(args[0], args[1], result);
        case OP_ADD:  return mk_add(num_args, args, result);
        case OP_MUL:  return mk_mul(num_args, args, result);
        case OP_SUB:  return mk_sub(num_args, args, result);
        case OP_DIV:  return BR_FAILED;
        case OP_IDIV: SASSERT(num_args == 2); return mk_idiv(args[0], args[1], result);
        case OP_MOD:  SASSERT(num_args == 2); return mk_mod(args[0], args[1], result);
        case OP_REM:  SASSERT(num_args == 2); return mk_rem(args[0], args[1], result);
        case OP_UMINUS:  SASSERT(num_args == 1); return mk_uminus(args[0], result);
        case OP_TO_REAL: return BR_FAILED;
        case OP_TO_INT:  return BR_FAILED;
        case OP_IS_INT:  return BR_FAILED;
        default:         return BR_FAILED;
        }
    }
    if (f->get_family_id() == m().get_basic_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_EQ:  SASSERT(num_args == 2); return mk_eq(args[0], args[1], result);
        case OP_ITE: SASSERT(num_args == 3); return mk_ite(args[0], args[1], args[2], result); 
        case OP_DISTINCT: 
            if (num_args >= 2 && m_arith.is_int(args[0])) {
                expr_ref_vector eqs(m());
                for (unsigned i = 0; i < num_args; ++i) {
                    for (unsigned j = i + 1; j < num_args; ++j) {
                        if (BR_DONE != mk_eq(args[i], args[j], result)) {
                            return BR_FAILED;
                        }
                        eqs.push_back(result);
                    }
                }
                result = m().mk_not(mk_or(eqs));
                return BR_DONE;
            }
            return BR_FAILED;
        default: return BR_FAILED;
        }
    }
    return BR_FAILED;
}

br_status bv2int_rewriter::mk_le(expr * s, expr * t, expr_ref & result) {
    expr_ref s1(m()), t1(m()), s2(m()), t2(m());
    if (is_bv2int(s, s1) && is_bv2int(t, t1)) {
        align_sizes(s1, t1, false);
        result = m_bv.mk_ule(s1, t1);
        return BR_DONE;
    }
    if (is_bv2int_diff(s, s1, s2) && is_bv2int_diff(t, t1, t2)) {
        //     s1 - s2 <= t1 - t2
        // <=>
        //     s1 + t2 <= t1 + s2
        //
        s1 = mk_bv_add(s1, t2, false);
        t1 = mk_bv_add(t1, s2, false);        
        align_sizes(s1, t1, false);
        result = m_bv.mk_ule(s1, t1);
        return BR_DONE;
    }
    if (is_sbv2int(s, s1) && is_sbv2int(t, t1)) {
        align_sizes(s1, t1, true);
        result = m_bv.mk_sle(s1, t1);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status bv2int_rewriter::mk_lt(expr * arg1, expr * arg2, expr_ref & result) {
    result = m().mk_not(m_arith.mk_le(arg2, arg1));
    return BR_REWRITE2;
}

br_status bv2int_rewriter::mk_ge(expr * arg1, expr * arg2, expr_ref & result) {
    return mk_le(arg2, arg1, result);
}

br_status bv2int_rewriter::mk_gt(expr * arg1, expr * arg2, expr_ref & result) {
    result = m().mk_not(m_arith.mk_le(arg1, arg2));
    return BR_REWRITE2;
}

br_status bv2int_rewriter::mk_ite(expr* c, expr* s, expr* t, expr_ref& result) {
    expr_ref s1(m()), t1(m());
    if (is_bv2int(s, s1) && is_bv2int(t, t1)) {
        align_sizes(s1, t1, false);
        result = m_bv.mk_bv2int(m().mk_ite(c, s1, t1));
        return BR_DONE;
    }

    if (is_sbv2int(s, s1) && is_sbv2int(t, t1)) {
        align_sizes(s1, t1, true);
        result = mk_sbv2int(m().mk_ite(c, s1, t1));
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status bv2int_rewriter::mk_eq(expr * s, expr * t, expr_ref & result) {
    expr_ref s1(m()), t1(m()), s2(m()), t2(m());
    if (is_bv2int(s, s1) && is_bv2int(t, t1)) {
        align_sizes(s1, t1, false);
        result = m().mk_eq(s1, t1);
        return BR_DONE;
    }
    if (is_bv2int_diff(s, s1, s2) && is_bv2int_diff(t, t1, t2)) {
        s1 = mk_bv_add(s1, t2, false);
        t1 = mk_bv_add(s2, t1, false);        
        align_sizes(s1, t1, false);
        result = m().mk_eq(s1, t1);
        return BR_DONE;
    }
    if (is_sbv2int(s, s1) && is_sbv2int(t, t1)) {
        align_sizes(s1, t1, true);
        result = m().mk_eq(s1, t1);
        return BR_DONE;
    }
    return BR_FAILED;
}


br_status bv2int_rewriter::mk_idiv(expr * arg1, expr * arg2, expr_ref & result) {
    // TBD
    return BR_FAILED;
}
 
br_status bv2int_rewriter::mk_mod(expr * s, expr * t, expr_ref & result) {
    expr_ref s1(m()), s2(m()), t1(m());
    rational r;
    if (!m_arith.is_numeral(t, r) || !r.is_pos())
        return BR_FAILED;
    if (is_bv2int(s, s1) && is_bv2int(t, t1)) {
        align_sizes(s1, t1, false);
        result = m_bv.mk_bv2int(m_bv.mk_bv_urem(s1, t1));
        TRACE("bv2int_rewriter", tout << result << "\n";);
        return BR_DONE;
    }

    //
    // (s1 - s2) mod t1 = (s1 + (t1 - (s2 mod t1))) mod t1
    //
    if (is_bv2int_diff(s, s1, s2) && is_bv2int(t, t1)) {
        expr_ref u1(m());
        align_sizes(s2, t1, false);
        u1 = m_bv.mk_bv_urem(s2, t1);
        u1 = m_bv.mk_bv_sub(t1, u1);
        u1 = mk_bv_add(s1, u1, false);
        align_sizes(u1, t1, false);
        result = m_bv.mk_bv2int(m_bv.mk_bv_urem(u1, t1));
        TRACE("bv2int_rewriter", tout << result << "\n";);
        return BR_DONE;
    }
    
#if 0
    // TBD: check semantics
    if (is_sbv2int(s, s1) && is_sbv2int(t, t1)) {
        align_sizes(s1, t1, true);
        result = mk_sbv2int(m_bv.mk_bv_srem(s1, t1));
        return BR_DONE;
    }
#endif
    return BR_FAILED;
}


br_status bv2int_rewriter::mk_rem(expr * arg1, expr * arg2, expr_ref & result) {
    // TBD
    return BR_FAILED;
}

br_status bv2int_rewriter::mk_uminus(expr * s, expr_ref & result) {
    expr_ref s1(m()), s2(m());
    if (is_bv2int_diff(s, s1, s2)) {
        result = m_arith.mk_sub(m_bv.mk_bv2int(s2), m_bv.mk_bv2int(s1));
        return BR_DONE;
    }
    if (is_sbv2int(s, s1)) {
        result = mk_sbv2int(m_bv.mk_bv_neg(s1));
        return BR_DONE;
    }
    return BR_FAILED;
}


br_status bv2int_rewriter::mk_add(unsigned num_args, expr * const* args, expr_ref& result) {
    br_status r = BR_DONE;
    SASSERT(num_args > 0);
    result = args[0];
    for (unsigned i = 1; r == BR_DONE && i < num_args; ++i) {
        r = mk_add(result, args[i], result);
    }
    return r;
}

void bv2int_rewriter::align_sizes(expr_ref& s, expr_ref& t, bool is_signed) {
    unsigned sz1 = m_bv.get_bv_size(s);
    unsigned sz2 = m_bv.get_bv_size(t);
    if (sz1 > sz2 && is_signed) {
        t = mk_extend(sz1-sz2, t, true);
    }
    if (sz1 > sz2 && !is_signed) {
        t = mk_extend(sz1-sz2, t, false);
    }
    if (sz1 < sz2 && is_signed) {
        s = mk_extend(sz2-sz1, s, true);
    }
    if (sz1 < sz2 && !is_signed) {
        s = mk_extend(sz2-sz1, s, false);
    }
}


bool bv2int_rewriter::is_zero(expr* n) {
    rational r;
    unsigned sz;
    return m_bv.is_numeral(n, r, sz) && r.is_zero();
}

expr* bv2int_rewriter::mk_bv_add(expr* s, expr* t, bool is_signed) {
    SASSERT(m_bv.is_bv(s));
    SASSERT(m_bv.is_bv(t));

    if (is_zero(s)) {
        return t;
    }
    if (is_zero(t)) {
        return s;
    }
    expr_ref s1(s, m()), t1(t, m());
    align_sizes(s1, t1, is_signed);
    s1 = mk_extend(1, s1, is_signed);
    t1 = mk_extend(1, t1, is_signed);
    return m_bv.mk_bv_add(s1, t1);
}


br_status bv2int_rewriter::mk_add(expr* s, expr* t, expr_ref& result) {
    expr_ref s1(m()), t1(m()), s2(m()), t2(m());
    if (is_bv2int(s, s1) && is_bv2int(t, t1)) {
        result = m_bv.mk_bv2int(mk_bv_add(s1, t1, false));
        return BR_DONE;
    }
    if (is_bv2int_diff(s, s1, s2) && is_bv2int_diff(t, t1, t2)) {
        //     s1 - s2 + t1 - t2
        // =
        //     s1 + t1 - (s2 + t2)
        //
        t1 = m_bv.mk_bv2int(mk_bv_add(s1, t1, false));
        t2 = m_bv.mk_bv2int(mk_bv_add(s2, t2, false));
        result = m_arith.mk_sub(t1, t2); 
        return BR_DONE;
    }
    if (is_sbv2int(s, s1) && is_sbv2int(t, t1)) {
        result = mk_sbv2int(mk_bv_add(s1, t1, true));
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status bv2int_rewriter::mk_mul(unsigned num_args, expr * const* args, expr_ref& result) {
    br_status r = BR_DONE;
    SASSERT(num_args > 0);
    result = args[0];
    for (unsigned i = 1; r == BR_DONE && i < num_args; ++i) {
        r = mk_mul(result, args[i], result);
    }
    return r;
}

expr* bv2int_rewriter::mk_bv_mul(expr* s, expr* t, bool is_signed) {
    SASSERT(m_bv.is_bv(s));
    SASSERT(m_bv.is_bv(t));
    if (is_zero(s)) {
        return s;
    }
    if (is_zero(t)) {
        return t;
    }    
    rational r; 
    unsigned sz;
    if (m_bv.is_numeral(s, r, sz) && r.is_one()) {
        return t;
    }
    if (m_bv.is_numeral(t, r, sz) && r.is_one()) {
        return s;
    }
    expr_ref s1(s, m()), t1(t, m());
    align_sizes(s1, t1, is_signed);
    unsigned n = m_bv.get_bv_size(t1);    
    unsigned max_bits = m_ctx.get_max_num_bits();
    bool add_side_conds = 2*n > max_bits;
    if (n >= max_bits) {
        //
    }
    else if (2*n > max_bits) {
        s1 = mk_extend(max_bits-n, s1, is_signed);
        t1 = mk_extend(max_bits-n, t1, is_signed);        
    }
    else {
        s1 = mk_extend(n, s1, is_signed);
        t1 = mk_extend(n, t1, is_signed);
    }
    if (add_side_conds) {
        if (is_signed) {
            m_ctx.add_side_condition(m_bv.mk_bvsmul_no_ovfl(s1, t1));        
            m_ctx.add_side_condition(m_bv.mk_bvsmul_no_udfl(s1, t1));        
        }
        else {
            m_ctx.add_side_condition(m_bv.mk_bvumul_no_ovfl(s1, t1));        
        }
    }
    return m_bv.mk_bv_mul(s1, t1);
}


br_status bv2int_rewriter::mk_mul(expr* s, expr* t, expr_ref& result) {
    expr_ref s1(m()), s2(m()), t1(m()), t2(m());
    if ((is_shl1(s, s1) && is_bv2int(t, t1)) ||
        (is_shl1(t, s1) && is_bv2int(s, t1))) {
        unsigned n = m_bv.get_bv_size(s1);
        unsigned m = m_bv.get_bv_size(t1);
        s1 = mk_extend(m, s1, false);
        t1 = mk_extend(n, t1, false);
        result = m_bv.mk_bv2int(m_bv.mk_bv_shl(t1, s1));
        return BR_DONE;
    }
    if (is_bv2int(s, s1) && is_bv2int(t, t1)) {
        result = m_bv.mk_bv2int(mk_bv_mul(s1, t1, false));
        return BR_DONE;
    }
    if ((is_bv2int(s, s1) && is_bv2int_diff(t, t1, t2)) ||
        (is_bv2int(t, s1) && is_bv2int_diff(s, t1, t2))) {
        t1 = m_bv.mk_bv2int(mk_bv_mul(s1, t1, false));
        t2 = m_bv.mk_bv2int(mk_bv_mul(s1, t2, false));
        result = m_arith.mk_sub(t1, t2);
        return BR_DONE;
    }
    if (is_sbv2int(s, s1) && is_sbv2int(t, t1)) {
        result = mk_sbv2int(mk_bv_mul(s1, t1, true));
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status bv2int_rewriter::mk_sub(unsigned num_args, expr * const* args, expr_ref& result) {
    br_status r = BR_DONE;
    SASSERT(num_args > 0);
    result = args[0];
    for (unsigned i = 1; r == BR_DONE && i < num_args; ++i) {
        r = mk_sub(result, args[i], result);
    }
    return r;
}

br_status bv2int_rewriter::mk_sub(expr* s, expr* t, expr_ref& result) {
    expr_ref s1(m()), t1(m()), s2(m()), t2(m());
    if (is_bv2int_diff(s, s1, s2) && is_bv2int_diff(t, t1, t2)) {
        //     s1 - s2 - (t1 - t2)
        // =
        //     s1 + t2 - (t1 + s2)
        //
        s1 = m_bv.mk_bv2int(mk_bv_add(s1, t2, false));
        s2 = m_bv.mk_bv2int(mk_bv_add(s2, t1, false));
        result = m_arith.mk_sub(s1, s2); 
        return BR_DONE;
    }
    if (is_sbv2int(s, s1) && is_sbv2int(t, t1)) {
        align_sizes(s1, t1, true);
        s1 = m_bv.mk_sign_extend(1, s1);
        t1 = m_bv.mk_sign_extend(1, t1);
        result = mk_sbv2int(m_bv.mk_bv_sub(s1, t1));
        return BR_DONE;
    }
    return BR_FAILED;
}

bool bv2int_rewriter::is_bv2int(expr* n, expr_ref& s) {
    rational k;
    bool is_int;
    if (m_bv.is_bv2int(n)) {
        s = to_app(n)->get_arg(0);
        return true;
    }
    if (m_arith.is_numeral(n, k, is_int) && is_int && !k.is_neg()) {
        unsigned sz = k.get_num_bits();
        s = m_bv.mk_numeral(k, m_bv.mk_sort(sz));
        return true;
    }
    return false;
}

bool bv2int_rewriter::is_shl1(expr* n, expr_ref& s) {
    expr* s1, *s2;
    rational r;
    unsigned bv_size;
    if(m_bv.is_bv2int(n, s2) && 
        m_bv.is_bv_shl(s2, s1, s2) && 
        m_bv.is_numeral(s1, r, bv_size) && 
        r.is_one()) {
        s = s2;
        return true;
    }
    return false;
}

bool bv2int_rewriter::is_bv2int_diff(expr* n, expr_ref& s, expr_ref& t) {
    if (is_bv2int(n, s)) {
        t = m_bv.mk_numeral(0, 1);
        return true;
    }
    rational k;
    bool is_int;
    if (m_arith.is_numeral(n, k, is_int) && is_int) {
        SASSERT(k.is_neg());
        k.neg();
        unsigned sz = k.get_num_bits();
        t = m_bv.mk_numeral(k, m_bv.mk_sort(sz));
        s = m_bv.mk_numeral(0, 1);
        return true;
    }
    //
    // bv2int(a) - bv2int(b)
    // 
    expr *e1, *e2;
    if (m_arith.is_sub(n, e1, e2) &&
        is_bv2int(e1, s) &&
        is_bv2int(e2, t)) {
        return true;
    }   
    if (m_arith.is_add(n, e1, e2) &&
        m_arith.is_numeral(e1, k, is_int) && is_int && k.is_neg() &&
        is_bv2int(e2, s)) {
        k.neg();
        unsigned sz = k.get_num_bits();
        t = m_bv.mk_numeral(k, m_bv.mk_sort(sz));
        return true;        
    }
    if (m_arith.is_add(n, e1, e2) &&
        m_arith.is_numeral(e2, k, is_int) && is_int && k.is_neg() &&
        is_bv2int(e1, s)) {
        k.neg();
        unsigned sz = k.get_num_bits();
        t = m_bv.mk_numeral(k, m_bv.mk_sort(sz));
        return true;        
    }
    return false;
}

bool bv2int_rewriter::is_sbv2int(expr* n, expr_ref& s) {
    if (is_bv2int(n, s)) {
        s = m_bv.mk_zero_extend(1, s);
        return true;
    }
    expr_ref u1(m()), u2(m());
    if (is_bv2int_diff(n, u1, u2)) {
        align_sizes(u1, u2, false);
        u1 = mk_extend(1, u1, false);
        u2 = mk_extend(1, u2, false);
        s = m_bv.mk_bv_sub(u1, u2);
        return true;
    }
    // ite(bv1 == b[n-1:n-1], bv2int(b[0:n-2]) - 2^{n-1}, bv2int(b[0:n-2]))
    expr* c, *t, *e1, *c1, *c2, *c3, *t1, *t2, *e2, *e3;
    rational k;
    bool is_int;
    unsigned lo, hi, lo1, hi1, sz;
    
    if (m().is_ite(n, c, t, e1) &&
        m().is_eq(c, c1, c2) &&
        m_bv.is_numeral(c1, k, sz) && k.is_one() && sz == 1 &&
        m_bv.is_extract(c2, lo, hi, c3) && 
        lo == hi && lo == m_bv.get_bv_size(c3) - 1 && 
        m_arith.is_sub(t, t1, t2) &&
        e1 == t1 &&
        m_bv.is_bv2int(e1, e2) &&
        m_bv.is_extract(e2, lo1, hi1, e3) &&
        lo1 == 0 && hi1 == hi-1 &&
        m_arith.is_numeral(t2, k, is_int) && is_int &&
        k == rational::power_of_two(hi) 
        ) {
        s = e3;
        return true;
    }
        
#if 0
    // bv2int(b[0:n-2]) - ite(bv1 == b[n-1:n-1], 2^{n-1}, 0)
    if (m().is_sub(n, e1, e2) &&
        m_bv.is_bv2int(e1, e3) &&
        m_bv.is_extract(e3, lo, hi, e4) &&
        lo == 0 && hi == m_bv.get_bv_size(e4) - 2 &&
        m().is_ite(e2, t1, t2, t3) &&
        m().is_eq(t1, c1, c2) &&
        m_bv.is_numeral(c1, k, sz) && k.is_one() && sz == 1 &&
        m_bv.is_extract(c2, lo1, hi1, c3) && lo1 == h1 + 1 && hi1 == lo1 &&
        c3 == e4 &&
        m_arith.is_numeral(t2, )) {

    }
#endif
    return false;
}

expr* bv2int_rewriter::mk_sbv2int(expr* b) {
    //
    // ite(bit1 = b[n-1:n-1], bv2int(b[0:n-2]) - 2^{n-1}, bv2int(b[0:n-2]))    
    // 
    expr* bv1 = m_bv.mk_numeral(1, 1);
    unsigned n = m_bv.get_bv_size(b);
    expr* c = m().mk_eq(bv1, m_bv.mk_extract(n-1, n-1, b));
    expr* e = m_bv.mk_bv2int(m_bv.mk_extract(n-2, 0, b));
    expr* t = m_arith.mk_sub(e, m_arith.mk_numeral(power(rational(2), n-1), true));
    return m().mk_ite(c, t, e);
} 

expr* bv2int_rewriter::mk_extend(unsigned sz, expr* b, bool is_signed) {
    if (sz == 0) {
        return b;
    }
	if (sz > m_ctx.get_max_num_bits()) {
		throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
	}
    rational r;
    unsigned bv_sz;
    if (is_signed) {
        return m_bv.mk_sign_extend(sz, b);
    }
    else if (m_bv.is_numeral(b, r, bv_sz)) {
        return m_bv.mk_numeral(r, bv_sz + sz);
    }
    else {
        return m_bv.mk_zero_extend(sz, b);
    }
}

template class rewriter_tpl<bv2int_rewriter_cfg>;



 
