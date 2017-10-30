/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv2real_rewriter.cpp

Abstract:

    Basic rewriting rules for bv2real propagation.

Author:

    Nikolaj (nbjorner) 2011-08-05

Notes:

--*/
#include "tactic/arith/bv2real_rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"


bv2real_util::bv2real_util(ast_manager& m, rational const& default_root, rational const& default_divisor, unsigned max_num_bits) : 
    m_manager(m), 
    m_arith(m), 
    m_bv(m), 
    m_decls(m),
    m_pos_le(m),
    m_pos_lt(m),
    m_side_conditions(m),
    m_default_root(default_root), 
    m_default_divisor(default_divisor), 
    m_max_divisor(rational(2)*default_divisor),
    m_max_num_bits(max_num_bits) {
    sort* real = m_arith.mk_real();
    sort* domain[2] = { real, real };
    m_pos_lt = m.mk_fresh_func_decl("<","",2,domain,m.mk_bool_sort());
    m_pos_le = m.mk_fresh_func_decl("<=","",2,domain,m.mk_bool_sort());
    m_decls.push_back(m_pos_lt);
    m_decls.push_back(m_pos_le);
}

bool bv2real_util::is_bv2real(func_decl* f) const {
    return m_decl2sig.contains(f);
}

bool bv2real_util::is_bv2real(func_decl* f, unsigned num_args, expr* const* args, 
                              expr*& m, expr*& n, rational& d, rational& r) const {
    bvr_sig sig;
    if (!m_decl2sig.find(f, sig)) {
        return false;
    }
    SASSERT(num_args == 2);
    m = args[0];
    n = args[1];
    d = sig.m_d;
    r = sig.m_r;
    SASSERT(sig.m_d.is_int() && sig.m_d.is_pos());
    SASSERT(sig.m_r.is_int() && sig.m_r.is_pos());
    SASSERT(m_bv.get_bv_size(m) == sig.m_msz);
    SASSERT(m_bv.get_bv_size(n) == sig.m_nsz);
    return true;
}

bool bv2real_util::is_bv2real(expr* e, expr*& m, expr*& n, rational& d, rational& r) const {
    if (!is_app(e)) return false;
    func_decl* f = to_app(e)->get_decl();
    return is_bv2real(f, to_app(e)->get_num_args(), to_app(e)->get_args(), m, n, d, r);
}

class bv2real_util::contains_bv2real_proc {
    bv2real_util const& m_util;
public:
    class found {};
    contains_bv2real_proc(bv2real_util const& u): m_util(u) {}
    void operator()(app* a) {
        if (m_util.is_bv2real(a->get_decl())) {
            throw found();
        }
    }
    void operator()(var*) {}
    void operator()(quantifier*) {}
};

bool bv2real_util::contains_bv2real(expr* e) const {
    contains_bv2real_proc p(*this);
    try {
        for_each_expr(p, e);
    }
    catch (contains_bv2real_proc::found) {
        return true;
    }
    return false;
}

bool bv2real_util::mk_bv2real(expr* _s, expr* _t, rational& d, rational& r, expr_ref& result) {
    expr_ref s(_s,m()), t(_t,m());
    if (align_divisor(s, t, d)) {
        result = mk_bv2real_c(s, t, d, r);
        return true;
    }
    else {
        return false;
    }
}

expr* bv2real_util::mk_bv2real_c(expr* s, expr* t, rational const& d, rational const& r) {
    bvr_sig sig;
    sig.m_msz = m_bv.get_bv_size(s);
    sig.m_nsz = m_bv.get_bv_size(t);
    sig.m_d = d;
    sig.m_r = r;
    func_decl* f;
    if (!m_sig2decl.find(sig, f)) {
        sort* domain[2] = { m_manager.get_sort(s), m_manager.get_sort(t) };
        sort* real = m_arith.mk_real();
        f = m_manager.mk_fresh_func_decl("bv2real", "", 2, domain, real);
        m_decls.push_back(f);
        m_sig2decl.insert(sig, f);
        m_decl2sig.insert(f, sig);
    }
    return m_manager.mk_app(f, s, t);
}

void bv2real_util::mk_bv2real_reduced(expr* s, expr* t, rational const& d, rational const& r, expr_ref & result) {
    expr_ref s1(m()), t1(m()), r1(m());
    rational num;
    mk_sbv2real(s, s1);
    mk_sbv2real(t, t1);
    mk_div(s1, d, s1);
    mk_div(t1, d, t1);
    r1 = a().mk_power(a().mk_numeral(r, false), a().mk_numeral(rational(1,2),false));
    t1 = a().mk_mul(t1, r1);
    result = a().mk_add(s1, t1);
}    

void bv2real_util::mk_div(expr* e, rational const& d, expr_ref& result) {
    result = a().mk_div(e, a().mk_numeral(rational(d), false));
}

void bv2real_util::mk_sbv2real(expr* e, expr_ref& result) {
    rational r;
    unsigned bv_size = m_bv.get_bv_size(e);
    rational bsize = power(rational(2), bv_size);
    expr_ref bvr(a().mk_to_real(m_bv.mk_bv2int(e)), m());
    expr_ref c(m_bv.mk_sle(m_bv.mk_numeral(rational(0), bv_size), e), m());
    result = m().mk_ite(c, bvr, a().mk_sub(bvr, a().mk_numeral(bsize, false)));
}


expr* bv2real_util::mk_bv_mul(rational const& n, expr* t) {
    if (n.is_one()) return t;    
    expr* s = mk_sbv(n);
    return mk_bv_mul(s, t);
}

void bv2real_util::align_divisors(expr_ref& s1, expr_ref& s2, expr_ref& t1, expr_ref& t2, rational& d1, rational& d2) {
    if (d1 == d2) {
        return;
    }
    // s/d1 ~ t/d2 <=> lcm*s/d1 ~ lcm*t/d2 <=> (lcm/d1)*s ~ (lcm/d2)*t
    // s/d1 ~ t/d2 <=> s/gcd*d1' ~ t/gcd*d2' <=> d2'*s/lcm ~ d1'*t/lcm

    rational g = gcd(d1,d2);
    rational l = lcm(d1,d2);
    rational d1g = d1/g;
    rational d2g = d2/g;
    s1 = mk_bv_mul(d2g, s1);
    s2 = mk_bv_mul(d2g, s2);
    t1 = mk_bv_mul(d1g, t1);
    t2 = mk_bv_mul(d1g, t2);
    d1 = l;
    d2 = l;
}

expr* bv2real_util::mk_bv_mul(expr* s, expr* t) {
    SASSERT(m_bv.is_bv(s));
    SASSERT(m_bv.is_bv(t));
    if (is_zero(s)) {
        return s;
    }
    if (is_zero(t)) {
        return t;
    }    
    expr_ref s1(s, m()), t1(t, m());
    align_sizes(s1, t1);
    unsigned n = m_bv.get_bv_size(t1);
    unsigned max_bits = get_max_num_bits();
    bool add_side_conds = 2*n > max_bits;
    if (n >= max_bits) {
        // nothing
    }
    else if (2*n > max_bits) {
        s1 = mk_extend(max_bits-n, s1);
        t1 = mk_extend(max_bits-n, t1); 
    }
    else {
        s1 = mk_extend(n, s1);
        t1 = mk_extend(n, t1); 
    }
    if (add_side_conds) {
        add_side_condition(m_bv.mk_bvsmul_no_ovfl(s1, t1));        
        add_side_condition(m_bv.mk_bvsmul_no_udfl(s1, t1));        
    }
    return m_bv.mk_bv_mul(s1, t1);
}

bool bv2real_util::is_zero(expr* n) {
    rational r;
    unsigned sz;
    return m_bv.is_numeral(n, r, sz) && r.is_zero();
}

expr* bv2real_util::mk_bv_add(expr* s, expr* t) {
    SASSERT(m_bv.is_bv(s));
    SASSERT(m_bv.is_bv(t));

    if (is_zero(s)) {
        return t;
    }
    if (is_zero(t)) {
        return s;
    }
    expr_ref s1(s, m()), t1(t, m());
    align_sizes(s1, t1);
    s1 = mk_extend(1, s1);
    t1 = mk_extend(1, t1);
    return m_bv.mk_bv_add(s1, t1);
}

void bv2real_util::align_sizes(expr_ref& s, expr_ref& t) {
    unsigned sz1 = m_bv.get_bv_size(s);
    unsigned sz2 = m_bv.get_bv_size(t);
    if (sz1 > sz2) {
        t = mk_extend(sz1-sz2, t);
    }
    else if (sz1 < sz2) {
        s = mk_extend(sz2-sz1, s);
    }
}

expr* bv2real_util::mk_sbv(rational const& n) {
    SASSERT(n.is_int());
    if (n.is_neg()) {
        rational m = abs(n);
        unsigned nb = m.get_num_bits();
        return m_bv.mk_bv_neg(m_bv.mk_numeral(m, nb+1));
    }
    else {
        unsigned nb = n.get_num_bits();
        return m_bv.mk_numeral(n, nb+1);
    }
}

expr* bv2real_util::mk_bv_sub(expr* s, expr* t) {
    expr_ref s1(s, m()), t1(t, m());
    align_sizes(s1, t1);
    s1 = mk_extend(1, s1);
    t1 = mk_extend(1, t1);
    return m_bv.mk_bv_sub(s1, t1);
}

expr* bv2real_util::mk_extend(unsigned sz, expr* b) {
    if (sz == 0) {
        return b;
    }
    rational r;
    unsigned bv_sz;
    if (m_bv.is_numeral(b, r, bv_sz) && 
        power(rational(2),bv_sz-1) > r) {
        return m_bv.mk_numeral(r, bv_sz + sz);
    }
    return m_bv.mk_sign_extend(sz, b);
}


bool bv2real_util::is_bv2real(expr* n, expr_ref& s, expr_ref& t, rational& d, rational& r) {
    expr* _s, *_t;
    if (is_bv2real(n, _s, _t, d, r)) {
        s = _s;
        t = _t;
        return true;
    }
    rational k;
    bool is_int;
    if (m_arith.is_numeral(n, k, is_int) && !is_int) {
        d = denominator(k);
        r = default_root();
        s = mk_sbv(numerator(k));
        t = mk_sbv(rational(0));
        return true;
    }
    return false;
}

bool bv2real_util::align_divisor(expr_ref& s, expr_ref& t, rational& d) {
    if (d > max_divisor()) {
        //
        // if divisor is over threshold, then divide s and t
        // add side condition that s, t are divisible.
        //
        rational overflow = d / max_divisor();
        if (!overflow.is_int()) return false;
        if (!mk_is_divisible_by(s, overflow)) return false;
        if (!mk_is_divisible_by(t, overflow)) return false;
        d = max_divisor();
    }
    return true;
}

bool bv2real_util::mk_is_divisible_by(expr_ref& s, rational const& _overflow) {
    rational overflow(_overflow);
    SASSERT(overflow.is_int());
    SASSERT(overflow.is_pos());
    SASSERT(!overflow.is_one());
    TRACE("bv2real_rewriter", 
          tout << mk_pp(s, m()) << " " << overflow << "\n";);
    unsigned power2 = 0;
    while ((overflow % rational(2)) == rational(0)) {
        power2++;
        overflow = div(overflow, rational(2));
    }

    if (power2 > 0) {
        unsigned sz = m_bv.get_bv_size(s);
        if (sz <= power2) {
            add_side_condition(m().mk_eq(s, m_bv.mk_numeral(rational(0), sz)));
            s = m_bv.mk_numeral(rational(0), 1);
        }
        else {
            expr* s1 = m_bv.mk_extract(power2-1, 0, s);
            add_side_condition(m().mk_eq(s1, m_bv.mk_numeral(rational(0), power2)));
            s = m_bv.mk_extract(sz-1, power2, s);
        }
    }

    TRACE("bv2real_rewriter", 
          tout << mk_pp(s, m()) << " " << overflow << "\n";);
    
    return overflow.is_one();
}



// ---------------------------------------------------------------------
// bv2real_rewriter

bv2real_rewriter::bv2real_rewriter(ast_manager& m, bv2real_util& util):
    m_manager(m), 
    m_util(util),
    m_bv(m),
    m_arith(m)
{}


br_status bv2real_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    TRACE("bv2real_rewriter", 
          tout << mk_pp(f, m()) << " ";
          for (unsigned i = 0; i < num_args; ++i) {
              tout << mk_pp(args[i], m()) << " ";
          }
          tout << "\n";);
    if(f->get_family_id() == m_arith.get_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_NUM:     return BR_FAILED;
        case OP_LE:      SASSERT(num_args == 2); return mk_le(args[0], args[1], result);
        case OP_GE:      SASSERT(num_args == 2); return mk_ge(args[0], args[1], result);
        case OP_LT:      SASSERT(num_args == 2); return mk_lt(args[0], args[1], result);
        case OP_GT:      SASSERT(num_args == 2); return mk_gt(args[0], args[1], result);
        case OP_ADD:     return mk_add(num_args, args, result);
        case OP_MUL:     return mk_mul(num_args, args, result);
        case OP_SUB:     return mk_sub(num_args, args, result);
        case OP_DIV:     SASSERT(num_args == 2); return mk_div(args[0], args[1], result);
        case OP_IDIV:    return BR_FAILED;
        case OP_MOD:     return BR_FAILED;
        case OP_REM:     return BR_FAILED;
        case OP_UMINUS:  SASSERT(num_args == 1); return mk_uminus(args[0], result);
        case OP_TO_REAL: return BR_FAILED; // TBD
        case OP_TO_INT:  return BR_FAILED; // TBD
        case OP_IS_INT:  return BR_FAILED; // TBD
        default:         return BR_FAILED;
        }
    }
    if (f->get_family_id() == m().get_basic_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_EQ: SASSERT(num_args == 2); return mk_eq(args[0], args[1], result);
        case OP_ITE: SASSERT(num_args == 3); return mk_ite(args[0], args[1], args[2], result); 
        default: return BR_FAILED;
        }
    }
    if (u().is_pos_ltf(f)) {
        SASSERT(num_args == 2);
        return mk_lt_pos(args[0], args[1], result);
    }
    if (u().is_pos_lef(f)) {
        SASSERT(num_args == 2);
        return mk_le_pos(args[0], args[1], result);        
    }

    return BR_FAILED;
}

bool bv2real_rewriter::mk_le(expr* s, expr* t, bool is_pos, bool is_neg, expr_ref& result) {
    expr_ref s1(m()), s2(m()), t1(m()), t2(m());
    rational d1, d2, r1, r2;
    SASSERT(is_pos || is_neg);
    if (u().is_bv2real(s, s1, s2, d1, r1) && u().is_bv2real(t, t1, t2, d2, r2) && 
        r1 == r2 && r1 == rational(2)) {
        //
        //      (s1 + s2*sqrt(2))/d1 <= (t1 + t2*sqrt(2))/d2
        // <=> 
        //
        //      let s1 = s1*d2-t1*d1, t2 = s2*d2-t2*d1
        //      
        // 
        //      s1 + s2*sqrt(2) <= 0
        // <=
        //      s1 + s2*approx(sign(s2),sqrt(2)) <= 0 
        //  or (s1 = 0 & s2 = 0)
        //
        // If s2 is negative use an under-approximation for sqrt(r).
        // If s2 is positive use an over-approximation for sqrt(r).
        // e.g., r = 2, then 5/4 and 3/2 are under/over approximations.
        // Then s1 + s2*approx(sign(s2), r) <= 0 => s1 + s2*sqrt(r) <= 0
        

        u().align_divisors(s1, s2, t1, t2, d1, d2);
        s1 = u().mk_bv_sub(s1, t1);
        s2 = u().mk_bv_sub(s2, t2);
        unsigned s2_size = m_bv.get_bv_size(s2);
        expr_ref le_proxy(m().mk_fresh_const("le_proxy",m().mk_bool_sort()), m());
        u().add_aux_decl(to_app(le_proxy)->get_decl());
        expr_ref gt_proxy(m().mk_not(le_proxy), m());
        expr_ref s2_is_nonpos(m_bv.mk_sle(s2, m_bv.mk_numeral(rational(0), s2_size)), m());
        
        expr_ref under(u().mk_bv_add(u().mk_bv_mul(rational(4), s1), u().mk_bv_mul(rational(5), s2)), m());
        expr_ref z1(m_bv.mk_numeral(rational(0), m_bv.get_bv_size(under)), m());
        expr_ref le_under(m_bv.mk_sle(under, z1), m());
        expr_ref over(u().mk_bv_add(u().mk_bv_mul(rational(2), s1), u().mk_bv_mul(rational(3), s2)), m());
        expr_ref z2(m_bv.mk_numeral(rational(0), m_bv.get_bv_size(over)), m());
        expr_ref le_over(m_bv.mk_sle(over, z2), m());

        // predicate may occur in positive polarity.
        if (is_pos) {
            // s1 + s2*sqrt(2) <= 0  <== s2 <= 0 & s1 + s2*(5/4) <= 0;  4*s1 + 5*s2 <= 0
            expr* e1 = m().mk_implies(m().mk_and(le_proxy, s2_is_nonpos), le_under);
            // s1 + s2*sqrt(2) <= 0  <== s2 > 0 & s1 + s2*(3/2);  0 <=> 2*s1 + 3*s2 <= 0
            expr* e2 = m().mk_implies(m().mk_and(le_proxy, m().mk_not(s2_is_nonpos)), le_over);
            u().add_side_condition(e1);
            u().add_side_condition(e2);
        }
        // predicate may occur in negative polarity.
        if (is_neg) {
            // s1 + s2*sqrt(2) > 0  <== s2 > 0 & s1 + s2*(5/4) > 0;  4*s1 + 5*s2 > 0
            expr* e3 = m().mk_implies(m().mk_and(gt_proxy, m().mk_not(s2_is_nonpos)), m().mk_not(le_under));
            // s1 + s2*sqrt(2) > 0  <== s2 <= 0 & s1 + s2*(3/2) > 0 <=> 2*s1 + 3*s2 > 0
            expr* e4 = m().mk_implies(m().mk_and(gt_proxy, s2_is_nonpos), m().mk_not(le_over));
            u().add_side_condition(e3);
            u().add_side_condition(e4);
        }

        TRACE("bv2real_rewriter", tout << "mk_le\n";);

        if (is_pos) {
            result = le_proxy;
        }
        else {
            result = gt_proxy;
        }
        return true;
    }
    return false;
}

br_status bv2real_rewriter::mk_le_pos(expr * s, expr * t, expr_ref & result) {
    if (mk_le(s, t, true, false, result)) {
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status bv2real_rewriter::mk_lt_pos(expr * s, expr * t, expr_ref & result) {
    if (mk_le(t, s, false, true, result)) {
        return BR_DONE;
    }
    return BR_FAILED;
}


br_status bv2real_rewriter::mk_le(expr * s, expr * t, expr_ref & result) {
    expr_ref s1(m()), s2(m()), t1(m()), t2(m());
    rational d1, d2, r1, r2;

    if (mk_le(s, t, true, true, result)) {
        return BR_DONE;
    }
 
    if (u().is_bv2real(s, s1, s2, d1, r1) && u().is_bv2real(t, t1, t2, d2, r2) && r1 == r2) {
        //
        // somewhat expensive approach without having 
        // polarity information for sound approximation.
        //

        // Convert to:
        //    t1 + t2*sqrt(r) >= 0
        // then to:
        // 
        // (t1 >= 0 && t2 <= 0 => t1^2 >= t2^2*r)
        // (t1 <= 0 && t2 >= 0 => t1^2 <= t2^2*r) 
        // (t1 >= 0 || t2 >= 0)
        // 
        // A cheaper approach is to approximate > under the assumption
        // that > occurs in positive polarity.
        // then if t2 is negative use an over-approximation for sqrt(r)
        // if t2 is positive use an under-approximation for sqrt(r).
        // e.g., r = 2, then 5/4 and 3/2 are under/over approximations.
        // Then t1 + t2*approx(sign(t2), r) > 0 => t1 + t2*sqrt(r) > 0
        //
        u().align_divisors(s1, s2, t1, t2, d1, d2);
        t1 = u().mk_bv_sub(t1, s1);
        t2 = u().mk_bv_sub(t2, s2);
        expr_ref z1(m()), z2(m());
        z1 = m_bv.mk_numeral(rational(0), m_bv.get_bv_size(t1));
        z2 = m_bv.mk_numeral(rational(0), m_bv.get_bv_size(t2));
        
        expr* gz1 = m_bv.mk_sle(z1, t1);
        expr* lz1 = m_bv.mk_sle(t1, z1);
        expr* gz2 = m_bv.mk_sle(z2, t2);
        expr* lz2 = m_bv.mk_sle(t2, z2);
        expr_ref t12(u().mk_bv_mul(t1, t1), m());
        expr_ref t22(u().mk_bv_mul(r1, u().mk_bv_mul(t2, t2)), m());
        u().align_sizes(t12, t22);
        expr* ge  = m_bv.mk_sle(t22, t12);
        expr* le  = m_bv.mk_sle(t12, t22);
        expr* e1  = m().mk_or(gz1, gz2);
        expr* e2  = m().mk_or(m().mk_not(gz1), m().mk_not(lz2), ge);
        expr* e3  = m().mk_or(m().mk_not(gz2), m().mk_not(lz1), le);
        result    = m().mk_and(e1, e2, e3);
        TRACE("bv2real_rewriter", tout << "\n";);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status bv2real_rewriter::mk_lt(expr * arg1, expr * arg2, expr_ref & result) {
    result = m().mk_not(m_arith.mk_le(arg2, arg1));
    return BR_REWRITE2;
}

br_status bv2real_rewriter::mk_ge(expr * arg1, expr * arg2, expr_ref & result) {
    return mk_le(arg2, arg1, result);
}

br_status bv2real_rewriter::mk_gt(expr * arg1, expr * arg2, expr_ref & result) {
    result = m().mk_not(m_arith.mk_le(arg1, arg2));
    return BR_REWRITE2;
}

br_status bv2real_rewriter::mk_ite(expr* c, expr* s, expr* t, expr_ref& result) {
    expr_ref s1(m()), s2(m()), t1(m()), t2(m());
    rational d1, d2, r1, r2;
    if (u().is_bv2real(s, s1, s2, d1, r1) && u().is_bv2real(t, t1, t2, d2, r2) && r1 == r2) {
        u().align_divisors(s1, s2, t1, t2, d1, d2);
        u().align_sizes(s1, t1);
        u().align_sizes(s2, t2);
        if (u().mk_bv2real(m().mk_ite(c, s1, t1), m().mk_ite(c, s2, t2), d1, r1, result)) {
            return BR_DONE;
        }
    }
    return BR_FAILED;
}

br_status bv2real_rewriter::mk_eq(expr * s, expr * t, expr_ref & result) {
    expr_ref s1(m()), s2(m()), t1(m()), t2(m());
    rational d1, d2, r1, r2;
    if (u().is_bv2real(s, s1, s2, d1, r1) && u().is_bv2real(t, t1, t2, d2, r2) && r1 == r2) {
        u().align_divisors(s1, s2, t1, t2, d1, d2);
        u().align_sizes(s1, t1);
        u().align_sizes(s2, t2);
        result = m().mk_and(m().mk_eq(s1, t1), m().mk_eq(s2, t2));
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status bv2real_rewriter::mk_uminus(expr * s, expr_ref & result) {
    expr_ref s1(m()), s2(m());
    rational d1, r1;
    if (u().is_bv2real(s, s1, s2, d1, r1)) {
        s1 = u().mk_extend(1, s1);
        s2 = u().mk_extend(1, s2);
        if (u().mk_bv2real(m_bv.mk_bv_neg(s1), m_bv.mk_bv_neg(s2), d1, r1, result)) {
            return BR_DONE;
        }
    }
    return BR_FAILED;
}

br_status bv2real_rewriter::mk_add(unsigned num_args, expr * const* args, expr_ref& result) {
    br_status r = BR_DONE;
    SASSERT(num_args > 0);
    result = args[0];
    for (unsigned i = 1; r == BR_DONE && i < num_args; ++i) {
        r = mk_add(result, args[i], result);
    }
    return r;
}

br_status bv2real_rewriter::mk_add(expr* s, expr* t, expr_ref& result) {
    expr_ref s1(m()), s2(m()), t1(m()), t2(m());
    rational d1, d2, r1, r2;
    if (u().is_bv2real(s, s1, s2, d1, r1) && u().is_bv2real(t, t1, t2, d2, r2) && r1 == r2) {
        u().align_divisors(s1, s2, t1, t2, d1, d2);
        if (u().mk_bv2real(u().mk_bv_add(s1, t1), u().mk_bv_add(t2, s2), d1, r1, result)) {
            return BR_DONE;
        }
    }
    return BR_FAILED;
}

br_status bv2real_rewriter::mk_mul(unsigned num_args, expr * const* args, expr_ref& result) {
    br_status r = BR_DONE;
    SASSERT(num_args > 0);
    result = args[0];
    for (unsigned i = 1; r == BR_DONE && i < num_args; ++i) {
        r = mk_mul(result, args[i], result);
    }
    return r;
}

br_status bv2real_rewriter::mk_div(expr* s, expr* t, expr_ref& result) {
    return BR_FAILED;
}

br_status bv2real_rewriter::mk_mul(expr* s, expr* t, expr_ref& result) {
    // TBD: optimize
    expr_ref s1(m()), t1(m()), s2(m()), t2(m());
    rational d1, d2, r1, r2;

    if (u().is_bv2real(s, s1, s2, d1, r1) && u().is_bv2real(t, t1, t2, d2, r2) && r1 == r2) {
        // s1*t1 + r1*(s2*t2) + (s1*t2 + s2*t2)*r1
        expr_ref u1(m()), u2(m());
        u1 = u().mk_bv_add(u().mk_bv_mul(s1, t1), u().mk_bv_mul(r1, u().mk_bv_mul(t2, s2)));
        u2 = u().mk_bv_add(u().mk_bv_mul(s1, t2), u().mk_bv_mul(s2, t1));
        rational tmp = d1*d2;
        if (u().mk_bv2real(u1, u2, tmp, r1, result)) {
            return BR_DONE;
        }
    }
    return BR_FAILED;
}

br_status bv2real_rewriter::mk_sub(unsigned num_args, expr * const* args, expr_ref& result) {
    br_status r = BR_DONE;
    SASSERT(num_args > 0);
    result = args[0];
    for (unsigned i = 1; r == BR_DONE && i < num_args; ++i) {
        r = mk_sub(result, args[i], result);
    }
    return r;
}


br_status bv2real_rewriter::mk_sub(expr* s, expr* t, expr_ref& result) {
    expr_ref s1(m()), s2(m()), t1(m()), t2(m());
    rational d1, d2, r1, r2;
    if (u().is_bv2real(s, s1, s2, d1, r1) && u().is_bv2real(t, t1, t2, d2, r2) && r1 == r2) {
        u().align_divisors(s1, s2, t1, t2, d1, d2);
        if (u().mk_bv2real(u().mk_bv_sub(s1, t1), u().mk_bv_sub(s2, t2), d1, r1, result)) {
            return BR_DONE;
        }
    }
    return BR_FAILED;
}




template class rewriter_tpl<bv2real_rewriter_cfg>;


br_status bv2real_elim_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    expr* m, *n;
    rational d, r;
    if (m_util.is_bv2real(f, num_args, args, m, n, d, r)) {
        m_util.mk_bv2real_reduced(m, n, d, r, result);
        return BR_REWRITE_FULL;        
    }
    return BR_FAILED;
}

template class rewriter_tpl<bv2real_elim_rewriter_cfg>;

