/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_bounds.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include"bv_bounds.h"
#include"ast_smt2_pp.h"

bv_bounds::~bv_bounds() {
    reset();
}

bv_bounds::conv_res bv_bounds::record(app * v, numeral lo, numeral hi, bool negated, vector<ninterval>& nis) {
    TRACE("bv_bounds", tout << "record0 " << mk_ismt2_pp(v, m_m) << ":" << (negated ? "~[" : "[") << lo << ";" << hi << "]" << std::endl;);
    const unsigned bv_sz = m_bv_util.get_bv_size(v);
    const numeral& zero = numeral::zero();
    const numeral& one = numeral::one();
    SASSERT(zero <= lo);
    SASSERT(lo <= hi);
    SASSERT(hi < numeral::power_of_two(bv_sz));
    numeral vmax, vmin;
    const bool has_upper = m_unsigned_uppers.find(v, vmax);
    const bool has_lower = m_unsigned_lowers.find(v, vmin);
    if (!has_lower) vmin = numeral::zero();
    if (!has_upper) vmax = (numeral::power_of_two(bv_sz) - one);
    bool lo_min = lo <= vmin;
    bool hi_max = hi >= vmax;
    if (negated) {
        if (lo_min && hi_max) return UNSAT;
        if (lo > vmax) return CONVERTED;
        if (hi < vmin) return CONVERTED;
        if (lo_min) {
            negated = false; lo = hi + one; hi = vmax;
            lo_min = lo <= vmin;
            hi_max = true;
        } else if (hi_max)  {
            negated = false; hi = lo - one; lo = vmin;
            hi_max = hi >= vmax;
            lo_min = true;
        }
        SASSERT(zero <= lo);
        SASSERT(lo <= hi);
        SASSERT(hi < numeral::power_of_two(bv_sz));
    }
    if (lo_min) lo = vmin;
    if (hi_max) hi = vmax;
    TRACE("bv_bounds", tout << "record1 " << mk_ismt2_pp(v, m_m) << ":" << (negated ? "~[" : "[") << lo << ";" << hi << "]" << std::endl;);
    if (lo > hi) return negated ? CONVERTED : UNSAT;
    if (lo_min && hi_max) return negated ? UNSAT : CONVERTED;
    nis.resize(nis.size() + 1);
    nis.back().v = v;
    nis.back().lo = lo;
    nis.back().hi = hi;
    nis.back().negated = negated;
    return CONVERTED;
}

bool bv_bounds::is_uleq(expr * e, expr * & v, numeral & c) {
    // To detect the following rewrite from bv_rewriter:
    //   m().mk_and(
    //   m().mk_eq(m_mk_extract(bv_sz - 1, first_non_zero + 1, a), m_util.mk_numeral(numeral(0), bv_sz - first_non_zero - 1)),
    //   m_util.mk_ule(m_mk_extract(first_non_zero, 0, a), m_mk_extract(first_non_zero, 0, b)));
    expr * eq;
    expr * eql;
    expr * eqr;
    expr * ule;
    expr * ulel;
    expr * uler;
    numeral eqr_val, uleqr_val;
    unsigned eqr_sz, uleqr_sz;
    if (!m_m.is_and(e, eq, ule)) return false;
    if (!m_m.is_eq(eq, eql, eqr)) return false;
    if (!m_bv_util.is_bv_ule(ule, ulel, uler)) return false;
    if (!m_bv_util.is_extract(eql)) return false;
    expr * const eql0 = to_app(eql)->get_arg(0);
    const unsigned eql0_sz = m_bv_util.get_bv_size(eql0);
    if (m_bv_util.get_extract_high(eql) != (eql0_sz - 1)) return false;
    if (!m_bv_util.is_numeral(eqr, eqr_val, eqr_sz)) return false;
    if (!eqr_val.is_zero()) return false;
    if (!m_bv_util.is_extract(ulel)) return false;
    expr * const ulel0 = to_app(ulel)->get_arg(0);
    if (ulel0 != eql0) return false;
    if ((m_bv_util.get_extract_high(ulel) + 1) != m_bv_util.get_extract_low(eql)) return false;
    if (m_bv_util.get_extract_low(ulel) != 0) return false;
    if (!m_bv_util.is_numeral(uler, uleqr_val, uleqr_sz)) return false;
    SASSERT(m_bv_util.get_bv_size(ulel0) == uleqr_sz + eqr_sz);
    v = ulel0;
    c = uleqr_val;
    return true;
}

bv_bounds::conv_res bv_bounds::convert(expr * e, vector<ninterval>& nis, bool negated) {
    TRACE("bv_bounds", tout << "new constraint: " << (negated ? "~" : "" ) << mk_ismt2_pp(e, m_m) << std::endl;);

    if (m_m.is_not(e)) {
        negated = !negated;
        e = to_app(e)->get_arg(0);
    }

    expr *lhs, *rhs;
    numeral val, val1;
    unsigned bv_sz1;

    if (0) {
        if (m_m.is_eq(e, lhs, rhs) && to_bound(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz1)) {
            return record(to_app(lhs), val, val, negated, nis);
        }

        if (m_m.is_eq(e, lhs, rhs) && to_bound(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz1)) {
            return record(to_app(rhs), val, val, negated, nis);
        }
    }

    if (is_uleq(e, lhs, val) && to_bound(lhs)) {
        return record(to_app(lhs), numeral::zero(), val, negated, nis);
    }

    if (1) {
        numeral rhs_val;
        unsigned rhs_sz;
        if (m_m.is_eq(e, lhs, rhs)
                && m_bv_util.is_numeral(rhs, rhs_val, rhs_sz)
                && rhs_val.is_zero()
                && m_bv_util.is_extract(lhs)) {
            expr * const lhs0 = to_app(lhs)->get_arg(0);
            const unsigned lhs0_sz = m_bv_util.get_bv_size(lhs0);
            if (m_bv_util.get_extract_high(lhs)+1 == lhs0_sz) {
                const  numeral u = numeral::power_of_two(m_bv_util.get_extract_low(lhs)) - numeral::one();
                return record(to_app(lhs0), numeral::zero(), u, negated, nis);
            }
        }
    }

    if (m_bv_util.is_bv_ule(e, lhs, rhs)) {
        unsigned bv_sz = m_bv_util.get_bv_size(lhs);
        // unsigned inequality with one variable and a constant
        if (to_bound(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz)) // v <= val
            return record(to_app(lhs), numeral::zero(), val, negated, nis);
        if (to_bound(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz)) // val <= v
            return record(to_app(rhs), val, numeral::power_of_two(bv_sz) - numeral::one(), negated, nis);

        // unsigned inequality with one variable, constant, and addition
        expr *t1, *t2;
        if (m_bv_util.is_bv_add(lhs, t1, t2)
                && m_bv_util.is_numeral(t1, val, bv_sz)
                && to_bound(t2)
                && t2 == rhs) {  // val + v <= v
            if (val.is_zero()) return negated ? UNSAT : CONVERTED;
            SASSERT(val.is_pos());
            const numeral mod = numeral::power_of_two(bv_sz);
            return record(to_app(rhs), mod - val, mod - numeral::one(), negated, nis);
        }

        if (m_bv_util.is_bv_add(rhs, t1, t2)
                && m_bv_util.is_numeral(t1, val, bv_sz)
                && to_bound(t2)
                && m_bv_util.is_numeral(lhs, val1, bv_sz1)) {  // val1 <= val + v
            SASSERT(bv_sz1 == bv_sz);
            const numeral mod = numeral::power_of_two(bv_sz);
            if (val1.is_zero()) return negated ? UNSAT : CONVERTED;
            if (val1 < val) {
                const numeral nl = mod - val;
                const numeral nh = mod + val1 - val - numeral::one();
                return nl <= nh ? record(to_app(t2), nl, nh, !negated, nis) : (negated ? UNSAT : CONVERTED);
            }
            else {
                const numeral l = val1 - val;
                const numeral h = mod - val - numeral::one();
                return l <= h ? record(to_app(t2), l, h, negated, nis) : (negated ? CONVERTED : UNSAT);
            }
        }

        if (m_bv_util.is_bv_add(lhs, t1, t2)
                && m_bv_util.is_numeral(t1, val, bv_sz)
                && to_bound(t2)
                && m_bv_util.is_numeral(rhs, val1, bv_sz1)) {  // val + v <= val1
            SASSERT(bv_sz1 == bv_sz);
            if (!val.is_pos() || !val1.is_pos()) return UNDEF;
            const numeral mod = numeral::power_of_two(bv_sz);
            if (val <= val1) {
                const numeral nl = val1 - val + numeral::one();
                const numeral nh = mod - val - numeral::one();
                return nl <= nh ? record(to_app(t2), nl, nh, !negated, nis) : (negated ? UNSAT : CONVERTED);
            }
            else {
                const numeral l = mod - val;
                const numeral h = l + val1;
                return record(to_app(t2), l, h, negated, nis);
            }
        }

        // v + c1 <= v + c2
        app * v1(NULL), *v2(NULL);
        numeral val1, val2;
        if (is_constant_add(bv_sz, lhs, v1, val1)
                && is_constant_add(bv_sz, rhs, v2, val2)
                && v1 == v2) {
            if (val1 == val2) return negated ? UNSAT : CONVERTED;
            const numeral mod = numeral::power_of_two(bv_sz);
            if (val1 < val2) {
                SASSERT(val1 < (mod - numeral::one()));
                SASSERT(val2 > numeral::zero());
                return record(v1, mod - val2, mod - val1 - numeral::one(), !negated, nis);
            }
            else {
                SASSERT(val1 > val2);
                SASSERT(val2 < (mod - numeral::one()));
                SASSERT(val1 > numeral::zero());
                return record(v1, mod - val1, mod - val2 - numeral::one(), negated, nis);
            }
        }
    }

        if (m_bv_util.is_bv_sle(e, lhs, rhs)) {
                unsigned bv_sz = m_bv_util.get_bv_size(lhs);
                // signed inequality with one variable and a constant
                if (to_bound(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz)) { // v <= val
                        val = m_bv_util.norm(val, bv_sz, true);
                        return convert_signed(to_app(lhs), -numeral::power_of_two(bv_sz - 1), val, negated, nis);
                }
                if (to_bound(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz)) { // val <= v
                        val = m_bv_util.norm(val, bv_sz, true);
                        return convert_signed(to_app(rhs), val, numeral::power_of_two(bv_sz - 1) - numeral::one(), negated, nis);
                }
        }

        return UNDEF;
}

void bv_bounds::reset() {
    intervals_map::iterator it = m_negative_intervals.begin();
    const intervals_map::iterator end = m_negative_intervals.end();
    for (; it != end; ++it) dealloc(it->m_value);
}

br_status bv_bounds::rewrite(unsigned limit, func_decl * f, unsigned num, expr * const * args, expr_ref& result) {
    if (!m_m.is_bool(f->get_range())) return BR_FAILED;
    const decl_kind k = f->get_decl_kind();
    if ((k != OP_OR && k != OP_AND) || num > limit) return BR_FAILED;
    const bool negated = k == OP_OR;
    vector<ninterval> nis;
    vector<unsigned> lengths;
    vector<bool> ignore;
    unsigned nis_head = 0;
    for (unsigned i = 0; i < num && m_okay; ++i) {
        expr * const curr = args[i];
        const conv_res cr = convert(curr, nis, negated);
        ignore.push_back(cr == UNDEF);
        switch (cr) {
            case UNDEF: continue;
            case UNSAT: m_okay = false; break;
            case CONVERTED:
                        {
                            for (unsigned i = nis_head; i < nis.size(); ++i) {
                                const ninterval& ni = nis[i];
                                m_okay = m_okay && add_bound_unsigned(ni.v, ni.lo, ni.hi, ni.negated);
                            }
                            lengths.push_back(nis.size());
                            nis_head = nis.size();
                            break;
                        }
            default: UNREACHABLE();
        }
    }
    if (!m_okay || !is_sat()) {
        result = negated ?  m_m.mk_true() : m_m.mk_false();
        return BR_DONE;
    }
    nis_head = 0;
    unsigned count = 0;
    expr_ref_vector nargs(m_m);
    bool has_singls = false;
    for (unsigned i = 0; i < num && m_okay; ++i) {
        TRACE("bv_bounds", tout << "check red: " << mk_ismt2_pp(args[i], m_m) << std::endl;);
        if (ignore[i]) {
            TRACE("bv_bounds", tout << "unprocessed" << std::endl;);
            nargs.push_back(args[i]);
            continue;
        }
        SASSERT(nis_head <= lengths[count]);
        const bool redundant = nis_head == lengths[count];
        bool is_singl = false;
        if (nis_head < lengths[count]) {
            app * const v = nis[nis_head].v;
            numeral th, tl;
            const unsigned bv_sz = m_bv_util.get_bv_size(v);
            const bool has_upper = m_unsigned_uppers.find(v, th);
            const bool has_lower = m_unsigned_lowers.find(v, tl);
            const numeral& one = numeral::one();
            if (!has_lower) tl = numeral::zero();
            if (!has_upper) th = (numeral::power_of_two(bv_sz) - one);
            TRACE("bv_bounds", tout << "bounds: " << mk_ismt2_pp(v, m_m) << "[" << tl << "-" << th << "]" << std::endl;);
            is_singl = tl == th;
            nis_head = lengths[count];
        }
        if (!redundant && !is_singl) nargs.push_back(args[i]);
        has_singls |= is_singl;
        CTRACE("bv_bounds", redundant, tout << "redundant: " << mk_ismt2_pp(args[i], m_m) << std::endl;);
        ++count;
    }

    if (nargs.size() == num && !has_singls) return BR_FAILED;

    expr_ref eq(m_m);
    for (bv_bounds::bound_map::iterator i = m_singletons.begin(); i != m_singletons.end(); ++i) {
        app * const v = i->m_key;
        const rational val = i->m_value;
        eq = m_m.mk_eq(v, bvu().mk_numeral(val, v->get_decl()->get_range()));
        if (negated) eq = m_m.mk_not(eq);
        nargs.push_back(eq);
    }

    switch (nargs.size()) {
        case 0: result = negated ? m_m.mk_false() : m_m.mk_true(); return BR_DONE;
        case 1: result = nargs.get(0); return BR_DONE;
        default: result = negated ? m_m.mk_or(nargs.size(), nargs.c_ptr())
                                  : m_m.mk_and(nargs.size(), nargs.c_ptr());
                 return BR_DONE;
    }
}

bool bv_bounds::add_constraint(expr* e) {
    TRACE("bv_bounds", tout << "new constraint" << mk_ismt2_pp(e, m_m) << std::endl;);
    if (!m_okay) return false;

    bool negated = false;
    if (m_m.is_not(e)) {
        negated = true;
        e = to_app(e)->get_arg(0);
    }

    expr *lhs, *rhs;
    numeral val, val1;
    unsigned bv_sz1;

    if (0) {
        if (m_m.is_eq(e, lhs, rhs) && to_bound(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz1)) {
            return add_bound_unsigned(to_app(lhs), val, val, negated);
        }

        if (m_m.is_eq(e, lhs, rhs) && to_bound(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz1)) {
            return add_bound_unsigned(to_app(rhs), val, val, negated);
        }
    }


    if (m_bv_util.is_bv_ule(e, lhs, rhs)) {
        unsigned bv_sz = m_bv_util.get_bv_size(lhs);
        // unsigned inequality with one variable and a constant
        if (to_bound(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz)) // v <= val
            return add_bound_unsigned(to_app(lhs), numeral::zero(), val, negated);
        if (to_bound(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz)) // val <= v
            return add_bound_unsigned(to_app(rhs), val, numeral::power_of_two(bv_sz) - numeral::one(), negated);

        // unsigned inequality with one variable, constant, and addition
        expr *t1, *t2;
        if (m_bv_util.is_bv_add(lhs, t1, t2)
                && m_bv_util.is_numeral(t1, val, bv_sz)
                && to_bound(t2)
                && t2 == rhs) {  // val + v <= v
            if (!val.is_pos()) return m_okay;
            const numeral mod = numeral::power_of_two(bv_sz);
            return add_bound_unsigned(to_app(rhs), mod - val, mod - numeral::one(), negated);
        }

        if (m_bv_util.is_bv_add(rhs, t1, t2)
                && m_bv_util.is_numeral(t1, val, bv_sz)
                && to_bound(t2)
                && m_bv_util.is_numeral(lhs, val1, bv_sz1)) {  // val1 <= val + v
            SASSERT(bv_sz1 == bv_sz);
            if (!val.is_pos() || !val1.is_pos()) return m_okay;
            const numeral mod = numeral::power_of_two(bv_sz);
            if (val1 < val) {
                const numeral nl = mod - val;
                const numeral nh = mod + val1 - val - numeral::one();
                return nl <= nh ? add_bound_unsigned(to_app(t2), nl, nh, !negated) : m_okay;
            }
            else {
                const numeral l = val1 - val;
                const numeral h = mod - val - numeral::one();
                return l <= h ? add_bound_unsigned(to_app(t2), l, h, negated) : m_okay;
            }
        }

        if (m_bv_util.is_bv_add(lhs, t1, t2)
                && m_bv_util.is_numeral(t1, val, bv_sz)
                && to_bound(t2)
                && m_bv_util.is_numeral(rhs, val1, bv_sz1)) {  // val + v <= val1
            SASSERT(bv_sz1 == bv_sz);
            if (!val.is_pos() || !val1.is_pos()) return m_okay;
            const numeral mod = numeral::power_of_two(bv_sz);
            if (val <= val1) {
                const numeral nl = val1 - val + numeral::one();
                const numeral nh = mod - val - numeral::one();
                return nl <= nh ? add_bound_unsigned(to_app(t2), nl, nh, !negated) : m_okay;
            }
            else {
                const numeral l = mod - val;
                const numeral h = l + val1;
                return add_bound_unsigned(to_app(t2), l, h, negated);
            }
        }

        // v + c1 <= v + c2
        app * v1(NULL), *v2(NULL);
        numeral val1, val2;
        if (is_constant_add(bv_sz, lhs, v1, val1)
                && is_constant_add(bv_sz, rhs, v2, val2)
                && v1 == v2) {
            if (val1 == val2) return m_okay;
            const numeral mod = numeral::power_of_two(bv_sz);
            if (val1 < val2) {
                SASSERT(val1 < (mod - numeral::one()));
                SASSERT(val2 > numeral::zero());
                return add_bound_unsigned(v1, mod - val2, mod - val1 - numeral::one(), !negated);
            }
            else {
                SASSERT(val1 > val2);
                SASSERT(val2 < (mod - numeral::one()));
                SASSERT(val1 > numeral::zero());
                return add_bound_unsigned(v1, mod - val1, mod - val2 - numeral::one(), negated);
            }
        }
    }

    if (m_bv_util.is_bv_sle(e, lhs, rhs)) {
        unsigned bv_sz = m_bv_util.get_bv_size(lhs);
        // signed inequality with one variable and a constant
        if (to_bound(lhs) && m_bv_util.is_numeral(rhs, val, bv_sz)) { // v <= val
            val = m_bv_util.norm(val, bv_sz, true);
            return add_bound_signed(to_app(lhs), -numeral::power_of_two(bv_sz - 1), val, negated);
        }
        if (to_bound(rhs) && m_bv_util.is_numeral(lhs, val, bv_sz)) { // val <= v
            val = m_bv_util.norm(val, bv_sz, true);
            return add_bound_signed(to_app(rhs), val, numeral::power_of_two(bv_sz - 1) - numeral::one(), negated);
        }
    }

    return m_okay;
}

bool bv_bounds::add_bound_unsigned(app * v, numeral a, numeral b, bool negate) {
    TRACE("bv_bounds", tout << "bound_unsigned " << mk_ismt2_pp(v, m_m) << ": " << (negate ? "~[" : "[") << a << ";" << b << "]" << std::endl;);
    const unsigned bv_sz = m_bv_util.get_bv_size(v);
    const numeral& zero = numeral::zero();
    const numeral& one = numeral::one();
    SASSERT(zero <= a);
    SASSERT(a <= b);
    SASSERT(b < numeral::power_of_two(bv_sz));
    const bool a_min = a == zero;
    const bool b_max = b == (numeral::power_of_two(bv_sz) - one);
    if (negate) {
        if (a_min && b_max) return m_okay = false;
        if (a_min) return bound_lo(v, b + one);
        if (b_max) return bound_up(v, a - one);
        return add_neg_bound(v, a, b);
    }
    else {
        if (!a_min) m_okay &= bound_lo(v, a);
        if (!b_max) m_okay &= bound_up(v, b);
        return m_okay;
    }
}

bv_bounds::conv_res bv_bounds::convert_signed(app * v, numeral a, numeral b, bool negate, vector<ninterval>& nis) {
    TRACE("bv_bounds", tout << "convert_signed " << mk_ismt2_pp(v, m_m) << ":" << (negate ? "~[" : "[") << a << ";" << b << "]" << std::endl;);
    const unsigned bv_sz = m_bv_util.get_bv_size(v);
    SASSERT(a <= b);
    const numeral& zero = numeral::zero();
    const numeral& one = numeral::one();
    const bool a_neg = a < zero;
    const bool b_neg = b < zero;
    if (!a_neg && !b_neg) return record(v, a, b, negate, nis);
    const numeral mod = numeral::power_of_two(bv_sz);
    if (a_neg && b_neg) return record(v, mod + a, mod + b, negate, nis);
    SASSERT(a_neg && !b_neg);
    if (negate) {
        const conv_res r1 = record(v, mod + a, mod - one, true, nis);
        const conv_res r2 = record(v, zero, b, true, nis);
        return r1 == UNSAT || r2 == UNSAT ? UNSAT : CONVERTED;
    }
    else {
        const numeral l = b + one;
        const numeral u = mod + a - one;
        return l <= u ? record(v, l, u, true, nis) : CONVERTED;
    }
}

bool bv_bounds::add_bound_signed(app * v, numeral a, numeral b, bool negate) {
    TRACE("bv_bounds", tout << "bound_signed " << mk_ismt2_pp(v, m_m) << ":" << (negate ? "~" : " ") << a << ";" << b << std::endl;);
    const unsigned bv_sz = m_bv_util.get_bv_size(v);
    SASSERT(a <= b);
    const numeral& zero = numeral::zero();
    const numeral& one = numeral::one();
    const bool a_neg = a < zero;
    const bool b_neg = b < zero;
    if (!a_neg && !b_neg) return add_bound_unsigned(v, a, b, negate);
    const numeral mod = numeral::power_of_two(bv_sz);
    if (a_neg && b_neg) return add_bound_unsigned(v, mod + a, mod + b, negate);
    SASSERT(a_neg && !b_neg);
    if (negate) {
        return add_bound_unsigned(v, mod + a, mod - one, true)
            && add_bound_unsigned(v, zero, b, true);
    }
    else {
        const numeral l = b + one;
        const numeral u = mod + a - one;
        return (l <= u) ? add_bound_unsigned(v, l, u, true) : m_okay;
    }
}

bool bv_bounds::bound_lo(app * v, numeral l) {
    SASSERT(in_range(v, l));
    TRACE("bv_bounds", tout << "lower " << mk_ismt2_pp(v, m_m) << ":" << l << std::endl;);
    // l <= v
    bound_map::obj_map_entry * const entry = m_unsigned_lowers.insert_if_not_there2(v, l);
    if (!(entry->get_data().m_value < l)) return m_okay;
    // improve bound
    entry->get_data().m_value = l;
    return m_okay;
}

bool bv_bounds::bound_up(app * v, numeral u) {
    SASSERT(in_range(v, u));
    TRACE("bv_bounds", tout << "upper " << mk_ismt2_pp(v, m_m) << ":" << u << std::endl;);
    // v <= u
    bound_map::obj_map_entry * const entry = m_unsigned_uppers.insert_if_not_there2(v, u);
    if (!(u < entry->get_data().m_value)) return m_okay;
    // improve bound
    entry->get_data().m_value = u;
    return m_okay;
}

bool bv_bounds::add_neg_bound(app * v, numeral a, numeral b) {
    TRACE("bv_bounds", tout << "negative bound " << mk_ismt2_pp(v, m_m) << ":" << a << ";" << b << std::endl;);
    bv_bounds::interval negative_interval(a, b);
    SASSERT(m_bv_util.is_bv(v));
    SASSERT(a >= numeral::zero());
    SASSERT(b < numeral::power_of_two(m_bv_util.get_bv_size(v)));
    SASSERT(a <= b);

    intervals_map::obj_map_entry * const e = m_negative_intervals.find_core(v);
    intervals * ivs(NULL);
    if (e == 0) {
        ivs = alloc(intervals);
        m_negative_intervals.insert(v, ivs);
    }
    else {
        ivs = e->get_data().get_value();
    }
    ivs->push_back(negative_interval);
    return m_okay;
}


bool bv_bounds::is_sat() {
    if (!m_okay) return false;
    obj_hashtable<app>   seen;
    obj_hashtable<app>::entry *dummy;

    for (bound_map::iterator i = m_unsigned_lowers.begin(); i != m_unsigned_lowers.end(); ++i) {
        app * const v = i->m_key;
        if (!seen.insert_if_not_there_core(v, dummy)) continue;
        if (!is_sat(v)) return false;
    }

    for (bound_map::iterator i = m_unsigned_uppers.begin(); i != m_unsigned_uppers.end(); ++i) {
        app * const v = i->m_key;
        if (!seen.insert_if_not_there_core(v, dummy)) continue;
        if (!is_sat(v)) return false;
    }

    for (intervals_map::iterator i = m_negative_intervals.begin(); i != m_negative_intervals.end(); ++i) {
        app * const v = i->m_key;
        if (!seen.insert_if_not_there_core(v, dummy)) continue;
        if (!is_sat(v)) return false;
    }

    return true;
}

struct interval_comp_t {
    bool operator() (bv_bounds::interval i, bv_bounds::interval j) {
        return (i.first < j.first);
    }
} interval_comp;


void bv_bounds::record_singleton(app * v, numeral& singleton_value) {
    TRACE("bv_bounds", tout << "singleton:" << mk_ismt2_pp(v, m_m) << ":" << singleton_value << std::endl;);
    SASSERT(!m_singletons.find(v, singleton_value));
    m_singletons.insert(v, singleton_value);
}

bool bv_bounds::is_sat(app * v) {
    TRACE("bv_bounds", tout << "is_sat " << mk_ismt2_pp(v, m_m) << std::endl;);
    const bool rv = is_sat_core(v);
    TRACE("bv_bounds", tout << "is_sat " << mk_ismt2_pp(v, m_m) << "\nres: " << rv << std::endl;);
    return rv;
}

bool bv_bounds::is_sat_core(app * v) {
    SASSERT(m_bv_util.is_bv(v));
    if (!m_okay) return false;
    unsigned const bv_sz = m_bv_util.get_bv_size(v);
    numeral lower, upper;
    const bool has_upper = m_unsigned_uppers.find(v, upper);
    const bool has_lower = m_unsigned_lowers.find(v, lower);
    if (has_upper && has_lower && lower > upper) return false;
    const numeral& one = numeral::one();
    if (!has_lower) lower = numeral::zero();
    if (!has_upper) upper = (numeral::power_of_two(bv_sz) - one);
    TRACE("bv_bounds", tout << "is_sat bound:" << lower << "-" << upper << std::endl;);
    intervals * negative_intervals(NULL);
    const bool has_neg_intervals = m_negative_intervals.find(v, negative_intervals);
    bool is_sat(false);
    numeral new_lo = lower;
    numeral new_hi = lower - one;
    numeral ptr = lower;
    if (has_neg_intervals) {
        SASSERT(negative_intervals != NULL);
        std::sort(negative_intervals->begin(), negative_intervals->end(), interval_comp);
        intervals::const_iterator e = negative_intervals->end();
        for (intervals::const_iterator i = negative_intervals->begin(); i != e; ++i) {
            const numeral negative_lower = i->first;
            const numeral negative_upper = i->second;
            if (ptr > negative_upper) continue;
            if (ptr < negative_lower) {
                if (!is_sat) new_lo = ptr;
                new_hi = negative_lower - one;
                if (new_hi > upper) new_hi = upper;
                is_sat = true;
            }
            TRACE("bv_bounds", tout << "is_sat new_lo, new_hi:" << new_lo << "-" << new_hi << std::endl;);
            ptr = negative_upper + one;
            TRACE("bv_bounds", tout << "is_sat ptr, new_hi:" << ptr << "-" << new_hi << std::endl;);
            if (ptr > upper) break;
        }
    }

    if (ptr <= upper) {
        if (!is_sat) new_lo = ptr;
        new_hi = upper;
        is_sat = true;
    }
    if (new_hi < upper) bound_up(v, new_hi);
    if (new_lo > lower) bound_lo(v, new_lo);
    TRACE("bv_bounds", tout << "is_sat new_lo, new_hi:" << new_lo << "-" << new_hi << std::endl;);

    const bool is_singleton = is_sat && new_hi == new_lo;
    if (is_singleton) record_singleton(v, new_lo);

    return is_sat;
}
