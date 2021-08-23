/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bit_blaster_tpl_def.h

Abstract:

    Template for bit-blaster operations

Author:

    Leonardo de Moura (leonardo) 2011-05-02.

Revision History:

--*/
#include "util/rational.h"
#include "util/common_msgs.h"
#include "ast/rewriter/bit_blaster/bit_blaster_tpl.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/rewriter_types.h"


template<typename Cfg>
void bit_blaster_tpl<Cfg>::checkpoint() {
    if (memory::get_allocation_size() > m_max_memory)
        throw rewriter_exception(Z3_MAX_MEMORY_MSG);
    if (!m().inc())
        throw rewriter_exception(m().limit().get_cancel_msg());
}

/**
   \brief Return true if all bits are true or false, and store the number represent by 
   these bits in r.
*/
template<typename Cfg>
bool bit_blaster_tpl<Cfg>::is_numeral(unsigned sz, expr * const * bits, numeral & r) const {
    r.reset();
    for (unsigned i = 0; i < sz; i++) {
        if (m().is_true(bits[i]))
            r += power(i);
        else if (!m().is_false(bits[i]))
            return false;
    }
    return true;
}

// hack to avoid GCC compilation error.
static void _num2bits(ast_manager & m, rational const & v, unsigned sz, expr_ref_vector & out_bits) {
    SASSERT(v.is_nonneg());
    rational aux = v;
    rational two(2), base32(1ull << 32ull, rational::ui64());
    for (unsigned i = 0; i < sz; i++) {
        if (i + 32 < sz) {
            unsigned u = (aux % base32).get_unsigned();
            for (unsigned j = 0; j < 32; ++j) {
                if (0 != (u & (1 << j))) {
                    out_bits.push_back(m.mk_true());
                }
                else {
                    out_bits.push_back(m.mk_false());
                }
            }
            aux = div(aux, base32);
            i += 31;
            continue;
        }
        else if ((aux % two).is_zero())
            out_bits.push_back(m.mk_false());
        else
            out_bits.push_back(m.mk_true());
        aux = div(aux, two);
    }
}


template<typename Cfg>
void bit_blaster_tpl<Cfg>::num2bits(numeral const & v, unsigned sz, expr_ref_vector & out_bits) const {
    _num2bits(m(), v, sz, out_bits);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_half_adder(expr * a, expr * b, expr_ref & out, expr_ref & cout) {
    mk_xor(a, b, out);
    mk_and(a, b, cout); 
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_full_adder(expr * a, expr * b, expr * cin, expr_ref & out, expr_ref & cout) {
    mk_xor3(a, b, cin, out);
    mk_carry(a, b, cin, cout);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_neg(unsigned sz, expr * const * a_bits, expr_ref_vector & out_bits) {
    SASSERT(sz > 0);
    expr_ref cin(m()), cout(m()), out(m());
    cin = m().mk_true();
    for (unsigned idx = 0; idx < sz; idx++) {
        expr_ref not_a(m());
        mk_not(a_bits[idx], not_a);
        if (idx < sz - 1) 
            mk_half_adder(not_a, cin, out, cout);
        else
            mk_xor(not_a, cin, out);
        out_bits.push_back(out);
        cin = cout;
    }
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_adder(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    SASSERT(sz > 0);
    expr_ref cin(m()), cout(m()), out(m());
    cin = m().mk_false();
    for (unsigned idx = 0; idx < sz; idx++) {
        if (idx < sz - 1)
            mk_full_adder(a_bits[idx], b_bits[idx], cin, out, cout);
        else
            mk_xor3(a_bits[idx], b_bits[idx], cin, out);
        out_bits.push_back(out);
        cin = cout;
    }

#if 0
    static unsigned counter = 0;
    counter++;
    verbose_stream() << "MK_ADDER: " << counter << std::endl;
#endif
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_subtracter(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits, expr_ref & cout) {
    SASSERT(sz > 0);
    expr_ref cin(m()), out(m());
    cin = m().mk_true();
    for (unsigned j = 0; j < sz; j++) {
        expr_ref not_b(m());
        mk_not(b_bits[j], not_b);
        mk_full_adder(a_bits[j], not_b, cin, out, cout);
        out_bits.push_back(out);
        cin = cout;
    }
#if 0
    for (unsigned j = 0; j < sz; ++j) {
        std::cout << j << "\n";
        std::cout << mk_pp(a_bits[j], m()) << "\n";
        std::cout << mk_pp(b_bits[j], m()) << "\n";
        std::cout << mk_pp(out_bits.get(j), m()) << "\n";
    }
#endif
    SASSERT(out_bits.size() == sz);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_multiplier(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    out_bits.reset();

    // TODO: share the bool_rewriter with the rest of the bit-blaster
    bool_rewriter rewriter(m());
    rewriter.set_flat(false);

    // First split a * b into constant and variable parts such that:
    // a * b = (Ca + Va) * (Cb + Vb)
    // TODO: allow callers to pass adders instead of just bits
    bit_blaster_adder a(rewriter, sz, a_bits);
    bit_blaster_adder b(rewriter, sz, b_bits);

    numeral a_const, b_const;
    expr_ref_vector a_var(m()), b_var(m());
    a.constant_bits(a_const);
    b.constant_bits(b_const);
    a.variable_bits(a_var);
    b.variable_bits(b_var);

    // Then this multiplication can be split into four terms:
    // a * b = Ca * Cb + Ca * Vb + Va * Cb + Va * Vb
    // and of these,
    // - Ca * Cb can be precomputed;
    // - the two C*V terms might add fewer bits in non-adjacent form;
    // - and Va * Vb must be done naively.
    // Non-adjacent form subsumes special cases, like -1, that have multiple
    // ones next to each other.

    // Finally, do all the sums at once with a tree adder.
    bit_blaster_adder total(rewriter, sz, a_const * b_const);
    mk_const_multiplier(a_const, b_var, total);
    mk_const_multiplier(b_const, a_var, total);

    expr_ref tmp(m());
    for (unsigned i = 0; i < sz; i++) {
        expr * bit_a = a_var.get(i);
        if (m().is_false(bit_a))
            continue;

        checkpoint();
        bool b_zero = true;
        for (unsigned j = 0; i + j < sz; j++) {
            expr * bit_b = b_var.get(j);
            if (m().is_false(bit_b))
                continue;
            b_zero = false;

            mk_and(bit_a, bit_b, tmp);
            total.add_bit(i + j, tmp);
        }

        // Once we see a prefix of b_var that's all 0, later prefixes will be
        // shorter and therefore also all 0.
        if (b_zero)
            break;
    }

    // TODO: return total so further linear operations can constant-fold more
    total.total_bits(out_bits);

#if 0
    static unsigned counter = 0;
    counter++;
    verbose_stream() << "MK_MULTIPLIER: " << counter << std::endl;
#endif
}


template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_umul_no_overflow(unsigned sz, expr * const * a_bits,  expr * const * b_bits, expr_ref & result) {
    SASSERT(sz > 0);
    expr_ref zero(m());
    zero = m().mk_false();
    ptr_buffer<expr,128> ext_a_bits;
    ptr_buffer<expr,128> ext_b_bits;
    ext_a_bits.append(sz, a_bits);
    ext_b_bits.append(sz, b_bits);
    ext_a_bits.push_back(zero);
    ext_b_bits.push_back(zero);
    SASSERT(ext_a_bits.size() == 1 + sz);
    SASSERT(ext_b_bits.size() == 1 + sz);
    expr_ref_vector mult_cout(m());
    //
    // mk_multiplier will simplify output taking into account that 
    // the most significant bits of ext_a_bits and ext_b_bits are zero.
    //
    mk_multiplier(1 + sz, ext_a_bits.data(), ext_b_bits.data(), mult_cout);
    expr_ref overflow1(m()), overflow2(m()), overflow(m());
    //
    // ignore bits [0, sz-1] of mult_cout
    //
    overflow1 = mult_cout[sz].get();

    expr_ref ovf(m()), v(m()), tmp(m());
    ovf = m().mk_false();
    v = m().mk_false();
    for (unsigned i = 1; i < sz; ++i) {
        mk_or(ovf, a_bits[sz-i], ovf);
        mk_and(ovf, b_bits[i], tmp);
        mk_or(tmp, v, v);
    }
    
    overflow2 = v;
    mk_or(overflow1, overflow2, overflow);
    mk_not(overflow, result);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_smul_no_overflow_core(unsigned sz, expr * const * a_bits,  expr * const * b_bits, bool is_overflow, expr_ref & result) {
    SASSERT(sz > 0);
    expr_ref zero(m());
    zero = m().mk_false();
    ptr_buffer<expr,128> ext_a_bits;
    ptr_buffer<expr,128> ext_b_bits;
    ext_a_bits.append(sz, a_bits);
    ext_b_bits.append(sz, b_bits);
    ext_a_bits.push_back(a_bits[sz-1]);
    ext_b_bits.push_back(b_bits[sz-1]);
    SASSERT(ext_a_bits.size() == 1 + sz);
    SASSERT(ext_b_bits.size() == 1 + sz);
    expr_ref_vector mult_cout(m());
    mk_multiplier(1 + sz, ext_a_bits.data(), ext_b_bits.data(), mult_cout);
    expr_ref overflow1(m()), overflow2(m()), overflow(m());

    //
    // The two most significant bits are different.
    // 
    mk_xor(mult_cout[sz].get(), mult_cout[sz-1].get(), overflow1);

    //
    // let 
    //     a_i = a[sz-1] xor a[i]
    //     b_i = b[sz-1] xor b[i]
    //     a_acc_i = a_{sz-2} or ... or a_{sz-1-i}
    //     b       = (a_acc_1 and b_1) or (a_acc_2 and b_2) or ... or (a_acc_{n-2} and b_{n-2})
    // 
    expr_ref v(m()), tmp(m()), a(m()), b(m()), a_acc(m()), sign(m());
    a_acc = m().mk_false();
    v = m().mk_false();
    for (unsigned i = 1; i + 1 < sz; ++i) {
        mk_xor(b_bits[sz-1], b_bits[i], b);
        mk_xor(a_bits[sz-1], a_bits[sz-1-i], a);
        mk_or(a, a_acc, a_acc);
        mk_and(a_acc, b, tmp);
        mk_or(tmp, v, v);
    }

    overflow2 = v;
    mk_or(overflow1, overflow2, overflow);

    if (is_overflow) {        
        // check for proper overflow
        // can only happen when the sign bits are the same.
        mk_iff(a_bits[sz-1], b_bits[sz-1], sign);
    }
    else {
        // check for proper underflow
        // can only happen when the sign bits are different.
        mk_xor(a_bits[sz-1], b_bits[sz-1], sign);
    }
    mk_and(sign, overflow, overflow);    
    mk_not(overflow, result);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_smul_no_overflow(unsigned sz, expr * const * a_bits,  expr * const * b_bits, expr_ref & result) {
    mk_smul_no_overflow_core(sz, a_bits, b_bits, true, result);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_smul_no_underflow(unsigned sz, expr * const * a_bits,  expr * const * b_bits, expr_ref & result) {
    mk_smul_no_overflow_core(sz, a_bits, b_bits, false, result);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_udiv_urem(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & q_bits, expr_ref_vector & r_bits) {
    SASSERT(sz > 0);

    // p is the residual of each stage of the division.
    expr_ref_vector & p = r_bits;

    // t is an auxiliary vector used to store the result of a subtraction
    expr_ref_vector t(m());

    // init p
    p.push_back(a_bits[sz-1]);
    for (unsigned i = 1; i < sz; i++)
        p.push_back(m().mk_false());

    q_bits.resize(sz);

    for (unsigned i = 0; i < sz; i++) {
        checkpoint();
        // generate p - b
        expr_ref q(m());
        t.reset();
        mk_subtracter(sz, p.data(), b_bits, t, q);
        q_bits.set(sz - i - 1, q);

        // update p
        if (i < sz - 1) {
            for (unsigned j = sz - 1; j > 0; j--) {
                expr_ref ie(m());
                mk_ite(q, t.get(j-1), p.get(j-1), ie); 
                p.set(j, ie);
            }
            p.set(0, a_bits[sz - i - 2]);
        }
        else {
            // last step: p contains the remainder
            for (unsigned j = 0; j < sz; j++) {
                expr_ref ie(m());
                mk_ite(q, t.get(j), p.get(j), ie);
                p.set(j, ie);
            }
        }
    }
    DEBUG_CODE({
        for (unsigned i = 0; i < sz; i++) {
            SASSERT(q_bits.get(i) != 0);
        }});
    TRACE("bit_blaster",
          tout << "a: ";
          for (unsigned i = 0; i < sz; ++i) tout << mk_pp(a_bits[i], m()) << " ";              
          tout << "\nb: ";
          for (unsigned i = 0; i < sz; ++i) tout << mk_pp(b_bits[i], m()) << " ";              
          tout << "\nq: ";
          for (unsigned i = 0; i < sz; ++i) tout << mk_pp(q_bits[i].get(), m()) << " ";              
          tout << "\nr: ";
          for (unsigned i = 0; i < sz; ++i) tout << mk_pp(r_bits[i].get(), m()) << " ";              
          tout << "\n";
          );
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_udiv(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & q_bits) {
    expr_ref_vector aux(m());
    mk_udiv_urem(sz, a_bits, b_bits, q_bits, aux);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_urem(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & r_bits) {
    expr_ref_vector aux(m());
    mk_udiv_urem(sz, a_bits, b_bits, aux, r_bits);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_multiplexer(expr * c, unsigned sz, expr * const * t_bits, expr * const * e_bits, expr_ref_vector & out_bits) {
    for (unsigned i = 0; i < sz; i++) {
        expr_ref t(m());
        mk_ite(c, t_bits[i], e_bits[i], t);
        out_bits.push_back(t);
    }
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_abs(unsigned sz, expr * const * a_bits, expr_ref_vector & out_bits) {
    expr * a_msb   = a_bits[sz - 1];
    if (m().is_false(a_msb)) {
        out_bits.append(sz, a_bits);
    }
    else if (m().is_true(a_msb)) {
        mk_neg(sz, a_bits, out_bits);
    }
    else {
        expr_ref_vector neg_a_bits(m());
        mk_neg(sz, a_bits, neg_a_bits);
        mk_multiplexer(a_msb, sz, neg_a_bits.data(), a_bits, out_bits);
    }
}

#define SDIV 0
#define SREM 1
#define SMOD 2

template<typename Cfg>
template<unsigned k>
void bit_blaster_tpl<Cfg>::mk_sdiv_srem_smod(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    // This definition is only good when the most significant bits are set.
    // Otherwise, it will create 4 copies of the expensive sdiv/srem/smod
    SASSERT(k == SDIV || k == SREM || k == SMOD);

    expr * a_msb   = a_bits[sz - 1];
    expr * b_msb   = b_bits[sz - 1];

    expr_ref_vector neg_a_bits(m());
    expr_ref_vector neg_b_bits(m());

    mk_neg(sz, a_bits, neg_a_bits);
    mk_neg(sz, b_bits, neg_b_bits);

    expr_ref_vector pp_q(m()), pp_r(m()), pn_q(m()), pn_r(m()), np_q(m()), np_r(m()), nn_q(m()), nn_r(m());

    if (!m().is_true(a_msb) && !m().is_true(b_msb)) {
        mk_udiv_urem(sz, a_bits, b_bits, pp_q, pp_r);
    }
    else {
        pp_q.resize(sz, m().mk_false());
        pp_r.resize(sz, m().mk_false());
    }
    
    if (!m().is_false(a_msb) && !m().is_true(b_msb)) {
        mk_udiv_urem(sz, neg_a_bits.data(), b_bits, np_q, np_r);
    }
    else {
        np_q.resize(sz, m().mk_false());
        np_r.resize(sz, m().mk_false());
    }

    if (!m().is_true(a_msb) && !m().is_false(b_msb)) {
        mk_udiv_urem(sz, a_bits, neg_b_bits.data(), pn_q, pn_r);
    }
    else {
        pn_q.resize(sz, m().mk_false());
        pn_r.resize(sz, m().mk_false());
    }

    if (!m().is_false(a_msb) && !m().is_false(b_msb)) {
        mk_udiv_urem(sz, neg_a_bits.data(), neg_b_bits.data(), nn_q, nn_r);
    }
    else {
        nn_q.resize(sz, m().mk_false());
        nn_r.resize(sz, m().mk_false());
    }

    expr_ref_vector ite1(m()), ite2(m());
    if (k == SDIV) {
        expr_ref_vector & pp_out = pp_q;
        expr_ref_vector   np_out(m());
        expr_ref_vector   pn_out(m());
        expr_ref_vector & nn_out = nn_q;

        if (!m().is_false(a_msb) && !m().is_true(b_msb))
            mk_neg(sz, np_q.data(), np_out);
        else
            np_out.resize(sz, m().mk_false());

        if (!m().is_true(a_msb) && !m().is_false(b_msb)) 
            mk_neg(sz, pn_q.data(), pn_out);
        else
            pn_out.resize(sz, m().mk_false());
        
#define MK_MULTIPLEXER()                                                        \
        mk_multiplexer(b_msb, sz, nn_out.data(), np_out.data(), ite1);        \
        mk_multiplexer(b_msb, sz, pn_out.data(), pp_out.data(), ite2);        \
        mk_multiplexer(a_msb, sz, ite1.data(),   ite2.data(),   out_bits)

        MK_MULTIPLEXER();
    }
    else if (k == SREM) {
        expr_ref_vector & pp_out = pp_r;
        expr_ref_vector   np_out(m());
        expr_ref_vector & pn_out = pn_r;
        expr_ref_vector   nn_out(m());

        if (!m().is_false(a_msb) && !m().is_true(b_msb)) 
            mk_neg(sz, np_r.data(), np_out);
        else
            np_out.resize(sz, m().mk_false());

        if (!m().is_false(a_msb) && !m().is_false(b_msb)) 
            mk_neg(sz, nn_r.data(), nn_out);
        else
            nn_out.resize(sz, m().mk_false());
        MK_MULTIPLEXER();
    }
    else {
        SASSERT(k == SMOD);
        expr_ref_vector & pp_out = pp_r; 
        expr_ref_vector   np_out(m());
        expr_ref_vector   pn_out(m());
        expr_ref_vector   nn_out(m());

        if (!m().is_false(a_msb) && !m().is_true(b_msb)) {
            expr_ref cout(m());
            mk_subtracter(sz, b_bits, np_r.data(), np_out, cout);
        }
        else
            np_out.resize(sz, m().mk_false());

        if (!m().is_true(a_msb) && !m().is_false(b_msb)) 
            mk_adder(sz, b_bits, pn_r.data(), pn_out);
        else
            pn_out.resize(sz, m().mk_false());

        if (!m().is_false(a_msb) && !m().is_false(b_msb)) 
            mk_neg(sz, nn_r.data(), nn_out);
        else
            nn_out.resize(sz, m().mk_false());

        MK_MULTIPLEXER();
    }
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_sdiv(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    expr * a_msb = a_bits[sz - 1];
    expr * b_msb = b_bits[sz - 1];
    if (m().is_false(a_msb) && m().is_false(b_msb)) {
        mk_udiv(sz, a_bits, b_bits, out_bits);
    }
    else if (m().is_false(a_msb) && m().is_true(b_msb)) {
        expr_ref_vector neg_b_bits(m());
        mk_neg(sz, b_bits, neg_b_bits);
        expr_ref_vector tmp(m());
        mk_udiv(sz, a_bits, neg_b_bits.data(), tmp);
        mk_neg(sz, tmp.data(), out_bits);
    }
    else if (m().is_true(a_msb) && m().is_false(b_msb)) {
        expr_ref_vector neg_a_bits(m());
        mk_neg(sz, a_bits, neg_a_bits);
        expr_ref_vector tmp(m());
        mk_udiv(sz, neg_a_bits.data(), b_bits, tmp);
        mk_neg(sz, tmp.data(), out_bits);
    }
    else if (m().is_true(a_msb) && m().is_true(b_msb)) {
        expr_ref_vector neg_a_bits(m());
        mk_neg(sz, a_bits, neg_a_bits);
        expr_ref_vector neg_b_bits(m());
        mk_neg(sz, b_bits, neg_b_bits);
        mk_udiv(sz, neg_a_bits.data(), neg_b_bits.data(), out_bits);
    }
    else {
#if 0
        // creates 4 dividers
        mk_sdiv_srem_smod<SDIV>(sz, a_bits, b_bits, out_bits);
#else
        // creates only 1
        expr_ref_vector abs_a_bits(m());
        expr_ref_vector abs_b_bits(m());
        mk_abs(sz, a_bits, abs_a_bits);
        mk_abs(sz, b_bits, abs_b_bits);
        expr_ref_vector udiv_bits(m());
        mk_udiv(sz, abs_a_bits.data(), abs_b_bits.data(), udiv_bits);
        expr_ref_vector neg_udiv_bits(m());
        mk_neg(sz, udiv_bits.data(), neg_udiv_bits);
        expr_ref c(m());
        mk_iff(a_msb, b_msb, c);
        mk_multiplexer(c, sz, udiv_bits.data(), neg_udiv_bits.data(), out_bits);
#endif
    }
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_srem(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    expr * a_msb = a_bits[sz - 1];
    expr * b_msb = b_bits[sz - 1];
    if (m().is_false(a_msb) && m().is_false(b_msb)) {
        mk_urem(sz, a_bits, b_bits, out_bits);
    }
    else if (m().is_false(a_msb) && m().is_true(b_msb)) {
        expr_ref_vector neg_b_bits(m());
        mk_neg(sz, b_bits, neg_b_bits);
        mk_urem(sz, a_bits, neg_b_bits.data(), out_bits);
    }
    else if (m().is_true(a_msb) && m().is_false(b_msb)) {
        expr_ref_vector neg_a_bits(m());
        mk_neg(sz, a_bits, neg_a_bits);
        expr_ref_vector tmp(m());
        mk_urem(sz, neg_a_bits.data(), b_bits, tmp);
        mk_neg(sz, tmp.data(), out_bits);
    }
    else if (m().is_true(a_msb) && m().is_true(b_msb)) {
        expr_ref_vector neg_a_bits(m());
        mk_neg(sz, a_bits, neg_a_bits);
        expr_ref_vector neg_b_bits(m());
        mk_neg(sz, b_bits, neg_b_bits);
        expr_ref_vector tmp(m());
        mk_urem(sz, neg_a_bits.data(), neg_b_bits.data(), tmp);
        mk_neg(sz, tmp.data(), out_bits);
    }
    else {
#if 0
        // creates 4 urem
        mk_sdiv_srem_smod<SREM>(sz, a_bits, b_bits, out_bits);
#else
        // creates only 1
        expr_ref_vector abs_a_bits(m());
        expr_ref_vector abs_b_bits(m());
        mk_abs(sz, a_bits, abs_a_bits);
        mk_abs(sz, b_bits, abs_b_bits);
        expr_ref_vector urem_bits(m());
        numeral n_b;
        unsigned shift;
        // a urem 2^n -> a & ((2^n)-1)
        if (is_numeral(sz, abs_b_bits.data(), n_b) && n_b.is_power_of_two(shift)) {
            mk_zero_extend(shift, abs_a_bits.data(), sz - shift, urem_bits);
        } else {
            mk_urem(sz, abs_a_bits.data(), abs_b_bits.data(), urem_bits);
        }
        expr_ref_vector neg_urem_bits(m());
        mk_neg(sz, urem_bits.data(), neg_urem_bits);
        mk_multiplexer(a_msb, sz, neg_urem_bits.data(), urem_bits.data(), out_bits);
#endif
    }
}

/**
   \brief Generate circuit for signed mod.

   This function implements the semantics of bvsmod given below for two bits:

   (define-fun bvsmod_def ((s (_ BitVec 2)) (t (_ BitVec 2))) (_ BitVec 2)
      (let ((msb_s ((_ extract 1 1) s))
            (msb_t ((_ extract 1 1) t)))
        (let ((abs_s (ite (= msb_s #b0) s (bvneg s)))
              (abs_t (ite (= msb_t #b0) t (bvneg t))))
          (let ((u (bvurem abs_s abs_t)))
            (ite (= u (_ bv0 2))
                 u
            (ite (and (= msb_s #b0) (= msb_t #b0))
                 u
            (ite (and (= msb_s #b1) (= msb_t #b0))
                 (bvadd (bvneg u) t)
            (ite (and (= msb_s #b0) (= msb_t #b1))
                 (bvadd u t)
                 (bvneg u)))))))))

  Note: The semantics is sensitive to the order of these tests.
  It is unsound to test first for whether the most significant
  bits of s and t are known and use the cases for those. If
  u is 0 then the result is 0.
*/

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_smod(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    expr * a_msb = a_bits[sz - 1];
    expr * b_msb = b_bits[sz - 1];

    expr_ref_vector abs_a_bits(m());
    expr_ref_vector abs_b_bits(m());
    mk_abs(sz, a_bits, abs_a_bits);
    mk_abs(sz, b_bits, abs_b_bits);
    expr_ref_vector u_bits(m());
    mk_urem(sz, abs_a_bits.data(), abs_b_bits.data(), u_bits);        
    expr_ref_vector neg_u_bits(m());
    mk_neg(sz, u_bits.data(), neg_u_bits);
    expr_ref_vector neg_u_add_b(m());
    mk_adder(sz, neg_u_bits.data(), b_bits, neg_u_add_b);
    expr_ref_vector u_add_b(m());
    mk_adder(sz, u_bits.data(), b_bits, u_add_b);
    expr_ref_vector zero(m());
    num2bits(numeral(0), sz, zero);
    expr_ref u_eq_0(m());
    mk_eq(sz, u_bits.data(), zero.data(), u_eq_0);
    
    expr_ref_vector & pp_bits = u_bits;      // pos & pos case
    expr_ref_vector & pn_bits = u_add_b;     // pos & neg case
    expr_ref_vector & np_bits = neg_u_add_b; // neg & pos case
    expr_ref_vector & nn_bits = neg_u_bits;  // neg & neg case
    
    expr_ref_vector ite1(m());
    expr_ref_vector ite2(m());
    expr_ref_vector body(m());
    mk_multiplexer(b_msb, sz, nn_bits.data(), np_bits.data(), ite1);
    mk_multiplexer(b_msb, sz, pn_bits.data(), pp_bits.data(), ite2);
    mk_multiplexer(a_msb, sz, ite1.data(), ite2.data(), body);
    mk_multiplexer(u_eq_0, sz, u_bits.data(), body.data(), out_bits);
    
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_eq(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref & out) {
    expr_ref_vector out_bits(m());
    for (unsigned i = 0; i < sz; i++) {
        mk_iff(a_bits[i], b_bits[i], out);
        out_bits.push_back(out);
    }
    mk_and(out_bits.size(), out_bits.data(), out);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_rotate_left(unsigned sz, expr * const * a_bits, unsigned n, expr_ref_vector & out_bits) {
    TRACE("bit_blaster", tout << n << ": " << sz << " ";
          for (unsigned i = 0; i < sz; ++i) {
              tout << mk_pp(a_bits[i], m()) << " ";
          }
          tout << "\n";
          );
    n = n % sz;
    for (unsigned i = sz - n; i < sz; i++) 
        out_bits.push_back(a_bits[i]);
    for (unsigned i = 0 ; i < sz - n; i++) 
        out_bits.push_back(a_bits[i]);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_rotate_right(unsigned sz, expr * const * a_bits, unsigned n, expr_ref_vector & out_bits) {
    n = n % sz;
    mk_rotate_left(sz, a_bits, sz - n, out_bits);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_sign_extend(unsigned sz, expr * const * a_bits, unsigned n, expr_ref_vector & out_bits) {
    for (unsigned i = 0; i < sz; i++) 
        out_bits.push_back(a_bits[i]);
    expr * high_bit = a_bits[sz - 1];
    for (unsigned i = sz; i < sz + n; i++)
        out_bits.push_back(high_bit);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_zero_extend(unsigned sz, expr * const * a_bits, unsigned n, expr_ref_vector & out_bits) {
    for (unsigned i = 0; i < sz; i++) 
        out_bits.push_back(a_bits[i]);
    expr * high_bit = m().mk_false();
    for (unsigned i = sz; i < sz + n; i++)
        out_bits.push_back(high_bit);
}

/**
   \brief Return an expression that is true iff a_bits represents the number n.
*/
template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_is_eq(unsigned sz, expr * const * a_bits, unsigned n, expr_ref & out) {
    numeral two(2);
    expr_ref_vector out_bits(m());
    for (unsigned i = 0; i < sz; i++) {
        if (n % 2 == 0) {
            expr_ref not_a(m());
            mk_not(a_bits[i], not_a);
            out_bits.push_back(not_a);
        }
        else {
            out_bits.push_back(a_bits[i]);
        }
        n = n / 2;
    }
    mk_and(out_bits.size(), out_bits.data(), out);
}

/**
   \brief Store in eqs the equalities a_bits = 0, a_bits = 1, ..., a_bits = sz -1. 
*/
template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_eqs(unsigned sz, expr * const * a_bits, expr_ref_vector & eqs) {
    for (unsigned i = 0; i < sz; i++) {
        expr_ref eq(m());
        mk_is_eq(sz, a_bits, i, eq);
        eqs.push_back(eq);
    }
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_shl(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    numeral k;
    if (is_numeral(sz, b_bits, k)) {
        if (k > numeral(sz)) k = numeral(sz);
        unsigned n = static_cast<unsigned>(k.get_int64());
        if (n >= sz) n = sz;
        unsigned pos; 
        for (pos = 0; pos < n; pos++)
            out_bits.push_back(m().mk_false());
        for (unsigned i = 0; pos < sz; pos++, i++)
            out_bits.push_back(a_bits[i]);
    }
    else {
        out_bits.append(sz, a_bits);
        
        unsigned i = 0;
        expr_ref_vector new_out_bits(m());
        for (; i < sz; ++i) {
            checkpoint();
            unsigned shift_i = 1 << i;
            if (shift_i >= sz) break;
            for (unsigned j = 0; j < sz; ++j) {
                expr_ref new_out(m());
                expr* a_j = m().mk_false();
                if (shift_i <= j) a_j = out_bits[j-shift_i].get();
                mk_ite(b_bits[i], a_j, out_bits[j].get(), new_out);
                new_out_bits.push_back(new_out);
            }
            out_bits.reset();
            out_bits.append(new_out_bits);
            new_out_bits.reset();
        }        
        expr_ref is_large(m());
        is_large = m().mk_false();
        for (; i < sz; ++i) {
            mk_or(is_large, b_bits[i], is_large);
        }
        for (unsigned j = 0; j < sz; ++j) {
            expr_ref new_out(m());
            mk_ite(is_large, m().mk_false(), out_bits[j].get(), new_out);
            out_bits[j] = new_out;
        }
    }
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_lshr(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    numeral k;
    if (is_numeral(sz, b_bits, k)) {
        if (k > numeral(sz)) k = numeral(sz);
        unsigned n   = static_cast<unsigned>(k.get_int64()); 
        unsigned pos = 0;
        for (unsigned i = n; i < sz; pos++, i++)
            out_bits.push_back(a_bits[i]);
        for (; pos < sz; pos++)
            out_bits.push_back(m().mk_false());
    }
    else {
        out_bits.append(sz, a_bits);        
        unsigned i = 0;
        for (; i < sz; ++i) {
            checkpoint();
            expr_ref_vector new_out_bits(m());
            unsigned shift_i = 1 << i;
            if (shift_i >= sz) break;
            for (unsigned j = 0; j < sz; ++j) {
                expr_ref new_out(m());
                expr* a_j = m().mk_false();
                if (shift_i + j < sz) a_j = out_bits[j+shift_i].get();
                mk_ite(b_bits[i], a_j, out_bits[j].get(), new_out);
                new_out_bits.push_back(new_out);
            }
            out_bits.reset();
            out_bits.append(new_out_bits);
        }
        expr_ref is_large(m());
        is_large = m().mk_false();
        for (; i < sz; ++i) {
            mk_or(is_large, b_bits[i], is_large);
        }
        for (unsigned j = 0; j < sz; ++j) {
            expr_ref new_out(m());
            mk_ite(is_large, m().mk_false(), out_bits[j].get(), new_out);
            out_bits[j] = new_out;
        }
    }
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_ashr(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    numeral k;
    if (is_numeral(sz, b_bits, k)) {
        if (k > numeral(sz)) k = numeral(sz);
        unsigned n   = static_cast<unsigned>(k.get_int64()); 
        unsigned pos = 0;
        for (unsigned i = n; i < sz; pos++, i++)
            out_bits.push_back(a_bits[i]);
        for (; pos < sz; pos++)
            out_bits.push_back(a_bits[sz-1]);
    }
    else {
        out_bits.append(sz, a_bits);        
        unsigned i = 0;
        for (; i < sz; ++i) {
            checkpoint();
            expr_ref_vector new_out_bits(m());
            unsigned shift_i = 1 << i;
            if (shift_i >= sz) break;
            for (unsigned j = 0; j < sz; ++j) {
                expr_ref new_out(m());
                expr* a_j = a_bits[sz-1];
                if (shift_i + j < sz) a_j = out_bits[j+shift_i].get();
                mk_ite(b_bits[i], a_j, out_bits[j].get(), new_out);
                new_out_bits.push_back(new_out);
            }
            out_bits.reset();
            out_bits.append(new_out_bits);
        }
        expr_ref is_large(m());
        is_large = m().mk_false();
        for (; i < sz; ++i) {
            mk_or(is_large, b_bits[i], is_large);
        }
        for (unsigned j = 0; j < sz; ++j) {
            expr_ref new_out(m());
            mk_ite(is_large, a_bits[sz-1], out_bits[j].get(), new_out);
            out_bits[j] = new_out;
        }
    }
}

template<typename Cfg>
template<bool Left>
void bit_blaster_tpl<Cfg>::mk_ext_rotate_left_right(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    numeral k;
    if (is_numeral(sz, b_bits, k) && k.is_unsigned()) {
        if (Left)
            mk_rotate_left(sz, a_bits, static_cast<unsigned>(k.get_uint64()), out_bits);
        else
            mk_rotate_right(sz, a_bits, static_cast<unsigned>(k.get_uint64()), out_bits);
    }
    else {
        //
        // Review: a better tuned implementation is possible by using shifts by power of two.
        // e.g., looping over the bits of b_bits, then rotate by a power of two depending
        // on the bit-position. This would get rid of the mk_urem.
        //
        expr_ref_vector sz_bits(m());
        expr_ref_vector masked_b_bits(m());
        expr_ref_vector eqs(m());
        numeral sz_numeral(sz);
        num2bits(sz_numeral, sz, sz_bits);
        mk_urem(sz, b_bits, sz_bits.data(), masked_b_bits);
        mk_eqs(sz, masked_b_bits.data(), eqs);
        for (unsigned i = 0; i < sz; i++) {
            checkpoint();
            expr_ref out(m());
            out = a_bits[i];
            for (unsigned j = 1; j < sz; j++) {
                expr_ref new_out(m());
                unsigned src = (Left ? (sz + i - j) : (i + j)) % sz;
                mk_ite(eqs.get(j), a_bits[src], out, new_out);
                out = new_out;
            }
            out_bits.push_back(out);
        }
    }
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_ext_rotate_left(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    mk_ext_rotate_left_right<true>(sz, a_bits, b_bits, out_bits);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_ext_rotate_right(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    mk_ext_rotate_left_right<false>(sz, a_bits, b_bits, out_bits);
}

template<typename Cfg>
template<bool Signed>
void bit_blaster_tpl<Cfg>::mk_le(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref & out) {
    SASSERT(sz > 0);
    expr_ref not_a(m());
    mk_not(a_bits[0], not_a);
    mk_or(not_a, b_bits[0], out);
    for (unsigned idx = 1; idx < (Signed ? sz - 1 : sz); idx++) {
        mk_not(a_bits[idx], not_a);
        mk_ge2(not_a, b_bits[idx], out, out);
    }
    if (Signed) {
        expr_ref not_b(m());
        mk_not(b_bits[sz-1], not_b);
        mk_ge2(not_b, a_bits[sz-1], out, out);
    }
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_sle(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref & out) {
    mk_le<true>(sz, a_bits, b_bits, out);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_ule(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref & out) {
    mk_le<false>(sz, a_bits, b_bits, out);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_not(unsigned sz, expr * const * a_bits, expr_ref_vector & out_bits) {
    for (unsigned i = 0; i < sz; i++) {
        expr_ref t(m());
        mk_not(a_bits[i], t);
        out_bits.push_back(t);
    }
}

#define MK_BINARY(NAME, OP)                                                                                                     \
template<typename Cfg>                                                                                                          \
void bit_blaster_tpl<Cfg>::NAME(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {        \
    for (unsigned i = 0; i < sz; i++) {                                                                                         \
        expr_ref t(m());                                                                                                        \
        OP(a_bits[i], b_bits[i], t);                                                                                            \
        out_bits.push_back(t);                                                                                                  \
    }                                                                                                                           \
}

MK_BINARY(mk_and, mk_and);
MK_BINARY(mk_or, mk_or);
MK_BINARY(mk_xor, mk_xor);
MK_BINARY(mk_xnor, mk_iff);
MK_BINARY(mk_nand, mk_nand);
MK_BINARY(mk_nor, mk_nor);

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_redand(unsigned sz, expr * const * a_bits, expr_ref_vector & out_bits) {
    expr_ref tmp(m());
    mk_and(sz, a_bits, tmp);
    out_bits.push_back(tmp);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_redor(unsigned sz, expr * const * a_bits, expr_ref_vector & out_bits) {
    expr_ref tmp(m());
    mk_or(sz, a_bits, tmp);
    out_bits.push_back(tmp);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_comp(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits) {
    expr_ref tmp(m());
    mk_eq(sz, a_bits, b_bits, tmp);
    out_bits.push_back(tmp);
}

template<typename Cfg>
void bit_blaster_tpl<Cfg>::mk_const_multiplier(numeral & a, expr_ref_vector & b_bits, bit_blaster_adder & result) {
    // If either a or b are definitely 0, then there's nothing to do here.
    if (a.is_zero())
        return;

    unsigned i;
    for (i = 0; i < b_bits.size(); i++)
        if (!m().is_false(b_bits.get(i)))
            break;
    if (i == b_bits.size())
        return;

    // We're multiplying two non-zero numbers. Convert the constant operand (a)
    // into non-adjacent form, which may reduce the number of non-zero bits,
    // which in turn reduces the number of terms we have to add together.
    // Unlike Booth encoding, this form can never increase the number of
    // non-zero bits.
    // https://en.m.wikipedia.org/wiki/Non-adjacent_form
    numeral subtract = floor(a / 2);
    numeral nonzero = bitwise_xor(subtract, a + subtract);

    // Decompose twos-complement negation into bitwise-not followed by deferred
    // addition of the constant 1. That combines adding the constants with all
    // the other addition the multiplier is doing, rather than sticking an
    // extra ripple-carry adder in front.
    expr_ref_vector not_b_bits(m());
    mk_not(b_bits.size(), b_bits.data(), not_b_bits);

    for (unsigned i = 0; i < result.size(); i++) {
        if (!nonzero.get_bit(i))
            continue;

        if (subtract.get_bit(i)) {
            result.add_shifted(not_b_bits, i);
            result.add_bit(i, true);
        } else {
            result.add_shifted(b_bits, i);
        }
    }
}
