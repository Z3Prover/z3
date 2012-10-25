/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bit_blaster_tpl.h

Abstract:

    Template for bit-blaster operations

Author:

    Leonardo de Moura (leonardo) 2011-05-02.

Revision History:

--*/
#ifndef _BIT_BLASTER_TPL_H_
#define _BIT_BLASTER_TPL_H_

#include"rational.h"

template<typename Cfg>
class bit_blaster_tpl : public Cfg {
public:
    typedef rational numeral;
protected:
    template<bool Signed>
    void mk_le(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref & out);

    template<unsigned k>
    void mk_sdiv_srem_smod(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);

    template<bool Left>
    void mk_ext_rotate_left_right(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);

    unsigned long long m_max_memory;
    volatile bool      m_cancel;
    bool               m_use_wtm; /* Wallace Tree Multiplier */
    bool               m_use_bcm; /* Booth Multiplier for constants */
    void checkpoint();

public:
    bit_blaster_tpl(Cfg const & cfg = Cfg(), unsigned long long max_memory = UINT64_MAX, bool use_wtm = false, bool use_bcm=false):
        Cfg(cfg),
        m_max_memory(max_memory),
        m_cancel(false),
        m_use_wtm(use_wtm),
        m_use_bcm(use_bcm) {
    }

    void set_max_memory(unsigned long long max_memory) {
        m_max_memory = max_memory;
    }

    void set_cancel(bool f) { m_cancel = f; }
    void cancel() { set_cancel(true); }
    void reset_cancel() { set_cancel(false); }
    
    // Cfg required API
    ast_manager & m() const { return Cfg::m(); }
    numeral power(unsigned n) const { return Cfg::power(n); }
    void mk_xor(expr * a, expr * b, expr_ref & r) { Cfg::mk_xor(a, b, r); }
    void mk_xor3(expr * a, expr * b, expr * c, expr_ref & r) { Cfg::mk_xor3(a, b, c, r); }
    void mk_carry(expr * a, expr * b, expr * c, expr_ref & r) { Cfg::mk_carry(a, b, c, r); }
    void mk_iff(expr * a, expr * b, expr_ref & r) { Cfg::mk_iff(a, b, r); }
    void mk_and(expr * a, expr * b, expr_ref & r) { Cfg::mk_and(a, b, r); }
    void mk_and(expr * a, expr * b, expr * c, expr_ref & r) { Cfg::mk_and(a, b, c, r); }
    void mk_and(unsigned sz, expr * const * args, expr_ref & r) { Cfg::mk_and(sz, args, r); }
    void mk_or(expr * a, expr * b, expr_ref & r) { Cfg::mk_or(a, b, r); }
    void mk_or(expr * a, expr * b, expr * c, expr_ref & r) { Cfg::mk_or(a, b, c, r); }
    void mk_or(unsigned sz, expr * const * args, expr_ref & r) { Cfg::mk_or(sz, args, r); }
    void mk_not(expr * a, expr_ref & r) { Cfg::mk_not(a, r); }
    void mk_ite(expr * c, expr * t, expr * e, expr_ref & r) { Cfg::mk_ite(c, t, e, r); }
    void mk_nand(expr * a, expr * b, expr_ref & r) { Cfg::mk_nand(a, b, r); }
    void mk_nor(expr * a, expr * b, expr_ref & r) { Cfg::mk_nor(a, b, r); }
    //


    bool is_numeral(unsigned sz, expr * const * bits) const;
    bool is_numeral(unsigned sz, expr * const * bits, numeral & r) const;
    bool is_minus_one(unsigned sz, expr * const * bits) const;
    void num2bits(numeral const & v, unsigned sz, expr_ref_vector & out_bits) const;
    
    void mk_half_adder(expr * a, expr * b, expr_ref & out, expr_ref & cout);
    void mk_full_adder(expr * a, expr * b, expr * cin, expr_ref & out, expr_ref & cout);
    void mk_neg(unsigned sz, expr * const * a_bits, expr_ref_vector & out_bits);
    void mk_adder(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_subtracter(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits, expr_ref & cout);
    void mk_multiplier(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_udiv_urem(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & q_bits, expr_ref_vector & r_bits);
    void mk_udiv(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & q_bits);
    void mk_urem(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & r_bits);
    void mk_multiplexer(expr * c, unsigned sz, expr * const * t_bits, expr * const * e_bits, expr_ref_vector & out_bits);
    void mk_sdiv(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_srem(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_smod(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_rotate_left(unsigned sz, expr * const * a_bits, unsigned n, expr_ref_vector & out_bits);
    void mk_rotate_right(unsigned sz, expr * const * a_bits, unsigned n, expr_ref_vector & out_bits);
    void mk_ext_rotate_left(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_ext_rotate_right(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_sign_extend(unsigned sz, expr * const * a_bits, unsigned n, expr_ref_vector & out_bits);
    void mk_zero_extend(unsigned sz, expr * const * a_bits, unsigned n, expr_ref_vector & out_bits);
    void mk_eq(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref & out);
    void mk_is_eq(unsigned sz, expr * const * a_bits, unsigned n, expr_ref & out);
    void mk_eqs(unsigned sz, expr * const * a_bits, expr_ref_vector & eqs);
    void mk_shl(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_lshr(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_ashr(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_sle(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref & out);
    void mk_ule(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref & out);
    void mk_not(unsigned sz, expr * const * a_bits, expr_ref_vector & out_bits);
    void mk_and(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_or(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_xor(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_xnor(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_nand(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_nor(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);
    void mk_redand(unsigned sz, expr * const * a_bits, expr_ref_vector & out_bits);
    void mk_redor(unsigned sz, expr * const * a_bits, expr_ref_vector & out_bits);
    void mk_umul_no_overflow(unsigned sz, expr * const * a_bits,  expr * const * b_bits, expr_ref & out);
    void mk_smul_no_overflow_core(unsigned sz, expr * const * a_bits,  expr * const * b_bits, bool is_overflow, expr_ref & result);
    void mk_smul_no_overflow(unsigned sz, expr * const * a_bits,  expr * const * b_bits, expr_ref & out);
    void mk_smul_no_underflow(unsigned sz, expr * const * a_bits,  expr * const * b_bits, expr_ref & out);
    void mk_comp(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);

    void mk_carry_save_adder(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr * const * c_bits, expr_ref_vector & sum_bits, expr_ref_vector & carry_bits);
    void mk_const_multiplier(unsigned sz, expr * const * a_bits, expr * const * b_bits, expr_ref_vector & out_bits);

    void mk_abs(unsigned sz, expr * const * a_bits, expr_ref_vector & out_bits);
};

#endif
