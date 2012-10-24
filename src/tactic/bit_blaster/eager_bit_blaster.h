/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    eager_bit_blaster.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-02.

Revision History:

--*/
#ifndef _EAGER_BIT_BLASTER_H_
#define _EAGER_BIT_BLASTER_H_

#include"bv_decl_plugin.h"
#include"bit_blaster.h"
#include"simplifier.h"
#include"basic_simplifier_plugin.h"

class eager_bit_blaster {

    class bv_plugin : public simplifier_plugin {
        bv_util                 m_util;
        bit_blaster             m_bb;
        basic_simplifier_plugin m_s;

        void get_bits(expr * n, expr_ref_vector & out_bits);
        app * mk_mkbv(expr_ref_vector const & bits);
            
        void reduce_not(expr * arg, expr_ref & result);
        void reduce_bin_or(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_or(unsigned num_args, expr * const * args, expr_ref & result);
        void reduce_bin_and(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_and(unsigned num_args, expr * const * args, expr_ref & result);
        void reduce_bin_nor(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_nor(unsigned num_args, expr * const * args, expr_ref & result);
        void reduce_bin_nand(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_nand(unsigned num_args, expr * const * args, expr_ref & result);
        void reduce_xor(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_xnor(expr * arg1, expr * arg2, expr_ref & result);

        void reduce_neg(expr * arg, expr_ref & result);
        void reduce_bin_add(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_add(unsigned num_args, expr * const * args, expr_ref & result);
        void reduce_bin_mul(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_mul(unsigned num_args, expr * const * args, expr_ref & result);
        void reduce_sdiv(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_udiv(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_srem(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_urem(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_smod(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_sle(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_ule(expr * arg1, expr * arg2, expr_ref & result);

        void reduce_concat(unsigned num_args, expr * const * args, expr_ref & result);
        void reduce_extract(unsigned start, unsigned end, expr * arg, expr_ref & result);

        void reduce_redor(expr * arg, expr_ref & result);
        void reduce_redand(expr * arg, expr_ref & result);

        void reduce_comp(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_shl(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_ashr(expr * arg1, expr * arg2, expr_ref & result);
        void reduce_lshr(expr * arg1, expr * arg2, expr_ref & result);

        void reduce_rotate_left(expr * arg, unsigned n, expr_ref & result);
        void reduce_rotate_right(expr * arg, unsigned n, expr_ref & result);
        void reduce_sign_extend(expr * arg, unsigned n, expr_ref & result);
        void reduce_zero_extend(expr * arg, unsigned n, expr_ref & result);

    public:
        bv_plugin(ast_manager & m, bit_blaster_params const & p);
        virtual ~bv_plugin();
        virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
        virtual bool reduce_eq(expr * lhs, expr * rhs, expr_ref & result);
        virtual bool reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result);
        basic_simplifier_plugin & get_basic_simplifier() { return m_s; }
        bool reduce_ite(expr * arg1, expr * arg2, expr * arg3, expr_ref & result);
    };

    /**
       \brief Plugin for handling the term-ite.
    */
    class basic_plugin : public simplifier_plugin {
        bv_plugin &               m_main;
        basic_simplifier_plugin & m_s;
    public:
        basic_plugin(ast_manager & m, bv_plugin & p, basic_simplifier_plugin & s);
        virtual ~basic_plugin();
        virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    };

    simplifier  m_simplifier;
public:
    eager_bit_blaster(ast_manager & m, bit_blaster_params const & p);
    void operator()(expr * s, expr_ref & r, proof_ref & p);
};

#endif /* _EAGER_BIT_BLASTER_H_ */

