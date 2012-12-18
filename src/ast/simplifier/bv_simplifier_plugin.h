/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    bv_simplifier_plugin.h

Abstract:

    Simplifier for the bv family.

Author:

    Leonardo (leonardo) 2008-01-08
    
--*/
#ifndef _BV_SIMPLIFIER_PLUGIN_H_
#define _BV_SIMPLIFIER_PLUGIN_H_

#include"basic_simplifier_plugin.h"
#include"poly_simplifier_plugin.h"
#include"bv_decl_plugin.h"
#include"map.h"
#include"bv_simplifier_params.h"
#include"arith_decl_plugin.h"

/**
   \brief Simplifier for the bv family.
*/
class bv_simplifier_plugin : public poly_simplifier_plugin {

    typedef rational numeral;
    struct extract_entry {
        unsigned m_high;
        unsigned m_low;
        expr *    m_arg;
        extract_entry():m_high(0), m_low(0), m_arg(0) {}
        extract_entry(unsigned h, unsigned l, expr * n):m_high(h), m_low(l), m_arg(n) {}
        unsigned hash() const {
            unsigned a = m_high;
            unsigned b = m_low;
            unsigned c = m_arg->get_id();
            mix(a,b,c);
            return c;
        }
        bool operator==(const extract_entry & e) const {
            return m_high == e.m_high && m_low == e.m_low && m_arg == e.m_arg;
        }
        struct hash_proc {
            unsigned operator()(extract_entry const& e) const { return e.hash(); }
        };
        struct eq_proc {
            bool operator()(extract_entry const& a, extract_entry const& b) const { return a == b; }
        };
    };
    typedef map<extract_entry, expr *, extract_entry::hash_proc , extract_entry::eq_proc > extract_cache;

protected:
    ast_manager&              m_manager;
    bv_util                   m_util;
    arith_util                m_arith;
    basic_simplifier_plugin & m_bsimp;
    bv_simplifier_params &    m_params;
    expr_ref_vector           m_zeros;
    extract_cache             m_extract_cache;

    unsigned_vector           m_lows, m_highs;
    ptr_vector<expr>          m_extract_args;

    rational mk_bv_and(numeral const& a0, numeral const& b0, unsigned sz);
    rational mk_bv_or(numeral const& a0, numeral const& b0, unsigned sz);
    rational mk_bv_xor(numeral const& a0, numeral const& b0, unsigned sz);
    rational mk_bv_not(numeral const& a0, unsigned sz);
    rational num(expr* e);
    bool has_sign_bit(numeral const& n, unsigned bv_size) { return m_util.has_sign_bit(n, bv_size); }

    bool shift_shift(bv_op_kind k, expr* arg1, expr* arg2, expr_ref& result);

    void bit2bool_simplify(unsigned idx, expr* e, expr_ref& result);

    void mk_add_concat(expr_ref& result);
    bool is_zero_bit(expr* x, unsigned idx);

    void mk_bv_rotate_left_core(unsigned shift, numeral r, unsigned bv_size, expr_ref& result);
    void mk_bv_rotate_right_core(unsigned shift, numeral r, unsigned bv_size, expr_ref& result);

public:
    bv_simplifier_plugin(ast_manager & m, basic_simplifier_plugin & b, bv_simplifier_params & p);
    virtual ~bv_simplifier_plugin();


    // simplifier_plugin:
    virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    virtual bool reduce_eq(expr * lhs, expr * rhs, expr_ref & result);
    virtual bool reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result);
    virtual void flush_caches();

    // poly_simplifier_plugin
    virtual rational norm(const rational & n);
    virtual bool is_numeral(expr * n, rational & val) const;
    bool is_numeral(expr * n) const { return m_util.is_numeral(n); }
    virtual bool is_minus_one(expr * n) const { return is_minus_one_core(n); }
    virtual expr * get_zero(sort * s) const;
    virtual app * mk_numeral(rational const & n);

    bool is_bv(expr * n) const { return m_util.is_bv(n); }
    bool is_bv_sort(sort * s) const { return m_util.is_bv_sort(s); }

    bool is_le(expr * n) const { return m_util.is_bv_ule(n) || m_util.is_bv_sle(n); }
    // REMARK: simplified bv expressions are never of the form a >= b.
    virtual bool is_le_ge(expr * n) const { return is_le(n); }

    uint64 to_uint64(const numeral & n, unsigned bv_size);
    rational norm(rational const& n, unsigned bv_size, bool is_signed) { return m_util.norm(n, bv_size, is_signed); }
    unsigned get_bv_size(expr const * n) { return get_bv_size(m_manager.get_sort(n)); }
    unsigned get_bv_size(sort const * s) { return m_util.get_bv_size(s); }
    void mk_leq_core(bool is_signed, expr * arg1, expr * arg2, expr_ref & result);
    void mk_ule(expr* a, expr* b, expr_ref& result);
    void mk_ult(expr* a, expr* b, expr_ref& result);
    void mk_sle(expr* a, expr* b, expr_ref& result);
    void mk_slt(expr* a, expr* b, expr_ref& result);
    void mk_bv_and(unsigned num_args, expr * const* args, expr_ref & result);
    void mk_bv_or(unsigned num_args, expr * const* args, expr_ref & result);
    void mk_bv_xor(unsigned num_args, expr * const* args, expr_ref & result);
    void mk_bv_not(expr * arg, expr_ref & result);
    void mk_extract(unsigned hi,unsigned lo, expr* bv, expr_ref& result);
    void mk_extract_core(unsigned high, unsigned low, expr * arg, expr_ref& result);
    void cache_extract(unsigned h, unsigned l, expr * arg, expr * result);
    expr* get_cached_extract(unsigned h, unsigned l, expr * arg);

    bool lookup_mk_extract(unsigned high, unsigned low, expr * arg, expr_ref& result);
    bool try_mk_extract(unsigned high, unsigned low, expr * arg, expr_ref& result);

    void mk_bv_eq(expr* a1, expr* a2, expr_ref& result);
    void mk_eq_core(expr * arg1, expr * arg2, expr_ref & result);
    void mk_args_eq_numeral(app * app, expr * n, expr_ref & result);

    void mk_concat(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_concat(expr * arg1, expr * arg2, expr_ref & result) { 
        expr * args[2] = { arg1, arg2 }; 
        mk_concat(2, args, result); 
    }
    void mk_zeroext(unsigned n, expr * arg, expr_ref & result);
    void mk_repeat(unsigned n, expr * arg, expr_ref & result);
    void mk_sign_extend(unsigned n, expr * arg, expr_ref & result);
    void mk_bv_lshr(expr * arg1, expr * arg2, expr_ref & result);
    void mk_bv_shl(expr * arg1, expr * arg2, expr_ref & result);
    void mk_bv_ashr(expr* arg1, expr* arg2, expr_ref& result);
    void mk_bv_smod(expr* arg1, expr* arg2, expr_ref& result);
    void mk_bv_urem(expr * arg1, expr * arg2, expr_ref & result);
    void mk_bv_srem(expr* arg1, expr* arg2, expr_ref& result);
    void mk_bv_udiv(expr* arg1, expr* arg2, expr_ref& result);
    void mk_bv_sdiv(expr* arg1, expr* arg2, expr_ref& result);
    void mk_bv_smod_i(expr* arg1, expr* arg2, expr_ref& result);
    void mk_bv_urem_i(expr * arg1, expr * arg2, expr_ref & result);
    void mk_bv_srem_i(expr* arg1, expr* arg2, expr_ref& result);
    void mk_bv_udiv_i(expr* arg1, expr* arg2, expr_ref& result);
    void mk_bv_sdiv_i(expr* arg1, expr* arg2, expr_ref& result);
    void mk_bv_nand(unsigned num_args, expr* const* args, expr_ref& result);
    void mk_bv_nor(unsigned num_args, expr* const* args, expr_ref& result);
    void mk_bv_xnor(unsigned num_args, expr* const* args, expr_ref& result);
    void mk_bv_rotate_right(func_decl* f, expr* arg, expr_ref& result);
    void mk_bv_rotate_left(func_decl* f, expr* arg, expr_ref& result);
    void mk_bv_ext_rotate_right(expr* arg1, expr* arg2, expr_ref& result);
    void mk_bv_ext_rotate_left(expr* arg1, expr* arg2, expr_ref& result);

    void mk_bv_redor(expr* arg, expr_ref& result);
    void mk_bv_redand(expr* arg, expr_ref& result);
    void mk_bv_comp(expr* arg1, expr* arg2, expr_ref& result);

    bool are_numerals(unsigned num_args, expr * const* args, unsigned& bv_size);
    app * mk_numeral(rational const & n, unsigned bv_size);
    app * mk_numeral(uint64 n, unsigned bv_size) { return mk_numeral(numeral(n, numeral::ui64()), bv_size); }
    app* mk_bv0(unsigned bv_size) { return m_util.mk_numeral(numeral(0), bv_size); }
    rational mk_allone(unsigned bv_size) { return rational::power_of_two(bv_size) - numeral(1); }
    bool is_minus_one_core(expr * arg) const;
    bool is_x_minus_one(expr * arg, expr * & x);
    void mk_int2bv(expr * arg, sort* range, expr_ref & result);
    void mk_bv2int(expr * arg, sort* range, expr_ref & result);
    uint64 n64(expr* e);
    bool is_mul_no_overflow(expr* e);
    bool is_add_no_overflow(expr* e);
    unsigned num_leading_zero_bits(expr* e);

};

#endif /* _BV_SIMPLIFIER_PLUGIN_H_ */
