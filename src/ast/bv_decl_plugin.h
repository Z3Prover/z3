/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bv_decl_plugin.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-09.

Revision History:

--*/
#ifndef BV_DECL_PLUGIN_H_
#define BV_DECL_PLUGIN_H_

#include"ast.h"

enum bv_sort_kind {
    BV_SORT
};

enum bv_op_kind {
    OP_BV_NUM,
    OP_BIT1,
    OP_BIT0,
    OP_BNEG,
    OP_BADD,
    OP_BSUB,
    OP_BMUL,

    OP_BSDIV,
    OP_BUDIV,
    OP_BSREM,
    OP_BUREM,
    OP_BSMOD,

    // special functions to record the division by 0 cases
    // these are internal functions
    OP_BSDIV0,
    OP_BUDIV0,
    OP_BSREM0,
    OP_BUREM0,
    OP_BSMOD0,

    // special functions where division by 0 has a fixed interpretation.
    OP_BSDIV_I,
    OP_BUDIV_I,
    OP_BSREM_I,
    OP_BUREM_I,
    OP_BSMOD_I,

    OP_ULEQ,
    OP_SLEQ,
    OP_UGEQ,
    OP_SGEQ,
    OP_ULT,
    OP_SLT,
    OP_UGT,
    OP_SGT,

    OP_BAND,
    OP_BOR,
    OP_BNOT,
    OP_BXOR,
    OP_BNAND,
    OP_BNOR,
    OP_BXNOR,

    OP_CONCAT,
    OP_SIGN_EXT,
    OP_ZERO_EXT,
    OP_EXTRACT,
    OP_REPEAT,

    OP_BREDOR,
    OP_BREDAND,
    OP_BCOMP,

    OP_BSHL,
    OP_BLSHR,
    OP_BASHR,
    OP_ROTATE_LEFT,
    OP_ROTATE_RIGHT,
    OP_EXT_ROTATE_LEFT,
    OP_EXT_ROTATE_RIGHT,

    OP_BUMUL_NO_OVFL, // no unsigned multiplication overflow predicate
    OP_BSMUL_NO_OVFL, // no signed multiplication overflow predicate
    OP_BSMUL_NO_UDFL, // no signed multiplication underflow predicate

    OP_BIT2BOOL, // predicate
    OP_MKBV,     // bools to bv
    OP_INT2BV,
    OP_BV2INT,

    OP_CARRY,
    OP_XOR3,

    LAST_BV_OP
};

// Assume k is a "div" operator. It returns the div0 uninterpreted function that
// models the value of "div" it is underspecified (i.e., when the denominator is zero).
inline bv_op_kind get_div0_op(bv_op_kind k) {
    switch (k) {
    case OP_BSDIV: return OP_BSDIV0;
    case OP_BUDIV: return OP_BUDIV0;
    case OP_BSREM: return OP_BSREM0;
    case OP_BUREM: return OP_BUREM0;
    case OP_BSMOD: return OP_BSMOD0;
    default: UNREACHABLE(); return LAST_BV_OP;
    }
}

// Assume decl is the declaration of a "div" operator. It returns the div0 declaration that
// models the value of "div" it is underspecified (i.e., when the denominator is zero).
inline func_decl * get_div0_decl(ast_manager & m, func_decl * decl) {
    return m.mk_func_decl(decl->get_family_id(), get_div0_op(static_cast<bv_op_kind>(decl->get_decl_kind())),
                          0, 0, 1, decl->get_domain());
}

class bv_decl_plugin : public decl_plugin {
protected:
    symbol m_bv_sym;
    symbol m_concat_sym;
    symbol m_sign_extend_sym;
    symbol m_zero_extend_sym;
    symbol m_extract_sym;
    symbol m_rotate_left_sym;
    symbol m_rotate_right_sym;
    symbol m_repeat_sym;
    symbol m_bit2bool_sym;
    symbol m_mkbv_sym;

    func_decl * m_bit0;
    func_decl * m_bit1;
    func_decl * m_carry;
    func_decl * m_xor3;

    ptr_vector<sort>   m_bv_sorts;
    sort *             m_int_sort;

    ptr_vector<func_decl>  m_bv_neg;
    ptr_vector<func_decl>  m_bv_add;
    ptr_vector<func_decl>  m_bv_sub;
    ptr_vector<func_decl>  m_bv_mul;
    ptr_vector<func_decl>  m_bv_sdiv;
    ptr_vector<func_decl>  m_bv_udiv;
    ptr_vector<func_decl>  m_bv_srem;
    ptr_vector<func_decl>  m_bv_urem;
    ptr_vector<func_decl>  m_bv_smod;

    ptr_vector<func_decl>  m_bv_sdiv0;
    ptr_vector<func_decl>  m_bv_udiv0;
    ptr_vector<func_decl>  m_bv_srem0;
    ptr_vector<func_decl>  m_bv_urem0;
    ptr_vector<func_decl>  m_bv_smod0;

    ptr_vector<func_decl>  m_bv_sdiv_i;
    ptr_vector<func_decl>  m_bv_udiv_i;
    ptr_vector<func_decl>  m_bv_srem_i;
    ptr_vector<func_decl>  m_bv_urem_i;
    ptr_vector<func_decl>  m_bv_smod_i;

    ptr_vector<func_decl>  m_bv_uleq;
    ptr_vector<func_decl>  m_bv_sleq;
    ptr_vector<func_decl>  m_bv_ugeq;
    ptr_vector<func_decl>  m_bv_sgeq;
    ptr_vector<func_decl>  m_bv_ult;
    ptr_vector<func_decl>  m_bv_slt;
    ptr_vector<func_decl>  m_bv_ugt;
    ptr_vector<func_decl>  m_bv_sgt;

    ptr_vector<func_decl>  m_bv_and;
    ptr_vector<func_decl>  m_bv_or;
    ptr_vector<func_decl>  m_bv_not;
    ptr_vector<func_decl>  m_bv_xor;
    ptr_vector<func_decl>  m_bv_nand;
    ptr_vector<func_decl>  m_bv_nor;
    ptr_vector<func_decl>  m_bv_xnor;

    ptr_vector<func_decl>  m_bv_redor;
    ptr_vector<func_decl>  m_bv_redand;
    ptr_vector<func_decl>  m_bv_comp;

    ptr_vector<func_decl>  m_bv_mul_ovfl;
    ptr_vector<func_decl>  m_bv_smul_ovfl;
    ptr_vector<func_decl>  m_bv_smul_udfl;

    ptr_vector<func_decl>  m_bv_shl;
    ptr_vector<func_decl>  m_bv_lshr;
    ptr_vector<func_decl>  m_bv_ashr;
    ptr_vector<func_decl>  m_ext_rotate_left;
    ptr_vector<func_decl>  m_ext_rotate_right;

    ptr_vector<func_decl>  m_bv2int;
    ptr_vector<func_decl>  m_int2bv;
    vector<ptr_vector<func_decl> > m_bit2bool;
    ptr_vector<func_decl>  m_mkbv;

    virtual void set_manager(ast_manager * m, family_id id);
    void mk_bv_sort(unsigned bv_size);
    sort * get_bv_sort(unsigned bv_size);
    func_decl * mk_func_decl(decl_kind k, unsigned bv_size);
    func_decl * mk_binary(ptr_vector<func_decl> & decls, decl_kind k,
                          char const * name, unsigned bv_size, bool ac, bool idempotent = false);
    func_decl * mk_unary(ptr_vector<func_decl> & decls, decl_kind k, char const * name, unsigned bv_size);
    func_decl * mk_pred(ptr_vector<func_decl> & decls, decl_kind k,
                        char const * name, unsigned bv_size);
    func_decl * mk_reduction(ptr_vector<func_decl> & decls, decl_kind k, char const * name, unsigned bv_size);
    func_decl * mk_comp(unsigned bv_size);
    bool get_bv_size(sort * t, int & result);
    bool get_bv_size(expr * t, int & result);
    bool get_concat_size(unsigned arity, sort * const * domain, int & result);
    bool get_extend_size(unsigned num_parameters, parameter const * parameters,
                         unsigned arity, sort * const * domain, int & result);
    bool get_extract_size(unsigned num_parameters, parameter const * parameters,
                          unsigned arity, sort * const * domain, int & result);

    func_decl * mk_bv2int(unsigned bv_size, unsigned num_parameters, parameter const * parameters,
                          unsigned arity, sort * const * domain);

    func_decl * mk_int2bv(unsigned bv_size, unsigned num_parameters, parameter const * parameters,
                          unsigned arity, sort * const * domain);

    func_decl * mk_bit2bool(unsigned bv_size, unsigned num_parameters, parameter const * parameters,
                            unsigned arity, sort * const * domain);

    func_decl * mk_mkbv(unsigned arity, sort * const * domain);


    func_decl * mk_num_decl(unsigned num_parameters, parameter const * parameters, unsigned arity);

    void get_offset_term(app * a, expr * & t, rational & offset) const;
public:
    bv_decl_plugin();

    virtual ~bv_decl_plugin() {}
    virtual void finalize();

    virtual decl_plugin * mk_fresh() { return alloc(bv_decl_plugin); }

    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);

    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range);

    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned num_args, expr * const * args, sort * range);

    virtual bool is_value(app * e) const;

    virtual bool is_unique_value(app * e) const { return is_value(e); }

    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);

    virtual void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic);

    virtual bool are_distinct(app* a, app* b) const;

    virtual expr * get_some_value(sort * s);

    bool get_int2bv_size(unsigned num_parameters, parameter const * parameters, int & result);

    virtual bool is_considered_uninterpreted(func_decl * f) {
        if (f->get_family_id() != get_family_id())
            return false;
        switch (f->get_decl_kind()) {
        case OP_BSDIV0:
        case OP_BUDIV0:
        case OP_BSREM0:
        case OP_BUREM0:
        case OP_BSMOD0:
            return true;
        default:
            return false;
        }
        return false;
    }
};

class bv_recognizers {
    family_id m_afid;
public:
    bv_recognizers(family_id fid):m_afid(fid) {}

    family_id get_fid() const { return m_afid; }
    family_id get_family_id() const { return get_fid(); }

    bool is_numeral(expr const * n, rational & val, unsigned & bv_size) const;
    bool is_numeral(expr const * n) const { return is_app_of(n, get_fid(), OP_BV_NUM); }
    bool is_allone(expr const * e) const;
    bool is_zero(expr const * e) const;
    bool is_bv_sort(sort const * s) const;
    bool is_bv(expr const* e) const {  return is_bv_sort(get_sort(e)); }

    bool is_concat(expr const * e) const { return is_app_of(e, get_fid(), OP_CONCAT); }
    bool is_extract(func_decl const * f) const { return is_decl_of(f, get_fid(), OP_EXTRACT); }
    bool is_extract(expr const * e) const { return is_app_of(e, get_fid(), OP_EXTRACT); }
    unsigned get_extract_high(func_decl const * f) const { return f->get_parameter(0).get_int(); }
    unsigned get_extract_low(func_decl const * f) const { return f->get_parameter(1).get_int(); }
    unsigned get_extract_high(expr const * n) const { SASSERT(is_extract(n)); return get_extract_high(to_app(n)->get_decl()); }
    unsigned get_extract_low(expr const * n) const { SASSERT(is_extract(n)); return get_extract_low(to_app(n)->get_decl()); }
    bool is_extract(expr const * e, unsigned & low, unsigned & high, expr * & b) const;
    bool is_bv2int(expr const * e, expr * & r) const;
    bool is_bv_add(expr const * e) const { return is_app_of(e, get_fid(), OP_BADD); }
    bool is_bv_sub(expr const * e) const { return is_app_of(e, get_fid(), OP_BSUB); }
    bool is_bv_mul(expr const * e) const { return is_app_of(e, get_fid(), OP_BMUL); }
    bool is_bv_neg(expr const * e) const { return is_app_of(e, get_fid(), OP_BNEG); }

    bool is_bv_sdiv(expr const * e) const { return is_app_of(e, get_fid(), OP_BSDIV); }
    bool is_bv_udiv(expr const * e) const { return is_app_of(e, get_fid(), OP_BUDIV); }
    bool is_bv_srem(expr const * e) const { return is_app_of(e, get_fid(), OP_BSREM); }
    bool is_bv_urem(expr const * e) const { return is_app_of(e, get_fid(), OP_BUREM); }
    bool is_bv_smod(expr const * e) const { return is_app_of(e, get_fid(), OP_BSMOD); }

    bool is_bv_sdiv0(expr const * e) const { return is_app_of(e, get_fid(), OP_BSDIV0); }
    bool is_bv_udiv0(expr const * e) const { return is_app_of(e, get_fid(), OP_BUDIV0); }
    bool is_bv_srem0(expr const * e) const { return is_app_of(e, get_fid(), OP_BSREM0); }
    bool is_bv_urem0(expr const * e) const { return is_app_of(e, get_fid(), OP_BUREM0); }
    bool is_bv_smod0(expr const * e) const { return is_app_of(e, get_fid(), OP_BSMOD0); }

    bool is_bv_sdivi(expr const * e) const { return is_app_of(e, get_fid(), OP_BSDIV_I); }
    bool is_bv_udivi(expr const * e) const { return is_app_of(e, get_fid(), OP_BUDIV_I); }
    bool is_bv_sremi(expr const * e) const { return is_app_of(e, get_fid(), OP_BSREM_I); }
    bool is_bv_uremi(expr const * e) const { return is_app_of(e, get_fid(), OP_BUREM_I); }
    bool is_bv_smodi(expr const * e) const { return is_app_of(e, get_fid(), OP_BSMOD_I); }

    bool is_bv_and(expr const * e) const { return is_app_of(e, get_fid(), OP_BAND); }
    bool is_bv_or(expr const * e) const { return is_app_of(e, get_fid(), OP_BOR); }
    bool is_bv_xor(expr const * e) const { return is_app_of(e, get_fid(), OP_BXOR); }
    bool is_bv_nand(expr const * e) const { return is_app_of(e, get_fid(), OP_BNAND); }
    bool is_bv_nor(expr const * e) const { return is_app_of(e, get_fid(), OP_BNOR); }
    bool is_bv_not(expr const * e) const { return is_app_of(e, get_fid(), OP_BNOT); }
    bool is_bv_ule(expr const * e) const { return is_app_of(e, get_fid(), OP_ULEQ); }
    bool is_bv_sle(expr const * e) const { return is_app_of(e, get_fid(), OP_SLEQ); }
    bool is_bit2bool(expr const * e) const { return is_app_of(e, get_fid(), OP_BIT2BOOL); }
    bool is_bv2int(expr const* e) const { return is_app_of(e, get_fid(), OP_BV2INT); }
    bool is_int2bv(expr const* e) const { return is_app_of(e, get_fid(), OP_INT2BV); }
    bool is_mkbv(expr const * e) const { return is_app_of(e, get_fid(), OP_MKBV); }
    bool is_bv_ashr(expr const * e) const { return is_app_of(e, get_fid(), OP_BASHR); }
    bool is_bv_lshr(expr const * e) const { return is_app_of(e, get_fid(), OP_BLSHR); }
    bool is_bv_shl(expr const * e) const { return is_app_of(e, get_fid(), OP_BSHL); }
    bool is_sign_ext(expr const * e) const { return is_app_of(e, get_fid(), OP_SIGN_EXT); }

    MATCH_BINARY(is_bv_add);
    MATCH_BINARY(is_bv_mul);
    MATCH_BINARY(is_bv_sle);
    MATCH_BINARY(is_bv_ule);
    MATCH_BINARY(is_bv_shl);
    MATCH_BINARY(is_bv_urem);
    MATCH_BINARY(is_bv_srem);
    MATCH_BINARY(is_bv_sdiv);
    MATCH_BINARY(is_bv_udiv);
    MATCH_BINARY(is_bv_smod);

    MATCH_BINARY(is_bv_uremi);
    MATCH_BINARY(is_bv_sremi);
    MATCH_BINARY(is_bv_sdivi);
    MATCH_BINARY(is_bv_udivi);
    MATCH_BINARY(is_bv_smodi);

    rational norm(rational const & val, unsigned bv_size, bool is_signed) const ;
    rational norm(rational const & val, unsigned bv_size) const { return norm(val, bv_size, false); }
    bool has_sign_bit(rational const & n, unsigned bv_size) const;
    bool mult_inverse(rational const & n, unsigned bv_size, rational & result);
};

class bv_util : public bv_recognizers {
    ast_manager &    m_manager;
    bv_decl_plugin * m_plugin;

public:
    bv_util(ast_manager & m);

    ast_manager & get_manager() const { return m_manager; }

    app * mk_numeral(rational const & val, sort* s);
    app * mk_numeral(rational const & val, unsigned bv_size);
    app * mk_numeral(uint64 u, unsigned bv_size) { return mk_numeral(rational(u, rational::ui64()), bv_size); }
    sort * mk_sort(unsigned bv_size);

    unsigned get_bv_size(sort const * s) const {
        SASSERT(is_bv_sort(s));
        return static_cast<unsigned>(s->get_parameter(0).get_int());
    }
    unsigned get_bv_size(expr const * n) const { return get_bv_size(m_manager.get_sort(n)); }
    unsigned get_int2bv_size(parameter const& p);


    app * mk_ule(expr * arg1, expr * arg2) { return m_manager.mk_app(get_fid(), OP_ULEQ, arg1, arg2); }
    app * mk_sle(expr * arg1, expr * arg2) { return m_manager.mk_app(get_fid(), OP_SLEQ, arg1, arg2); }
    app * mk_extract(unsigned high, unsigned low, expr * n) {
        parameter params[2] = { parameter(high), parameter(low) };
        return m_manager.mk_app(get_fid(), OP_EXTRACT, 2, params, 1, &n);
    }
    app * mk_concat(unsigned num, expr * const * args) { return m_manager.mk_app(get_fid(), OP_CONCAT, num, args);  }
    app * mk_concat(expr * arg1, expr * arg2) { expr * args[2] = { arg1, arg2 }; return mk_concat(2, args); }
    app * mk_bv_or(unsigned num, expr * const * args) { return m_manager.mk_app(get_fid(), OP_BOR, num, args);  }
    app * mk_bv_not(expr * arg) { return m_manager.mk_app(get_fid(), OP_BNOT, arg); }
    app * mk_bv_xor(unsigned num, expr * const * args) { return m_manager.mk_app(get_fid(), OP_BXOR, num, args);  }
    app * mk_bv_neg(expr * arg) { return m_manager.mk_app(get_fid(), OP_BNEG, arg); }
    app * mk_bv_urem(expr * arg1, expr * arg2) { return m_manager.mk_app(get_fid(), OP_BUREM, arg1, arg2); }
    app * mk_bv_srem(expr * arg1, expr * arg2) { return m_manager.mk_app(get_fid(), OP_BSREM, arg1, arg2); }
    app * mk_bv_add(expr * arg1, expr * arg2) { return m_manager.mk_app(get_fid(), OP_BADD, arg1, arg2); }
    app * mk_bv_sub(expr * arg1, expr * arg2) { return m_manager.mk_app(get_fid(), OP_BSUB, arg1, arg2); }
    app * mk_bv_mul(expr * arg1, expr * arg2) { return m_manager.mk_app(get_fid(), OP_BMUL, arg1, arg2); }
    app * mk_zero_extend(unsigned n, expr* e) {
        parameter p(n);
        return m_manager.mk_app(get_fid(), OP_ZERO_EXT, 1, &p, 1, &e);
    }
    app * mk_sign_extend(unsigned n, expr* e) {
        parameter p(n);
        return m_manager.mk_app(get_fid(), OP_SIGN_EXT, 1, &p, 1, &e);
    }
    app * mk_bv_shl(expr* arg1, expr* arg2) { return m_manager.mk_app(get_fid(), OP_BSHL, arg1, arg2); }
    app * mk_bv_ashr(expr* arg1, expr* arg2) { return m_manager.mk_app(get_fid(), OP_BASHR, arg1, arg2); }
    app * mk_bv_lshr(expr* arg1, expr* arg2) { return m_manager.mk_app(get_fid(), OP_BLSHR, arg1, arg2); }

    app * mk_bv2int(expr* e);

    app * mk_bvsmul_no_ovfl(expr* m, expr* n) { return m_manager.mk_app(get_fid(), OP_BSMUL_NO_OVFL, n, m); }
    app * mk_bvsmul_no_udfl(expr* m, expr* n) { return m_manager.mk_app(get_fid(), OP_BSMUL_NO_UDFL, n, m); }
    app * mk_bvumul_no_ovfl(expr* m, expr* n) { return m_manager.mk_app(get_fid(), OP_BUMUL_NO_OVFL, n, m); }

    app * mk_bv(unsigned n, expr* const* es) { return m_manager.mk_app(get_fid(), OP_MKBV, n, es); }

};

#endif /* BV_DECL_PLUGIN_H_ */

