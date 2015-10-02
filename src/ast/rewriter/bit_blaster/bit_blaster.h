/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bit_blaster.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-05.

Revision History:

--*/
#ifndef BIT_BLASTER_H_
#define BIT_BLASTER_H_

#include"basic_simplifier_plugin.h"
#include"bit_blaster_params.h"
#include"bit_blaster_tpl.h"
#include"bv_decl_plugin.h"
#include"rational.h"

class bit_blaster_cfg {
public:
    typedef rational numeral;
protected:
    bv_util                  &  m_util;
    bit_blaster_params const &  m_params;
    basic_simplifier_plugin  &  s;
public:
    bit_blaster_cfg(bv_util & u, bit_blaster_params const & p, basic_simplifier_plugin & _s);

    ast_manager & m() const { return m_util.get_manager(); }
    numeral power(unsigned n) const { return rational::power_of_two(n); }
    void mk_xor(expr * a, expr * b, expr_ref & r) { s.mk_xor(a, b, r); }
    void mk_xor3(expr * a, expr * b, expr * c, expr_ref & r);
    void mk_carry(expr * a, expr * b, expr * c, expr_ref & r);
    void mk_iff(expr * a, expr * b, expr_ref & r) { s.mk_iff(a, b, r); }
    void mk_and(expr * a, expr * b, expr_ref & r) { s.mk_and(a, b, r); }
    void mk_and(expr * a, expr * b, expr * c, expr_ref & r) { s.mk_and(a, b, c, r); }
    void mk_and(unsigned sz, expr * const * args, expr_ref & r) { s.mk_and(sz, args, r); }
    void mk_or(expr * a, expr * b, expr_ref & r) { s.mk_or(a, b, r); }
    void mk_or(expr * a, expr * b, expr * c, expr_ref & r) { s.mk_or(a, b, c, r); }
    void mk_or(unsigned sz, expr * const * args, expr_ref & r) { s.mk_or(sz, args, r); }
    void mk_not(expr * a, expr_ref & r) { s.mk_not(a, r); }
    void mk_ite(expr * c, expr * t, expr * e, expr_ref & r) { s.mk_ite(c, t, e, r); }
    void mk_nand(expr * a, expr * b, expr_ref & r) { s.mk_nand(a, b, r); }
    void mk_nor(expr * a, expr * b, expr_ref & r) { s.mk_nor(a, b, r); }
};

class bit_blaster : public bit_blaster_tpl<bit_blaster_cfg> {
    bv_util                 m_util;
    basic_simplifier_plugin m_simp;
public:
    bit_blaster(ast_manager & m, bit_blaster_params const & params);
    bit_blaster_params const & get_params() const { return this->m_params; }
};

#endif /* BIT_BLASTER_H_ */

