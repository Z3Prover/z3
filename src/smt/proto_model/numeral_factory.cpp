/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    numeral_factory.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-28.

Revision History:

--*/
#include"numeral_factory.h"
#include"ast_pp.h"

app * arith_factory::mk_value_core(rational const & val, sort * s) {
    return m_util.mk_numeral(val, s);
}

arith_factory::arith_factory(ast_manager & m):
    numeral_factory(m, m.mk_family_id("arith")),
    m_util(m) {
}

arith_factory::~arith_factory() {
}

app * arith_factory::mk_value(rational const & val, bool is_int) {
    return numeral_factory::mk_value(val, is_int ? m_util.mk_int() : m_util.mk_real());
}

bv_factory::bv_factory(ast_manager & m):
    numeral_factory(m, m.mk_family_id("bv")),
    m_util(m) {
}

bv_factory::~bv_factory() {
}

app * bv_factory::mk_value_core(rational const & val, sort * s) {
    return m_util.mk_numeral(val, s);
}

app * bv_factory::mk_value(rational const & val, unsigned bv_size) {
    return numeral_factory::mk_value(val, m_util.mk_sort(bv_size));
}
