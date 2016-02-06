/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bit_blaster.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-05.

Revision History:

--*/
#include"bit_blaster.h"
#include"bit_blaster_tpl_def.h"
#include"ast_pp.h"
#include"bv_decl_plugin.h"

bit_blaster_cfg::bit_blaster_cfg(bv_util & u, bit_blaster_params const & p, bool_rewriter& rw):
    m_util(u),
    m_params(p),
    m_rw(rw) {
}

static void sort_args(expr * & l1, expr * & l2, expr * & l3) {
    expr * args[3] = {l1, l2, l3};
    // ast_lt_proc is based on the AST ids. So, it is a total order on AST nodes.
    // No need for stable_sort
    std::sort(args, args+3, ast_lt_proc());
    l1 = args[0]; l2 = args[1]; l3 = args[2];
}

void bit_blaster_cfg::mk_xor3(expr * l1, expr * l2, expr * l3, expr_ref & r) {
    TRACE("xor3", tout << "#" << l1->get_id() << " #" << l2->get_id() << " #" << l3->get_id(););
    sort_args(l1, l2, l3);
    TRACE("xor3_sorted", tout << "#" << l1->get_id() << " #" << l2->get_id() << " #" << l3->get_id(););
    if (m_params.m_bb_ext_gates) {
        if (l1 == l2)
            r = l3;
        else if (l1 == l3)
            r = l2;
        else if (l2 == l3)
            r = l1;
        else if (m().is_complement(l1, l2))
            m_rw.mk_not(l3, r);
        else if (m().is_complement(l1, l3))
            m_rw.mk_not(l2, r);
        else if (m().is_complement(l2, l3))
            m_rw.mk_not(l1, r);
        else if (m().is_true(l1))
            m_rw.mk_iff(l2, l3, r);
        else if (m().is_false(l1))
            m_rw.mk_xor(l2, l3, r);
        else if (m().is_true(l2))
            m_rw.mk_iff(l1, l3, r);
        else if (m().is_false(l2))
            m_rw.mk_xor(l1, l3, r);
        else if (m().is_true(l3))
            m_rw.mk_iff(l1, l2, r);
        else if (m().is_false(l3))
            m_rw.mk_xor(l1, l2, r);
        else
            r = m().mk_app(m_util.get_family_id(), OP_XOR3, l1, l2, l3);
    }
    else {
        expr_ref t(m());
        m_rw.mk_xor(l1, l2, t);
        m_rw.mk_xor(t, l3, r);
    }
}

void bit_blaster_cfg::mk_carry(expr * l1, expr * l2, expr * l3, expr_ref & r) {
    TRACE("carry", tout << "#" << l1->get_id() << " #" << l2->get_id() << " #" << l3->get_id(););
    sort_args(l1, l2, l3);
    TRACE("carry_sorted", tout << "#" << l1->get_id() << " #" << l2->get_id() << " #" << l3->get_id(););
    if (m_params.m_bb_ext_gates) {
        if ((m().is_false(l1) && m().is_false(l2)) ||
            (m().is_false(l1) && m().is_false(l3)) ||
            (m().is_false(l2) && m().is_false(l3)))
            r = m().mk_false();
        else if ((m().is_true(l1) && m().is_true(l2)) ||
                 (m().is_true(l1) && m().is_true(l3)) ||
                 (m().is_true(l2) && m().is_true(l3)))
            r = m().mk_true();
        else if (l1 == l2 && l1 == l3)
            r = l1;
        else if (m().is_false(l1))
            m_rw.mk_and(l2, l3, r);
        else if (m().is_false(l2))
            m_rw.mk_and(l1, l3, r);
        else if (m().is_false(l3))
            m_rw.mk_and(l1, l2, r);
        else if (m().is_true(l1))
            m_rw.mk_or(l2, l3, r);
        else if (m().is_true(l2))
            m_rw.mk_or(l1, l3, r);
        else if (m().is_true(l3))
            m_rw.mk_or(l1, l2, r);
        else if (m().is_complement(l1, l2))
            r = l3;
        else if (m().is_complement(l1, l3))
            r = l2;
        else if (m().is_complement(l2, l3))
            r = l1;
        else 
            r = m().mk_app(m_util.get_family_id(), OP_CARRY, l1, l2, l3);
    }
    else {
        expr_ref t1(m()), t2(m()), t3(m());
        m_rw.mk_and(l1, l2, t1);
        m_rw.mk_and(l1, l3, t2);
        m_rw.mk_and(l2, l3, t3);
        m_rw.mk_or(t1, t2, t3, r);
    }
}

template class bit_blaster_tpl<bit_blaster_cfg>;

bit_blaster::bit_blaster(ast_manager & m, bit_blaster_params const & params):
    bit_blaster_tpl<bit_blaster_cfg>(bit_blaster_cfg(m_util, params, m_rw)),
    m_util(m),
    m_rw(m) {
}
