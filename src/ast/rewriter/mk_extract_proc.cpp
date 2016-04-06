/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  mk_extract_proc.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include"mk_extract_proc.h"
mk_extract_proc::mk_extract_proc(bv_util & u):
    m_util(u),
    m_high(0),
    m_low(UINT_MAX),
    m_domain(0),
    m_f_cached(0) {
}

mk_extract_proc::~mk_extract_proc() {
    if (m_f_cached) {
        // m_f_cached has a reference to m_domain, so, I don't need to inc_ref m_domain
        ast_manager & m = m_util.get_manager();
        m.dec_ref(m_f_cached);
    }
}

app * mk_extract_proc::operator()(unsigned high, unsigned low, expr * arg) {
    ast_manager & m = m_util.get_manager();
    sort * s = m.get_sort(arg);
    if (m_low == low && m_high == high && m_domain == s)
        return m.mk_app(m_f_cached, arg);
    // m_f_cached has a reference to m_domain, so, I don't need to inc_ref m_domain
    if (m_f_cached)
        m.dec_ref(m_f_cached);
    app * r    = to_app(m_util.mk_extract(high, low, arg));
    m_high     = high;
    m_low      = low;
    m_domain   = s;
    m_f_cached = r->get_decl();
    m.inc_ref(m_f_cached);
    return r;
}
