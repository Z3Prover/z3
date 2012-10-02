/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    value.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-08-17.

Revision History:

--*/
#include"value.h"

void bool_value::display(std::ostream & out) const {
    out << (m_value ? "true" : "false");
}

unsigned bool_value::hash() const {
    return m_value ? 1 : 0;
}

bool bool_value::operator==(const value & other) const {
    const bool_value * o = dynamic_cast<const bool_value*>(&other);
    return o && m_value == o->m_value;
}

basic_factory::basic_factory(ast_manager & m):
    value_factory(symbol("basic"), m),
    m_bool(m) {
    m_bool  = m.mk_type(m.get_basic_family_id(), BOOL_SORT);
    m_true  = alloc(bool_value, true, m_bool.get());
    m_false = alloc(bool_value, false, m_bool.get());
}


