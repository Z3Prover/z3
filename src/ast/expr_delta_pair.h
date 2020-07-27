/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    expr_delta_pair.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-14.

Revision History:

--*/
#pragma once

/**
   \brief Auxiliary structure used to cache the intermediate results of the variable substitution procedure.
*/
struct expr_delta_pair {
    expr *    m_node;
    unsigned  m_delta;
    
    expr_delta_pair():m_node(nullptr), m_delta(0) {}
    expr_delta_pair(expr * n, unsigned d):m_node(n), m_delta(d) {}
    unsigned hash() const { return hash_u_u(m_node->hash(), m_delta); }
    bool operator==(const expr_delta_pair & e) const { return m_node == e.m_node && m_delta == e.m_delta; }
};


