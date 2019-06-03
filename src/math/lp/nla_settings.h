/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/

#pragma once
namespace nla {
class nla_settings {
    bool m_run_order;
    bool m_run_tangents;
public:
    nla_settings() : m_run_order(true), m_run_tangents(true) {}
    bool run_order() const { return m_run_order; }
    bool& run_order() { return m_run_order; }

    bool run_tangents() const { return m_run_tangents; }
    bool& run_tangents() { return m_run_tangents; }    
};
}
