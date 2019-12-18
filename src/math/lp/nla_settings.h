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
    bool     m_run_order;
    bool     m_run_tangents;
    bool     m_run_horner;
    // how often to call the horner heuristic
    unsigned m_horner_frequency;
    unsigned m_horner_row_length_limit;
    // grobner fields
    bool     m_run_grobner;
    unsigned m_grobner_frequency;
    unsigned m_grobner_eqs_threshold;
    unsigned m_grobner_row_length_limit;
    unsigned m_grobner_expr_size_limit;

public:
    nla_settings() : m_run_order(true),
                     m_run_tangents(true),
                     m_run_horner(true),
                     m_horner_frequency(4),
                     m_horner_row_length_limit(10),
                     m_run_grobner(true),
                     m_grobner_frequency(5),
                     m_grobner_eqs_threshold(512),
                     m_grobner_row_length_limit(10),
                     m_grobner_expr_size_limit(20)
    {}
    
    unsigned grobner_eqs_threshold() const { return m_grobner_eqs_threshold; }
    unsigned& grobner_eqs_threshold() { return m_grobner_eqs_threshold; }

    bool run_order() const { return m_run_order; }
    bool& run_order() { return m_run_order; }

    bool run_tangents() const { return m_run_tangents; }
    bool& run_tangents() { return m_run_tangents; }    

    bool run_horner() const { return m_run_horner; }
    bool& run_horner() { return m_run_horner; }    

    unsigned horner_frequency() const { return m_horner_frequency; }
    unsigned& horner_frequency() { return m_horner_frequency; }
    unsigned horner_row_length_limit() const { return m_horner_row_length_limit; }
    unsigned& horner_row_length_limit() { return m_horner_row_length_limit; }    

    bool run_grobner() const { return m_run_grobner; }
    bool& run_grobner() { return m_run_grobner; }    

    unsigned grobner_row_length_limit() const { return m_grobner_row_length_limit; }
    unsigned grobner_expr_size_limit() const { return m_grobner_expr_size_limit; }
};
}
