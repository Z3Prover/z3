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
    unsigned m_horner_subs_fixed;
    // grobner fields
    bool     m_run_grobner;
    unsigned m_grobner_row_length_limit;
    unsigned m_grobner_subs_fixed;
    unsigned m_grobner_eqs_growth;
    unsigned m_grobner_tree_size_growth;
    unsigned m_grobner_expr_size_growth;
    unsigned m_grobner_expr_degree_growth;
    unsigned m_grobner_max_simplified;
    unsigned m_grobner_number_of_conflicts_to_report;
public:
    nla_settings() : m_run_order(true),
                     m_run_tangents(true),
                     m_run_horner(true),
                     m_horner_frequency(4),
                     m_horner_row_length_limit(10),
                     m_horner_subs_fixed(2),
                     m_run_grobner(true),
                     m_grobner_row_length_limit(50),
                     m_grobner_subs_fixed(false)
    {}
    unsigned grobner_eqs_growth() const { return m_grobner_eqs_growth;}
    unsigned& grobner_eqs_growth() { return m_grobner_eqs_growth;}
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
    unsigned horner_subs_fixed() const { return m_horner_subs_fixed; }
    unsigned& horner_subs_fixed() { return m_horner_subs_fixed; }

    bool run_grobner() const { return m_run_grobner; }
    bool& run_grobner() { return m_run_grobner; }

    unsigned grobner_row_length_limit() const { return m_grobner_row_length_limit; }
    unsigned& grobner_row_length_limit() { return m_grobner_row_length_limit; }
    unsigned grobner_subs_fixed() const { return m_grobner_subs_fixed; }
    unsigned& grobner_subs_fixed() { return m_grobner_subs_fixed; }

    unsigned grobner_tree_size_growth() const { return m_grobner_tree_size_growth; }
    unsigned & grobner_tree_size_growth() { return m_grobner_tree_size_growth; }

    unsigned grobner_expr_size_growth() const { return m_grobner_expr_size_growth; }
    unsigned & grobner_expr_size_growth() { return m_grobner_expr_size_growth; }

    unsigned grobner_expr_degree_growth() const { return m_grobner_expr_degree_growth; }
    unsigned & grobner_expr_degree_growth() { return m_grobner_expr_degree_growth; }

    unsigned grobner_max_simplified() const { return m_grobner_max_simplified; }
    unsigned & grobner_max_simplified() { return m_grobner_max_simplified; }

    unsigned grobner_number_of_conflicts_to_report() const { return m_grobner_number_of_conflicts_to_report; }
    unsigned & grobner_number_of_conflicts_to_report() { return m_grobner_number_of_conflicts_to_report; }

    
};
}
