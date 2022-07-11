/*++
Copyright (c) 2017 Microsoft Corporation

Author:

    Lev Nachmanson (levnach)

--*/

#pragma once
namespace nla {
    struct nla_settings {
        bool     run_order     = true;
        bool     run_tangents  = true;
        
        // horner fields
        bool     run_horner              = true;
        unsigned horner_frequency        = 4;
        unsigned horner_row_length_limit = 10;
        unsigned horner_subs_fixed       = 2;

        
        // grobner fields
        bool     run_grobner                = true;
        unsigned grobner_row_length_limit   = 50;
        unsigned grobner_subs_fixed         = 1;
        unsigned grobner_eqs_growth         = 10;
        unsigned grobner_tree_size_growth   = 2;
        unsigned grobner_expr_size_growth   = 2;
        unsigned grobner_expr_degree_growth = 2;
        unsigned grobner_max_simplified     = 10000;
        unsigned grobner_number_of_conflicts_to_report = 1;
        unsigned grobner_quota      = 0;
        unsigned grobner_frequency  = 4;


        // nra fields
        bool     run_nra = false;
    
        // expensive patching
        bool     expensive_patching = false;

        nla_settings() {}

    };
}
