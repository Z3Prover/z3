/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    theory_seq_params.h

Abstract:

    Parameters for sequence theory plugin

Revision History:


--*/

#pragma once

#include "util/params.h"

struct theory_seq_params {
    /*
     * Enable splitting guided by length constraints
     */
    bool m_split_w_len = false;
    bool m_seq_validate = false;
    bool m_seq_regex_monadic = false;
    unsigned m_seq_regex_budget = 1000000;
    unsigned m_seq_regex_split = 0;
    symbol m_seq_regex_transition_mode = symbol("light-ant");
    symbol m_seq_regex_orientation = symbol("forward");
    unsigned m_seq_max_unfolding = UINT_MAX/4;
    unsigned m_seq_min_unfolding = 1;
    unsigned m_seq_parikh_k = 2;
    unsigned m_seq_parikh_n = 2;
    unsigned m_seq_parikh_chars = 6;
    // Opt-in gate for eq_approx_split (ast/seq/seq_eq_facet.h), read via
    // ambient_context_i::fparams() rather than a bespoke accessor.
    // Mirrors the c3 branch's `smt.nseq.eq_approx` (also default false -
    // see nielsen_graph::apply_eq_approx's `if (!m_eq_approx) return
    // false;` gate in seq_nielsen_regex.cpp).
    bool m_seq_eq_approx = false;
    // Opt-in gate for power_fine_wilf, mirroring c3's smt.nseq.fine_wilf.
    bool m_seq_fine_wilf = false;
    // Opt-in gate for mem_parikh_split, mirroring c3's smt.nseq.parikh.
    bool m_seq_mem_parikh = false;
    // Master gate for mem_leaf_split (whole-language monadic decision
    // over the conjunction of active plain regex memberships), mirroring
    // c3's smt.nseq.monadic_leaf (default true there). Default here is
    // false: benchmarking on the regexes suite showed mem_leaf_split
    // firing too eagerly on unproductive branches (asking/committing far
    // more often than it refutes), causing a net regression in solved
    // count vs. leaving it off. Enable explicitly once the ask
    // frequency/budget is tuned to actually pay for itself.
    bool m_seq_monadic_leaf = false;
    unsigned m_seq_monadic_leaf_budget = 300000;
    unsigned m_seq_block_compression = 0;
    // Run mem_leaf_split's refutation-only ask once at the search root
    // before the DFS proper starts, mirroring c3's smt.nseq.monadic_leaf_root
    // and nielsen_graph::monadic_leaf_root_refute.
    bool m_seq_monadic_leaf_root = true;
    unsigned m_seq_monadic_leaf_budget_root = 50000;
    // Gate for mem_facet's incremental single-variable regex-intersection
    // feasibility check (view_witness/vw().check() in mem_propagation),
    // mirroring c3's smt.nseq.regex_precheck.
    bool m_seq_regex_precheck = true;

    theory_seq_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }

    void updt_params(params_ref const & p);
};
