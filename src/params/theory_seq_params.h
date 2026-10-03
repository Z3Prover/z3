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
    // ambient_context_i::fparams(). Mirrors c3's `smt.nseq.eq_approx`.
    bool m_seq_eq_approx = false;
    // Opt-in gate for power_fine_wilf, mirroring c3's smt.nseq.fine_wilf.
    bool m_seq_fine_wilf = false;
    // Opt-in gate for mem_parikh_split, mirroring c3's smt.nseq.parikh.
    bool m_seq_mem_parikh = false;
    // Master gate for mem_leaf_split, the whole-language monadic decision
    // over active plain regex memberships. Mirrors c3's
    // `smt.nseq.monadic_leaf`; default false here because current tuning
    // made it too eager on the regexes suite.
    bool m_seq_monadic_leaf = false;
    unsigned m_seq_monadic_leaf_budget = 300000;
    unsigned m_seq_block_compression = 0;
    // Run mem_leaf_split's refutation-only ask once at the search root
    // before the DFS proper starts, mirroring c3's smt.nseq.monadic_leaf_root
    // and nielsen_graph::monadic_leaf_root_refute.
    bool m_seq_monadic_leaf_root = true;
    unsigned m_seq_monadic_leaf_budget_root = 50000;
    // While equations/disequations are still pending, retry the root-only
    // ask every `m_seq_monadic_leaf_root_period` split() visits instead of
    // exactly once: a single long DFS (no outer-SMT restart) can run
    // thousands of nodes before equations settle, and the memberships fed
    // to the monadic engine change as substitutions and bound-derived
    // regexes accumulate. 0 disables the retry (ask only once, the prior
    // behavior).
    unsigned m_seq_monadic_leaf_root_period = 64;
    // Gate for mem_facet's incremental single-variable regex-intersection
    // feasibility check (view_witness/vw().check() in mem_propagation),
    // mirroring c3's smt.nseq.regex_precheck.
    bool m_seq_regex_precheck = true;
    // Opt-in gate for using seq::monadic as the end-game witness solver in
    // mem_propagation::propagate(), with ambient length bounds asserted as
    // hypotheses. Falls back to view_witness when unsupported or out of
    // budget; default off pending validation on regex/mem benchmarks.
    bool m_seq_mem_monadic_endgame = false;

    theory_seq_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }

    void updt_params(params_ref const & p);
};
