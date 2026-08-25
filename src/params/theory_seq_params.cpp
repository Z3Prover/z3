/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    theory_seq_params.cpp

Abstract:

    Parameters for sequence theory plugin

Revision History:


--*/

#include "params/theory_seq_params.h"
#include "params/smt_params_helper.hpp"

static void validate_regex_transition_mode(symbol const& s) {
    if (s == "light-ant" || s == "brz")
        return;
    throw default_exception("Invalid seq regex transition mode. Legal values are light-ant, brz");
}

static void validate_regex_orientation(symbol const& s) {
    if (s == "forward" || s == "reversed" || s == "retry")
        return;
    throw default_exception("Invalid seq regex orientation. Legal values are forward, reversed, retry");
}

void theory_seq_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_split_w_len = p.seq_split_w_len();
    m_seq_validate = p.seq_validate();
    m_seq_regex_monadic = p.seq_regex_monadic();
    m_seq_regex_budget = p.seq_regex_budget();
    m_seq_regex_split = p.seq_regex_split();
    m_seq_regex_transition_mode = p.seq_regex_transition_mode();
    validate_regex_transition_mode(m_seq_regex_transition_mode);
    m_seq_regex_orientation = p.seq_regex_orientation();
    validate_regex_orientation(m_seq_regex_orientation);
    m_seq_max_unfolding = p.seq_max_unfolding();
    m_seq_min_unfolding = p.seq_min_unfolding();
}
