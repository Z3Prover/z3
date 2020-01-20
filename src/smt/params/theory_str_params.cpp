/*++
Module Name:

    theory_str_params.cpp

Abstract:

    Parameters for string theory plugin

Author:

    Murphy Berzish (mtrberzi) 2016-12-13

Revision History:

--*/

#include "smt/params/theory_str_params.h"
#include "smt/params/smt_params_helper.hpp"

void theory_str_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_StrongArrangements = p.str_strong_arrangements();
    m_AggressiveLengthTesting = p.str_aggressive_length_testing();
    m_AggressiveValueTesting = p.str_aggressive_value_testing();
    m_AggressiveUnrollTesting = p.str_aggressive_unroll_testing();
    m_UseFastLengthTesterCache = p.str_fast_length_tester_cache();
    m_UseFastValueTesterCache = p.str_fast_value_tester_cache();
    m_StringConstantCache = p.str_string_constant_cache();
    m_FiniteOverlapModels = p.str_finite_overlap_models();
    m_UseBinarySearch = p.str_use_binary_search();
    m_BinarySearchInitialUpperBound = p.str_binary_search_start();
    m_OverlapTheoryAwarePriority = p.str_overlap_priority();
    m_RegexAutomata = p.str_regex_automata();
    m_RegexAutomata_DifficultyThreshold = p.str_regex_automata_difficulty_threshold();
    m_RegexAutomata_IntersectionDifficultyThreshold = p.str_regex_automata_intersection_difficulty_threshold();
    m_RegexAutomata_FailedAutomatonThreshold = p.str_regex_automata_failed_automaton_threshold();
    m_RegexAutomata_FailedIntersectionThreshold = p.str_regex_automata_failed_intersection_threshold();
    m_RegexAutomata_LengthAttemptThreshold = p.str_regex_automata_length_attempt_threshold();
    m_FixedLengthModels = p.str_fixed_length_models();
    m_FixedLengthRefinement = p.str_fixed_length_refinement();
    m_FixedLengthNaiveCounterexamples = p.str_fixed_length_naive_cex();
}

#define DISPLAY_PARAM(X) out << #X"=" << X << std::endl;

void theory_str_params::display(std::ostream & out) const {
    DISPLAY_PARAM(m_StrongArrangements);
    DISPLAY_PARAM(m_AggressiveLengthTesting);
    DISPLAY_PARAM(m_AggressiveValueTesting);
    DISPLAY_PARAM(m_AggressiveUnrollTesting);
    DISPLAY_PARAM(m_UseFastLengthTesterCache);
    DISPLAY_PARAM(m_UseFastValueTesterCache);
    DISPLAY_PARAM(m_StringConstantCache);
    DISPLAY_PARAM(m_UseBinarySearch);
    DISPLAY_PARAM(m_BinarySearchInitialUpperBound);
    DISPLAY_PARAM(m_OverlapTheoryAwarePriority);
    DISPLAY_PARAM(m_RegexAutomata);
    DISPLAY_PARAM(m_RegexAutomata_DifficultyThreshold);
    DISPLAY_PARAM(m_RegexAutomata_IntersectionDifficultyThreshold);
    DISPLAY_PARAM(m_RegexAutomata_FailedAutomatonThreshold);
    DISPLAY_PARAM(m_RegexAutomata_FailedIntersectionThreshold);
    DISPLAY_PARAM(m_RegexAutomata_LengthAttemptThreshold);
    DISPLAY_PARAM(m_FixedLengthModels);
    DISPLAY_PARAM(m_FixedLengthNaiveCounterexamples);
}
