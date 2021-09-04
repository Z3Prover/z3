/*++
Module Name:

    theory_str_params.h

Abstract:

    Parameters for string theory plugin

Author:

    Murphy Berzish (mtrberzi) 2016-12-13

Revision History:

--*/

#pragma once

#include "util/params.h"

struct theory_str_params {
    /*
     * If AssertStrongerArrangements is set to true,
     * the implications that would normally be asserted during arrangement generation
     * will instead be asserted as equivalences.
     * This is a stronger version of the standard axiom.
     * The Z3str2 axioms can be simulated by setting this to false.
     */
    bool m_StrongArrangements = true;

    /*
     * If AggressiveLengthTesting is true, we manipulate the phase of length tester equalities
     * to prioritize trying concrete length options over choosing the "more" option.
     */
    bool m_AggressiveLengthTesting = false;

    /*
     * Similarly, if AggressiveValueTesting is true, we manipulate the phase of value tester equalities
     * to prioritize trying concrete value options over choosing the "more" option.
     */
    bool m_AggressiveValueTesting = false;

    /*
     * If AggressiveUnrollTesting is true, we manipulate the phase of regex unroll tester equalities
     * to prioritize trying concrete unroll counts over choosing the "more" option.
     */
    bool m_AggressiveUnrollTesting = true;

    /*
     * If UseFastLengthTesterCache is set to true,
     * length tester terms will not be generated from scratch each time they are needed,
     * but will be saved in a map and looked up.
     */
    bool m_UseFastLengthTesterCache = false;

    /*
     * If UseFastValueTesterCache is set to true,
     * value tester terms will not be generated from scratch each time they are needed,
     * but will be saved in a map and looked up.
     */
    bool m_UseFastValueTesterCache = true;

    /*
     * If StringConstantCache is set to true,
     * all string constants in theory_str generated from anywhere will be cached and saved.
     */
    bool m_StringConstantCache = true;

    double m_OverlapTheoryAwarePriority = -0.1;

    /*
     * RegexAutomata_DifficultyThreshold is the lowest difficulty above which Z3str3
     * will not eagerly construct an automaton for a regular expression term.
     */
    unsigned m_RegexAutomata_DifficultyThreshold = 1000;

    /*
     * RegexAutomata_IntersectionDifficultyThreshold is the lowest difficulty above which Z3str3
     * will not eagerly intersect automata to check unsatisfiability.
     */
    unsigned m_RegexAutomata_IntersectionDifficultyThreshold = 1000;

    /*
     * RegexAutomata_FailedAutomatonThreshold is the number of failed attempts to build an automaton
     * after which a full automaton (i.e. with no length information) will be built regardless of difficulty.
     */
    unsigned m_RegexAutomata_FailedAutomatonThreshold = 10;

    /*
     * RegexAutomaton_FailedIntersectionThreshold is the number of failed attempts to perform automaton
     * intersection after which intersection will always be performed regardless of difficulty.
     */
    unsigned m_RegexAutomata_FailedIntersectionThreshold = 10;

    /*
     * RegexAutomaton_LengthAttemptThreshold is the number of attempts to satisfy length/path constraints
     * before which we begin checking unsatisfiability of a regex term.
     */
    unsigned m_RegexAutomata_LengthAttemptThreshold = 10;
    /*
     * If FixedLengthRefinement is true and the fixed-length equation solver is enabled,
     * Z3str3 will use abstraction refinement to handle formulas that would result in disjunctions or expensive
     * reductions to fixed-length formulas.
     */
    bool m_FixedLengthRefinement = false;

    /*
     * If FixedLengthNaiveCounterexamples is true and the fixed-length equation solver is enabled,
     * Z3str3 will only construct simple counterexamples to block unsatisfiable length assignments
     * instead of attempting to learn more complex lessons.
     */
    bool m_FixedLengthNaiveCounterexamples = true;

    theory_str_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }

    void updt_params(params_ref const & p);
    void display(std::ostream & out) const;
};

