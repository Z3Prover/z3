/*++
Module Name:

    theory_str_params.h

Abstract:

    Parameters for string theory plugin

Author:

    Murphy Berzish (mtrberzi) 2016-12-13

Revision History:

--*/

#ifndef THEORY_STR_PARAMS_H
#define THEORY_STR_PARAMS_H

#include"params.h"

struct theory_str_params {
    /*
     * If AssertStrongerArrangements is set to true,
     * the implications that would normally be asserted during arrangement generation
     * will instead be asserted as equivalences.
     * This is a stronger version of the standard axiom.
     * The Z3str2 axioms can be simulated by setting this to false.
     */
    bool m_StrongArrangements;

    /*
     * If AggressiveLengthTesting is true, we manipulate the phase of length tester equalities
     * to prioritize trying concrete length options over choosing the "more" option.
     */
    bool m_AggressiveLengthTesting;

    /*
     * Similarly, if AggressiveValueTesting is true, we manipulate the phase of value tester equalities
     * to prioritize trying concrete value options over choosing the "more" option.
     */
    bool m_AggressiveValueTesting;

    /*
     * If AggressiveUnrollTesting is true, we manipulate the phase of regex unroll tester equalities
     * to prioritize trying concrete unroll counts over choosing the "more" option.
     */
    bool m_AggressiveUnrollTesting;

    /*
     * If UseFastLengthTesterCache is set to true,
     * length tester terms will not be generated from scratch each time they are needed,
     * but will be saved in a map and looked up.
     */
    bool m_UseFastLengthTesterCache;

    /*
     * If UseFastValueTesterCache is set to true,
     * value tester terms will not be generated from scratch each time they are needed,
     * but will be saved in a map and looked up.
     */
    bool m_UseFastValueTesterCache;

    /*
     * If StringConstantCache is set to true,
     * all string constants in theory_str generated from anywhere will be cached and saved.
     */
    bool m_StringConstantCache;

    /*
     * If FiniteOverlapModels is set to true,
     * arrangements that result in overlapping variables will generate a small number of models
     * to test instead of completely giving up on the case.
     */
    bool m_FiniteOverlapModels;

    bool m_UseBinarySearch;
    unsigned m_BinarySearchInitialUpperBound;

    double m_OverlapTheoryAwarePriority;

    theory_str_params(params_ref const & p = params_ref()):
        m_StrongArrangements(true),
        m_AggressiveLengthTesting(false),
        m_AggressiveValueTesting(false),
        m_AggressiveUnrollTesting(true),
        m_UseFastLengthTesterCache(false),
        m_UseFastValueTesterCache(true),
        m_StringConstantCache(true),
        m_FiniteOverlapModels(false),
        m_UseBinarySearch(false),
        m_BinarySearchInitialUpperBound(64),
        m_OverlapTheoryAwarePriority(-0.1)
    {
        updt_params(p);
    }

    void updt_params(params_ref const & p);
};

#endif /* THEORY_STR_PARAMS_H */
