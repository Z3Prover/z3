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
    bool m_AssertStrongerArrangements;

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

    theory_str_params(params_ref const & p = params_ref()):
        m_AssertStrongerArrangements(true),
        m_AggressiveLengthTesting(false),
        m_AggressiveValueTesting(false)
    {
        updt_params(p);
    }

    void updt_params(params_ref const & p);
};

#endif /* THEORY_STR_PARAMS_H */
