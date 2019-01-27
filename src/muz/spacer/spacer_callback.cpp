/**++
Copyright (c) 2017 Microsoft Corporation and Matteo Marescotti

Module Name:

    spacer_callback.cpp

Abstract:

    SPACER plugin for handling events

Author:

    Matteo Marescotti

Notes:

--*/

#include "spacer_callback.h"
#include "muz/spacer/spacer_context.h"


namespace spacer {

    void user_callback::new_lemma_eh(expr *lemma, unsigned level) {
        m_new_lemma_eh(m_state, lemma, level);
    }

    void user_callback::predecessor_eh() {
        m_predecessor_eh(m_state);
    }

    void user_callback::unfold_eh() {
        m_unfold_eh(m_state);
    }

}