/**++
Copyright (c) 2017 Microsoft Corporation and Matteo Marescotti

Module Name:

    spacer_callback.h

Abstract:

    SPACER plugin for handling events

Author:

    Matteo Marescotti

Notes:

--*/

#pragma once

#include "muz/spacer/spacer_context.h"
#include "muz/base/dl_engine_base.h"


namespace spacer {

    class user_callback : public spacer_callback {
    private:
        void *m_state;
        const datalog::t_new_lemma_eh m_new_lemma_eh;
        const datalog::t_predecessor_eh m_predecessor_eh;
        const datalog::t_unfold_eh m_unfold_eh;

    public:
        user_callback(context &context,
                      void *state,
                      const datalog::t_new_lemma_eh new_lemma_eh,
                      const datalog::t_predecessor_eh predecessor_eh,
                      const datalog::t_unfold_eh unfold_eh) :
                spacer_callback(context),
                m_state(state),
                m_new_lemma_eh(new_lemma_eh),
                m_predecessor_eh(predecessor_eh),
                m_unfold_eh(unfold_eh) {}

        inline bool new_lemma() override { return m_new_lemma_eh != nullptr; }

        void new_lemma_eh(expr *lemma, unsigned level) override;

        inline bool predecessor() override { return m_predecessor_eh != nullptr; }

        void predecessor_eh() override;

        inline bool unfold() override { return m_unfold_eh != nullptr; }

        void unfold_eh() override;

    };

}


