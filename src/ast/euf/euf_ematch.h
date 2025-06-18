/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_ematch.h

Abstract:

    basic E-matching algorithm with SO support.
    
Author:

    Nikolaj Bjorner (nbjorner) 2025-6-16

--*/

#pragma once

#include "ast/euf/euf_egraph.h"

namespace euf {

    class ematch {
    protected:
        egraph& g;
        std::ostream& display(std::ostream& out) const { return out; }
        std::function<void(void)> m_on_match;
    public:
        ematch(egraph& g):
            g(g)
        {}

        void operator()(expr* pat, enode* t, enode** binding);      
            
    };
}
