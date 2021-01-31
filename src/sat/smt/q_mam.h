/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    euf_mam.h

Abstract:

    Matching Abstract Machine

Author:

    Leonardo de Moura (leonardo) 2007-02-13.
    Nikolaj Bjorner (nbjorner) 2021-01-22.

--*/
#pragma once

#include "ast/ast.h"
#include "ast/euf/euf_egraph.h"
#include <functional>

namespace euf {
    class solver;
};

namespace q {

    typedef euf::enode enode;
    typedef euf::egraph egraph;
    typedef euf::enode_vector enode_vector;

    class ematch;

    /**
       \brief Matching Abstract Machine (MAM)
    */
    class mam {
        friend class mam_impl;

        mam() {}

    public:

        static mam * mk(euf::solver& ctx, ematch& em);
        
        virtual ~mam() {}
        
        virtual void add_pattern(quantifier * q, app * mp) = 0;

        virtual void add_node(enode * n, bool lazy) = 0;

        virtual void propagate() = 0;

        virtual bool can_propagate() const = 0;
        
        virtual void rematch(bool use_irrelevant = false) = 0;
        
        virtual void on_merge(enode * root, enode * other) = 0;

        virtual void on_match(quantifier * qa, app * pat, unsigned num_bindings, enode * const * bindings, unsigned max_generation) = 0;

        virtual void reset() = 0;

        virtual std::ostream& display(std::ostream& out) = 0;
                
        virtual bool check_missing_instances() = 0;

        static void ground_subterms(expr* e, ptr_vector<app>& ground);

    };
};

