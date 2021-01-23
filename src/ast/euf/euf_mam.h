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

    /**
       \brief Matching Abstract Machine (MAM)
    */
    class mam {
        friend class mam_impl;

        mam() {}

    public:

        static mam * mk(egraph & ctx, 
                        std::function<void(quantifier*, app*, unsigned, enode* const*, unsigned)>& add_instance);
        
        virtual ~mam() {}
        
        virtual void add_pattern(quantifier * q, app * mp) = 0;

        virtual void push_scope() = 0;

        virtual void pop_scope(unsigned num_scopes) = 0;

        virtual void match() = 0;
        
        virtual void rematch(bool use_irrelevant = false) = 0;

        virtual bool has_work() const = 0;
        
        virtual void add_eq_eh(enode * r1, enode * r2) = 0;

        virtual void reset() = 0;

        virtual std::ostream& display(std::ostream& out) = 0;
        
        virtual void on_match(quantifier * q, app * pat, unsigned num_bindings, enode * const * bindings, unsigned max_generation) = 0;
        
        virtual bool is_shared(enode * n) const = 0;

        virtual bool check_missing_instances() = 0;
    };
};

